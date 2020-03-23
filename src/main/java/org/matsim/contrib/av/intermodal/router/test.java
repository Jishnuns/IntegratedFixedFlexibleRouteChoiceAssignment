/* *********************************************************************** *
 * project: org.matsim.*
 * TranitRouter.java
 *                                                                         *
 * *********************************************************************** *
 *                                                                         *
 * copyright       : (C) 2009 by the members listed in the COPYING,        *
 *                   LICENSE and WARRANTY file.                            *
 * email           : info at matsim dot org                                *
 *                                                                         *
 * *********************************************************************** *
 *                                                                         *
 *   This program is free software; you can redistribute it and/or modify  *
 *   it under the terms of the GNU General Public License as published by  *
 *   the Free Software Foundation; either version 2 of the License, or     *
 *   (at your option) any later version.                                   *
 *   See also COPYING, LICENSE and WARRANTY file                           *
 *                                                                         *
 * *********************************************************************** */

package org.matsim.contrib.av.intermodal.router;

import java.io.BufferedReader;
import java.io.FileReader;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Iterator;
import java.util.Random;
import org.matsim.analysis.*;
import org.matsim.core.controler.*;

import java.util.*;
import org.matsim.api.core.v01.Coord;
import org.matsim.api.core.v01.TransportMode;
import org.matsim.api.core.v01.network.Link;
import org.matsim.api.core.v01.network.Network;
import org.matsim.api.core.v01.network.Node;
import org.matsim.api.core.v01.population.Leg;
import org.matsim.api.core.v01.population.Person;
import org.matsim.api.core.v01.population.Route;
import org.matsim.core.config.groups.PlanCalcScoreConfigGroup;
import org.matsim.core.network.NetworkUtils;
import org.matsim.core.population.PopulationUtils;
import org.matsim.core.population.routes.RouteUtils;
import org.matsim.core.router.InitialNode;
import org.matsim.core.router.util.LeastCostPathCalculator.Path;
import org.matsim.core.router.util.TravelTime;
import org.matsim.core.utils.geometry.CoordUtils;
import org.matsim.core.utils.misc.Time;
import org.matsim.facilities.Facility;
import org.matsim.pt.router.*;
import org.matsim.pt.router.TransitRouterNetwork.TransitRouterNetworkLink;
import org.matsim.pt.router.TransitRouterNetwork.TransitRouterNetworkNode;
import org.matsim.pt.routes.ExperimentalTransitRoute;
import org.matsim.pt.transitSchedule.api.TransitLine;
import org.matsim.pt.transitSchedule.api.TransitRoute;
import org.matsim.pt.transitSchedule.api.TransitRouteStop;
import org.matsim.pt.transitSchedule.api.TransitStopFacility;

/**
 * Not thread-safe because MultiNodeDijkstra is not. Does not expect the TransitSchedule to change once constructed! michaz '13
 *
 * @author jbischoff
 */
public class test implements TransitRouter {

	private final TransitRouterNetwork transitNetwork;
	private final Network network;
	private final PlanCalcScoreConfigGroup pcsConfig;
	private final TransitRouterConfig trConfig;
	private final TransitTravelDisutility travelDisutility;
	private final TravelTime travelTime;
	private final VariableAccessEgressTravelDisutility variableAccessEgressTravelDisutility;
	public final List<Double> routelength= new LinkedList<>();
	public final List<Integer> sample = new LinkedList<>();
	public final List<Path> pathsizepath = new LinkedList<>();
	
	private final PreparedTransitSchedule preparedTransitSchedule;


	public test(
			final PlanCalcScoreConfigGroup planCalcScoreConfig,
			final TransitRouterConfig transitRouterConfig,
			final PreparedTransitSchedule preparedTransitSchedule,
			final TransitRouterNetwork routerNetwork,
			final TravelTime travelTime,
			final TransitTravelDisutility travelDisutility, final VariableAccessEgressTravelDisutility variableAccessEgressTravelDisutility,
			final Network network) {
		this.pcsConfig = planCalcScoreConfig;
		this.trConfig = transitRouterConfig;
		this.transitNetwork = routerNetwork;
		this.travelTime = travelTime;
		this.travelDisutility = travelDisutility;
		this.preparedTransitSchedule = preparedTransitSchedule;
		this.variableAccessEgressTravelDisutility = variableAccessEgressTravelDisutility;
		this.network = network;
	}

	//The function which returns all the nearest stops from a point
	
	private Map<Node, InitialNode> locateWrappedNearestTransitNodes(Person person, Coord coord, double departureTime) {
		Collection<TransitRouterNetworkNode> nearestNodes = this.transitNetwork.getNearestNodes(coord, this.trConfig.getSearchRadius());
		if (nearestNodes.size() < 2) {
			// also enlarge search area if only one stop found, maybe a second one is near the border of the search area
			TransitRouterNetworkNode nearestNode = this.transitNetwork.getNearestNode(coord);
			double distance = CoordUtils.calcEuclideanDistance(coord, nearestNode.stop.getStopFacility().getCoord());
			nearestNodes = this.transitNetwork.getNearestNodes(coord, distance + this.trConfig.getExtensionRadius());
		}
		Map<Node, InitialNode> wrappedNearestNodes = new LinkedHashMap<>();
		for (TransitRouterNetworkNode node : nearestNodes) {
			Coord toCoord = node.stop.getStopFacility().getCoord();
			Leg initialLeg = getAccessEgressLeg(person, coord, toCoord, departureTime);
			double initialTime = initialLeg.getTravelTime();
			double marginalUtilityOfDistance_utl_m = 
					pcsConfig.getModes().get(initialLeg.getMode()).getMonetaryDistanceRate() * pcsConfig.getMarginalUtilityOfMoney() +
					pcsConfig.getModes().get(initialLeg.getMode()).getMarginalUtilityOfDistance();
			double marginalUtilityOfTravelTime_utl_s = 
					pcsConfig.getModes().get(initialLeg.getMode()).getMarginalUtilityOfTraveling()/3600.0 -
					pcsConfig.getPerforming_utils_hr()/3600.;
			//  getMarginalUtilityOfTravelTimeWalk includes the opportunity cost of time.
			double timeCost = - initialLeg.getTravelTime() * marginalUtilityOfTravelTime_utl_s ;
			// (sign: margUtl is negative; overall it should be positive because it is a cost.)
			double distanceCost = - initialLeg.getRoute().getDistance() * marginalUtilityOfDistance_utl_m ;
			// (sign: same as above)
			double initialCost = timeCost + distanceCost;
			wrappedNearestNodes.put(node, new InitialNode(initialCost, initialTime + departureTime));
		}
		return wrappedNearestNodes;
	}

	private Leg getAccessEgressLeg(Person person, Coord coord, Coord toCoord, double time) {
		return variableAccessEgressTravelDisutility.getAccessEgressModeAndTraveltime(person, coord, toCoord, time);
	}


	private double getTransferTime(Person person, Coord coord, Coord toCoord) { 
		return travelDisutility.getWalkTravelTime(person, coord, toCoord) + this.trConfig.getAdditionalTransferTime();
	}

	private double getAccessEgressDisutility(Person person, Coord coord, Coord toCoord) {
		return travelDisutility.getWalkTravelDisutility(person, coord, toCoord);
	}
	//Jishnu
	//Function which calculates the path size factor
	// Should receive a list of all paths (transit routes) between all possible transit route network stop pairs
	private double pathsizecalculator(Path p, int k)
	{
		if(p!= null)
		{
			double PS=0.0, SAP=0.0,gamma=10.0;
			//System.out.println("One");
			for (Link lll : p.links)
			{
				TransitRouterNetworkLink link1 = (TransitRouterNetworkLink) lll;
				//System.out.println("The size of the path list is: "+ pathsizepath.size());
				for(int i : sample )
				{
					//System.out.println("The value of i is: " + i);
					if(i!=k)
					{
						if(pathsizepath.get(i)!=null)
						{
							for (Link llll : pathsizepath.get(i).links)
							{
								TransitRouterNetworkLink link2 = (TransitRouterNetworkLink) llll;
                                if(link2.getId()==link1.getId())
                                {
                                	SAP= SAP + (Math.pow((routelength.get(k)/routelength.get(i)),gamma));
                                    break;
                                }
                            }
						}
                    }
				}
		   	    PS = PS + ((link1.getLength()/(routelength.get(k))*SAP));
		   }
		   return PS;
		}
		else
			return 0;
	}
	//calculates the utility of each path
	private double utilitycalculator(Node a, InitialNode b, Node c, InitialNode d, final Facility<?> fromFacility, final Facility<?> toFacility)
	{
		
		//reading from file
		int numtransfer=0,iteration=100;
		double utility = 0;
		double bwalk=-2.046, btransfer=-0.443,bmoney=1, bwait =1, binveh = 1,waittime=0;
		double firstdist = CoordUtils.calcEuclideanDistance(fromFacility.getCoord(),a.getCoord());
		double seconddist= CoordUtils.calcEuclideanDistance(a.getCoord(),c.getCoord());
		double lastdist = CoordUtils.calcEuclideanDistance(toFacility.getCoord(),c.getCoord());
		String[] words = new String[15];
		String first="./Results for Sioux/output/intermodalExample/ITERS/it."; 
		String FILENAME = " ";
		BufferedReader bw = null;
		FileReader fw = null;
		while(iteration>=0)
		{
			
			FILENAME = first+ Integer.toString(iteration)+"/"+Integer.toString(iteration)+".taxi_stats.txt"; 	
			File file = new File(FILENAME);
			if (file.exists()) {
				try {
		            fw = new FileReader(file.getAbsoluteFile());
					bw = new BufferedReader(fw);
					String line;
					int r=0;
					while ((line = bw.readLine()) != null) {
						    if(r==26){
								words = line.split("	");
								words[2] = words[2].replaceAll(",", ".");
								waittime = Double.parseDouble(words[2]);
						}
					    r++;
					}
					
				} catch (IOException e) {

					e.printStackTrace();

				} finally {

					try {

						if (bw != null)
							bw.close();

						if (fw != null)
							fw.close();

					} catch (IOException ex) {

						ex.printStackTrace();

					}
				}		
				break; 			
			} 
			iteration--;
		}
		//file write end
		if(firstdist>100){
			firstdist = firstdist * 1.3;
		    utility = utility + (-2*waittime) + (-1*firstdist*1.3/13.88) + (-411.4*firstdist*1.3*0.00048); 
		    numtransfer++;
		}
		else{
			firstdist = firstdist * 1.3;
		    utility = utility + (-2*firstdist/0.833); 
		}
		if(lastdist>100){
			lastdist = lastdist * 1.3;
		    utility = utility + (-2*waittime) + (-1*lastdist*1.3/13.88) + (-411.4*lastdist*1.3*0.00159); 
	        numtransfer++;	
		}
		else{
			lastdist = lastdist * 1.3;
		    utility = utility + (-2*lastdist/0.833); 
		}
		if(numtransfer==1)
			btransfer = -300;
		else
			btransfer = -300;
		utility = utility + (-2*150) + (-1*seconddist*1.3/7.25) + (-411.4*seconddist*1.3*0.000265) + (btransfer*numtransfer);
		return Math.exp(utility);
	}
	
	//Jishnu
	@Override
	public List<Leg> calcRoute(final Facility<?> fromFacility, final Facility<?> toFacility, final double departureTime, final Person person) {
		
		// find possible start stops
		Map<Node, InitialNode> wrappedFromNodes = this.locateWrappedNearestTransitNodes(person, fromFacility.getCoord(), departureTime);
		//int sizeinitial = wrappedFromNodes.size();
		// find possible end stops
		Map<Node, InitialNode> wrappedToNodes = this.locateWrappedNearestTransitNodes(person, toFacility.getCoord(), departureTime);
		//int sizefinal = wrappedToNodes.size();
		
		double prosum=0, routelengthi = 0.0;
		
		List<Double> pathsizefactor=new LinkedList<>();//creating linkedlist for path size computation
		List<Double> utility=new LinkedList<>();//creating linkedlist for utility
		List<Double> probability=new LinkedList<>();//creating linkedlist for probability
		
		int k;
		
		//calculates utility and selects the stop pair according to a path size size logit model
		
		//adds the least cost path tree for all the origin destination transit stop pairs
		//System.out.println("One");  
		    Map<Node, InitialNode> wrappedFromNodesFinal = new LinkedHashMap<>();
			Map<Node, InitialNode> wrappedToNodesFinal = new LinkedHashMap<>();
			k=0;
			int iterator= 0;
			for (Map.Entry<Node, InitialNode> entryfrom : wrappedFromNodes.entrySet()) {
				for (Map.Entry<Node, InitialNode> entryto : wrappedToNodes.entrySet()) {
				       	    routelengthi = 0.0;
					        wrappedFromNodesFinal.put(entryfrom.getKey(), entryfrom.getValue());
						    wrappedToNodesFinal.put(entryto.getKey(), entryto.getValue());
						    TransitLeastCostPathTree treeforpathsize = new TransitLeastCostPathTree(transitNetwork, travelDisutility, travelTime,
									wrappedFromNodesFinal, wrappedToNodesFinal, person);
						    Path pathforps = treeforpathsize.getPath(wrappedToNodesFinal);
						    //pathsizepath.add(pathforps);
						    pathsizepath.add(pathforps);
						    //System.out.println("C");  
						    if(pathforps!=null)
						    {
						    	for (Link ll : pathforps.links) 
						    	{
						    		TransitRouterNetworkLink link = (TransitRouterNetworkLink) ll;
						    		routelengthi= routelengthi + link.getLength();		
						    	}
						    	routelength.add(routelengthi);
						    }
						    
						    else
						    	routelength.add(0.0);
						    //System.out.println("D");  
						    wrappedFromNodesFinal.clear();
						    wrappedToNodesFinal.clear();   
						    treeforpathsize = null; //check again
				            iterator ++; 
				}
			}
			//call the path size factor computation function here
			//System.out.println("Two"); 
			
			for (k = 0; k < pathsizepath.size(); k++) 
		    	sample.add(k);
				//pathsizefactor.add(this.pathsizecalculator(pathsizepath.get(k),k));
		    for(int q:sample)
		       	pathsizefactor.add(this.pathsizecalculator(pathsizepath.get(q),q));
		   pathsizepath.clear();
			k=0;
			//System.out.println("Three"); 
			for (Map.Entry<Node, InitialNode> entryfrom : wrappedFromNodes.entrySet()) {
				for (Map.Entry<Node, InitialNode> entryto : wrappedToNodes.entrySet()) {
				       utility.add(this.utilitycalculator(entryfrom.getKey(), entryfrom.getValue(), entryto.getKey(), entryto.getValue(), fromFacility, toFacility)*pathsizefactor.get(k));
				       prosum = prosum + (utility.get(k)*pathsizefactor.get(k));
				       k++;
				}
			}
			//System.out.println("Four"); 
			   for (int qq : sample) {
			    	if(qq==0)
			    	probability.add(utility.get(qq)/prosum);
			    	else
			    		probability.add(probability.get(qq-1)+(utility.get(qq)/prosum));
			      }
			Random rand = new Random();
			int index=0;
			double r= rand.nextDouble();
			while(r>probability.get(index))	
			 index++;
			for (int qqq:sample ) {
		    	if(qqq==index)
		    	probability.add(utility.get(qqq)/prosum);
		    	
		      }
			sample.clear(); 
			//System.out.println("Five"); 
			k=0;
			for (Map.Entry<Node, InitialNode> entryfrom : wrappedFromNodes.entrySet()) {
				for (Map.Entry<Node, InitialNode> entryto : wrappedToNodes.entrySet()) {
				       if (k == index) {
						    wrappedFromNodesFinal.put(entryfrom.getKey(), entryfrom.getValue());
						    wrappedToNodesFinal.put(entryto.getKey(), entryto.getValue());
						    
				       }
				       k++;
				}
			}
			//System.out.println("Six"); 
		    TransitLeastCostPathTree tree = new TransitLeastCostPathTree(transitNetwork, travelDisutility, travelTime,
				wrappedFromNodesFinal, wrappedToNodesFinal, person);
		// find routes between start and end stop
		Path p = tree.getPath(wrappedToNodes);
		if (p == null) {
			return null;
		}

		double directWalkCost = getAccessEgressDisutility(person, fromFacility.getCoord(), toFacility.getCoord());
		double pathCost = p.travelCost + wrappedFromNodes.get(p.nodes.get(0)).initialCost + wrappedToNodes.get(p.nodes.get(p.nodes.size() - 1)).initialCost;

		if (directWalkCost * trConfig.getDirectWalkFactor() < pathCost) {
			return this.createDirectAccessEgressModeLegList(null, fromFacility.getCoord(), toFacility.getCoord(), departureTime);
		}
		return convertPathToLegList(departureTime, p, fromFacility.getCoord(), toFacility.getCoord(), person);
	}
	private List<Leg> createDirectAccessEgressModeLegList(Person person, Coord fromCoord, Coord toCoord, double time) {
		List<Leg> legs = new ArrayList<>();
		Leg leg = getAccessEgressLeg(person, fromCoord, toCoord, time);
		legs.add(leg);
		return legs;
	}

	protected List<Leg> convertPathToLegList(double departureTime, Path path, Coord fromCoord, Coord toCoord, Person person) {
		// yy would be nice if the following could be documented a bit better.  kai, jul'16
		
		// now convert the path back into a series of legs with correct routes
		double time = departureTime;
		List<Leg> legs = new ArrayList<>();
		Leg leg;
		TransitLine line = null;
		TransitRoute route = null;
		TransitStopFacility accessStop = null;
		TransitRouteStop transitRouteStart = null;
		TransitRouterNetworkLink prevLink = null;
		double currentDistance = 0;
		int transitLegCnt = 0;
		for (Link ll : path.links) {
			TransitRouterNetworkLink link = (TransitRouterNetworkLink) ll;
			if (link.getLine() == null) {
				// (it must be one of the "transfer" links.) finish the pt leg, if there was one before...
				TransitStopFacility egressStop = link.fromNode.stop.getStopFacility();
				if (route != null) {
					leg = PopulationUtils.createLeg(TransportMode.pt);
					ExperimentalTransitRoute ptRoute = new ExperimentalTransitRoute(accessStop, line, route, egressStop);
					double arrivalOffset = (link.getFromNode().stop.getArrivalOffset() != Time.UNDEFINED_TIME) ? link.fromNode.stop.getArrivalOffset() : link.fromNode.stop.getDepartureOffset();
					double arrivalTime = this.preparedTransitSchedule.getNextDepartureTime(route, transitRouteStart, time) + (arrivalOffset - transitRouteStart.getDepartureOffset());
					ptRoute.setTravelTime(arrivalTime - time);

//					ptRoute.setDistance( currentDistance );
					ptRoute.setDistance( link.getLength() );
					// (see MATSIM-556)

					leg.setRoute(ptRoute);
					leg.setTravelTime(arrivalTime - time);
					time = arrivalTime;
					legs.add(leg);
					transitLegCnt++;
					accessStop = egressStop;
				}
				line = null;
				route = null;
				transitRouteStart = null;
				currentDistance = link.getLength();
			} else {
				// (a real pt link)
				currentDistance += link.getLength();
				if (link.getRoute() != route) {
					// the line changed
					TransitStopFacility egressStop = link.fromNode.stop.getStopFacility();
					if (route == null) {
						// previously, the agent was on a transfer, add the walk leg
						transitRouteStart = ((TransitRouterNetworkLink) ll).getFromNode().stop;
						if (accessStop != egressStop) {
							if (accessStop != null) {
								leg = PopulationUtils.createLeg(TransportMode.transit_walk);
								//							    double walkTime = getWalkTime(person, accessStop.getCoord(), egressStop.getCoord());
								double transferTime = getTransferTime(person, accessStop.getCoord(), egressStop.getCoord());
								Route walkRoute = RouteUtils.createGenericRouteImpl(accessStop.getLinkId(),
										egressStop.getLinkId());
								// (yy I would have expected this from egressStop to accessStop. kai, jul'16)
								
								//							    walkRoute.setTravelTime(walkTime);
								walkRoute.setTravelTime(transferTime);
								
//								walkRoute.setDistance( currentDistance );
								walkRoute.setDistance( trConfig.getBeelineDistanceFactor() * 
										NetworkUtils.getEuclideanDistance(accessStop.getCoord(), egressStop.getCoord()) );
								// (see MATSIM-556)

								leg.setRoute(walkRoute);
								//							    leg.setTravelTime(walkTime);
								leg.setTravelTime(transferTime);
								//							    time += walkTime;
								time += transferTime;
								legs.add(leg);
							} else {
								// accessStop == null, so it must be the first access-leg. If mode is e.g. taxi, we need a transit_walk to get to pt link
								leg = getAccessEgressLeg(person, fromCoord, egressStop.getCoord(),time);
								if (variableAccessEgressTravelDisutility.isTeleportedAccessEgressMode(leg.getMode()))
								{
									leg.getRoute().setEndLinkId(egressStop.getLinkId());
									time += leg.getTravelTime();
									legs.add(leg);


								} else {
									legs.add(leg); //access leg
									time += leg.getTravelTime();
									
									Route walkRoute = RouteUtils.createGenericRouteImpl(
											leg.getRoute().getEndLinkId(), egressStop.getLinkId());
									double walkTime = getTransferTime(person, network.getLinks().get(leg.getRoute().getEndLinkId()).getCoord(), egressStop.getCoord());
									walkRoute.setTravelTime(walkTime);
									walkRoute.setDistance(trConfig.getBeelineDistanceFactor() * 
											NetworkUtils.getEuclideanDistance(network.getLinks().get(leg.getRoute().getEndLinkId()).getCoord(), egressStop.getCoord()) );
								
									Leg walkleg = PopulationUtils.createLeg(TransportMode.transit_walk);
									walkleg.setTravelTime(walkTime);
									walkleg.setRoute(walkRoute);
									time += walkTime;
									legs.add(walkleg);
									
								}
								
//								walkRoute.setDistance( currentDistance );
								// (see MATSIM-556)

							}
						}
						currentDistance = 0;
					}
					line = link.getLine();
					route = link.getRoute();
					accessStop = egressStop;
				}
			}
			prevLink = link;
		}
		if (route != null) {
			// the last part of the path was with a transit route, so add the pt-leg and final walk-leg
			leg = PopulationUtils.createLeg(TransportMode.pt);
			TransitStopFacility egressStop = prevLink.toNode.stop.getStopFacility();
			ExperimentalTransitRoute ptRoute = new ExperimentalTransitRoute(accessStop, line, route, egressStop);
//			ptRoute.setDistance( currentDistance );
			ptRoute.setDistance( trConfig.getBeelineDistanceFactor() * NetworkUtils.getEuclideanDistance(accessStop.getCoord(), egressStop.getCoord() ) );
			// (see MATSIM-556)
			leg.setRoute(ptRoute);
			double arrivalOffset = ((prevLink).toNode.stop.getArrivalOffset() != Time.UNDEFINED_TIME) ?
					(prevLink).toNode.stop.getArrivalOffset()
					: (prevLink).toNode.stop.getDepartureOffset();
					double arrivalTime = this.preparedTransitSchedule.getNextDepartureTime(route, transitRouteStart, time) + (arrivalOffset - transitRouteStart.getDepartureOffset());
					leg.setTravelTime(arrivalTime - time);
					ptRoute.setTravelTime( arrivalTime - time );
					legs.add(leg);
					transitLegCnt++;
					accessStop = egressStop;
		}
		if (prevLink != null) {
			if (accessStop == null) {
				// no use of pt
				leg = getAccessEgressLeg(person, fromCoord, toCoord, time);
				legs.add(leg);

			} else {
				Leg eleg = getAccessEgressLeg(person, accessStop.getCoord(), toCoord, time);
				
				if (variableAccessEgressTravelDisutility.isTeleportedAccessEgressMode(eleg.getMode())){
					leg = eleg;
					leg.getRoute().setStartLinkId(accessStop.getLinkId());
					legs.add(leg);

				}
				else {
					leg = PopulationUtils.createLeg(TransportMode.transit_walk);
					double walkTime = getTransferTime(person, accessStop.getCoord(), network.getLinks().get(eleg.getRoute().getStartLinkId()).getCoord());
					leg.setTravelTime(walkTime);
					Route walkRoute = RouteUtils.createGenericRouteImpl(accessStop.getLinkId(), eleg.getRoute().getStartLinkId());
					walkRoute.setDistance(trConfig.getBeelineDistanceFactor() * 
											NetworkUtils.getEuclideanDistance(accessStop.getCoord(),network.getLinks().get(eleg.getRoute().getStartLinkId()).getCoord()));
					leg.setRoute(walkRoute);
					legs.add(leg);
					legs.add(eleg);
				}
			}
		}
		if (transitLegCnt == 0) {
			// it seems, the agent only walked
			legs.clear();
			try{
			leg = getAccessEgressLeg(person, fromCoord, toCoord, time);

			legs.add(leg);
			} catch (NullPointerException e){
				throw new RuntimeException(" npe: person"+ person + fromCoord + toCoord + time);
			}
		}
		return legs;
	}

	public TransitRouterNetwork getTransitRouterNetwork() {
		return this.transitNetwork;
	}

	protected TransitRouterNetwork getTransitNetwork() {
		return transitNetwork;
	}

	protected TransitRouterConfig getConfig() {
		return trConfig;
	}

}
