/*	
 * ConnectedSetFunctionElement.java 
 * 
 * Copyright (C) 2010 Roozbeh Farahbod
 *
 * Last modified by $Author$ on $Date$.
 *
 * Licensed under the Academic Free License version 3.0
 *   http://www.opensource.org/licenses/afl-3.0.php
 *   http://www.coreasm.org/afl-3.0.php
 *
 */
package org.coreasim.network.plugins.graph;

import java.util.List;
import java.util.Set;

import org.coreasim.engine.CoreASIMError;
import org.coreasim.engine.absstorage.Element;
import org.coreasim.engine.absstorage.ElementBackgroundElement;
import org.coreasim.engine.absstorage.FunctionElement;
import org.coreasim.engine.absstorage.Signature;
import org.coreasim.engine.plugins.set.SetBackgroundElement;
import org.coreasim.engine.plugins.set.SetElement;
import org.jgrapht.Graph;
import org.jgrapht.alg.ConnectivityInspector;

/**
 * Computes the connected set of a vertex in a graph.
 * 
 * @author Roozbeh Farahbod
 *
 */
public class ConnectedSetFunctionElement extends FunctionElement {

	Signature sig = null;
	final ConnectivityInspectorCache inspectorCache;

	public static final String FUNCTION_NAME = "connectedSet";
	
	public ConnectedSetFunctionElement(ConnectivityInspectorCache inspectorCache) {
		this.inspectorCache = inspectorCache;
	}
	
	@Override
	public FunctionClass getFClass() {
		return FunctionClass.fcDerived;
	}

	@Override
	public Signature getSignature() {
		if (sig == null)
			sig = new Signature(GraphBackgroundElement.BACKGROUND_NAME,
				ElementBackgroundElement.ELEMENT_BACKGROUND_NAME,
				SetBackgroundElement.SET_BACKGROUND_NAME);
		return sig;
	}

	@Override
	public Element getValue(List<? extends Element> args) {
		if (!(args.size() == 2 && args.get(0) instanceof GraphElement)) 
			throw new CoreASIMError("Illegal arguments for " + FUNCTION_NAME + ".");
		
		Graph<Element, Element> g = ((GraphElement)args.get(0)).getGraph();
		Element v = args.get(1);
		
		ConnectivityInspector<Element, Element> inspector = inspectorCache.getInspector(g);
				
		if (inspector != null) {
			Set<Element> conSet = inspector.connectedSetOf(v);
			if (conSet != null)
				return new SetElement(conSet);
		}
		
		return Element.UNDEF;
	}

}
