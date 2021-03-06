/*	
 * IndexesFunctionElement.java  	
 * 
 * Copyright (C) 2007 Roozbeh Farahbod
 *
 * Licensed under the Academic Free License version 3.0 
 *   http://www.opensource.org/licenses/afl-3.0.php
 *   http://www.coreasm.org/afl-3.0.php
 *
 * This file contains source code contributed by the European FP7 research project BIOMICS (Grant no. 318202)
 * Copyright (C) 2016 Daniel Schreckling, Eric Rothstein (BIOMICS) 
 *
 * Licensed under the Academic Free License version 3.0 
 *   http://www.opensource.org/licenses/afl-3.0.php
 *
 */	
 
package org.coreasim.engine.plugins.list;

import java.util.List;

import org.coreasim.engine.ControlAPI;
import org.coreasim.engine.CoreASIMError;
import org.coreasim.engine.absstorage.AbstractStorage;
import org.coreasim.engine.absstorage.Element;
import org.coreasim.engine.absstorage.FunctionElement;
import org.coreasim.engine.absstorage.Signature;
import org.coreasim.engine.plugins.collection.AbstractListElement;

/** 
 * Implementation of the 'indexes(e, list)' function.
 *   
 * @author  Roozbeh Farahbod
 * 
 */
public class IndexesFunctionElement extends FunctionElement {

	/**
	 * 
	 */
	private static final long serialVersionUID = -4680441766343263950L;
	public static final String NAME = "indexes";
	public static final String NAME_ALTERNATIVE = "indices";
	
	protected final ControlAPI capi;
	protected final AbstractStorage storage;
	protected Signature signature;
	
	public IndexesFunctionElement(ControlAPI capi) {
		this.capi = capi;
		this.storage = capi.getStorage();
		setFClass(FunctionClass.fcDerived);
		signature = new Signature(2);
	}
	
	/* (non-Javadoc)
	 * @see org.coreasm.engine.absstorage.FunctionElement#getValue(java.util.List)
	 */
	@Override
	public Element getValue(List<? extends Element> args) {
		if (!checkArguments(args))
			throw new CoreASIMError("Illegal arguments for " + NAME + ".");
		
		AbstractListElement list = (AbstractListElement)args.get(0);
		return new ListElement(list.indexesOf(args.get(1)));
	}

	public Signature getSignature() {
		return signature;
	}
	
	protected boolean checkArguments(List<? extends Element> args) {
		return (args.size() == 2) 
				&& (args.get(0) instanceof AbstractListElement);
	}

}
