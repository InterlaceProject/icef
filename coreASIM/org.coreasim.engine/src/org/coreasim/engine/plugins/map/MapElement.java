/*	
 * MapElement.java 	1.0
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
 
package org.coreasim.engine.plugins.map;

import java.io.ByteArrayOutputStream;
import java.io.Externalizable;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.coreasim.engine.absstorage.Element;
import org.coreasim.engine.absstorage.Enumerable;
import org.coreasim.engine.absstorage.FunctionElement;
import org.coreasim.engine.absstorage.Location;
import org.coreasim.engine.absstorage.Update;
import org.coreasim.engine.absstorage.UpdateMultiset;
import org.coreasim.engine.interpreter.InterpreterException;
import org.coreasim.engine.interpreter.Node;
import org.coreasim.engine.plugins.collection.AbstractListElement;
import org.coreasim.engine.plugins.collection.AbstractMapElement;
import org.coreasim.engine.plugins.collection.ModifiableCollection;
import org.coreasim.engine.plugins.list.ListElement;
import org.coreasim.engine.plugins.number.NumberElement;

import java.util.Set;

/** 
 * Map elements
 *   
 * @author  Roozbeh Farahbod
 * 
 */
public class MapElement extends AbstractMapElement implements ModifiableCollection {

	/**
	 * 
	 */
	private static final long serialVersionUID = 444310923199263581L;
	
	protected final Map<Element, Element> map;
	protected Set<Element> keySet = null;
	protected Set<Element> valueSet = null;
	protected Collection<Element> valueCollection = null;
	protected Set<Element> enumeration = null;
	protected List<Element> enumListCache = null;
	
	public MapElement() {
		this.map = Collections.unmodifiableMap(new HashMap<Element, Element>());
	}
	
	public MapElement(Map<? extends Element, ? extends Element> map) {
		this.map = Collections.unmodifiableMap(new HashMap<Element, Element>(map));
	}
	
	public MapElement(MapElement anotherMap) {
		this(anotherMap.map);
	}
	
	
	@Override
	public String getBackground() {
		return MapBackgroundElement.NAME;
	}

	@Override
	public boolean containsKey(Element key) {
		return map.containsKey(key);
	}

	@Override
	public boolean containsValue(Element value) {
		return map.containsValue(value);
	}

	@Override
	public Element get(Element key) {
		Element result = map.get(key);
		if (result == null) 
			result = defaultValue;
		return result;
	}

	@Override
	public boolean isEmpty() {
		return map.isEmpty();
	}

	@Override
	public Set<Element> keySet() {
		if (keySet == null) {
			keySet = Collections.unmodifiableSet(map.keySet());
		}
		return keySet;
	}

	public int size() {
		return map.size();
	}

	/**
	 * The size of this map in integer.
	 */
	public int intSize() {
		return map.size();
	}
	
	/**
	 * decides whether the given map is a probability distribution or not.
	 * @throws Exception 
	 */
	//TODO BSL it may make sense to add an exception that explains why it is not
	//a probability distribution
	public String isProbabilityDistribution() {
		double number = 0;
		for (Element k : map.keySet())
		{
			Element v = map.get(k);
			if (! (v instanceof NumberElement))
			{
				return "The probability distribution has a non-number value.";
			}
			NumberElement n = (NumberElement) v;
			double theValue  = n.getValue();
			if(theValue < 0)
			{
				return "A probability value should not be negative.";
			}
			number += theValue;
			//FIXME Float comparisons are fun, yay!
			if(number > 1.001)
			{
				return "The sum of probability values should not be greater than 1.";
			}
		}
		//FIXME Float comparisons are fun, yay!
		if(number < 0.999)
		{
			return "The probabilities in the distribution do not add up to 1.";
		}
		return "";
	}

	@Override
	public Collection<Element> values() {
		if (valueCollection == null) {
			valueCollection = Collections.unmodifiableCollection(map.values());
		}
		return valueCollection;
	}

	public boolean contains(Element e) {
		if (enumeration == null) 
			enumerate();
		return enumeration.contains(e);
	}

	public Collection<Element> enumerate() {
		if (enumeration == null) {
			enumeration = new HashSet<Element>();
			for (Entry<Element, Element> entry: map.entrySet()) {
				enumeration.add(new ListElement(entry.getKey(), entry.getValue()));
			}
		} 
		return enumeration;
	}

	@Override
	public String denotation() {
		if (intSize() == 0) 
			return "{ -> }";
		else {
			StringBuffer result = new StringBuffer("{");
			
			for (Element k: map.keySet())
				result.append(k.denotation() + "->" + map.get(k).denotation() + ", ");
			
			return result.substring(0, result.length() - 2).toString() + "}";
		}
	}

	@Override
	public String toString() {
		if (intSize() == 0) 
			return "{ -> }";
		else {
			StringBuffer result = new StringBuffer("{");
			
			for (Element k: map.keySet())
				result.append(k.toString() + "->" + map.get(k) + ", ");
			
			return result.substring(0, result.length() - 2).toString() + "}";
		}
	}

	/**
	 * @return returns the values-set of this map.
	 */
	@Override
	public Set<Element> getRange() {
		if (valueSet == null) {
			valueSet = Collections.unmodifiableSet(new HashSet<Element>(this.values()));
		}
		return valueSet;
	}

	@Override
	public AbstractMapElement getNewInstance(Map<? extends Element, ? extends Element> map) {
		return new MapElement(map);
	}

	/**
	 * Creates a new map element with the given collection of 
	 * key-value pairs in form of {@link AbstractListElement AbstractListElements} 
	 * of size 2.
	 * 
	 * @throws IllegalArgumentException if the collection is not as specified above 
	 */
	@Override
	public AbstractMapElement getNewInstance(Collection<? extends Element> collection) {
		Map<Element, Element> map = new HashMap<Element, Element>();
		for (Element e: collection) {
			if (e instanceof AbstractListElement 
					&& ((AbstractListElement)e).size() == 2) {
				final AbstractListElement pair = (AbstractListElement)e;
				map.put(pair.head(), pair.last());
			} else
				throw new IllegalArgumentException("Cannot create a new map from the given collection.");
		}
		return new MapElement(map);
	}

	@Override
	public Map<Element, Element> getMap() {
		// System.out.println("Copy of map Serialisation Test: "+isSerializable(new MapElement(this)));
		return Collections.unmodifiableMap(map);
	}

	public List<Element> getIndexedView() throws UnsupportedOperationException {
		if (enumListCache == null)
			enumListCache = Collections.unmodifiableList(new ArrayList<Element>(enumerate()));
		return enumListCache;
	}

	public boolean supportsIndexedView() {
		return true;
	}

	/**
	 * Adds the mapping of element <code>e</code> to this map to create 
	 * a new {@link MapElement}. It then creates an update assigning the new {@link MapElement}
	 * to the given location.
	 * 
	 * Expects <code>e</code> to be an instance of {@link AbstractMapElement}.
	 * 
	 * @see ModifiableCollection#computeAddUpdate(Location, Element, Element, Node)
	 */
	@Override
	public UpdateMultiset computeAddUpdate(Location loc, Element e,
			Element agent, Node node) throws InterpreterException {
		if (e instanceof AbstractMapElement) {
			HashMap<Element, Element> tempMap = new HashMap<Element, Element>(this.map);
			tempMap.putAll(((AbstractMapElement)e).getMap());
			MapElement newMap = new MapElement(tempMap);
			Update u = new Update(loc, newMap, Update.UPDATE_ACTION, agent, node.getScannerInfo());
			return new UpdateMultiset(u);
		} else 
			throw new InterpreterException("Cannot add non-map elements to a map."); 
	}

	/**
	 * If<br>
	 * 1) <code>e</code> is an instance of {@link MapElement}, removes the exact 
	 * key-value pairs of <code>e</code> from this map element;<br>
	 * 2) <code>e</code> is an {@link Enumerable}, removes all the keys from this 
	 * map element that are in <code>e</code>;<br>
	 * 3) <code>e</code> is an {@link Element} (none of the above), if it is a key
	 * in this map, removes it from the map.
	 */
	@Override
	public UpdateMultiset computeRemoveUpdate(Location loc, Element e,
			Element agent, Node node) throws InterpreterException {
		HashMap<Element, Element> tempMap = new HashMap<Element, Element>(this.map);
		if (e instanceof MapElement) {
			/*
			 * if the element is a MapElement then remove all the key-value 
			 * pairs in this map element that match those of the given map element.
			 */
			for (Entry<Element, Element> me: ((MapElement)e).map.entrySet()) {
				final Element key = me.getKey();
				if (tempMap.get(key) != null && tempMap.get(key).equals(me.getValue()))
					tempMap.remove(key);
			}
		} else
			if (e instanceof Enumerable) {
				for (Element ei: ((Enumerable)e).enumerate()) {
					tempMap.remove(ei);
				}
			} else
				tempMap.remove(e);
		
		MapElement newMap = new MapElement(tempMap);
		Update u = new Update(loc, newMap, Update.UPDATE_ACTION, agent, node.getScannerInfo());
		//System.out.println("Serialisation Test: "+isSerializable(newMap));
		return new UpdateMultiset(u);
	}
	public static void main(String[] args)
    {
        System.out.println("Is Serializable? "+isSerializable(new MapElement()));
    }

    public static boolean isSerializable(final Object o)
    {
        final boolean retVal;

        if(implementsInterface(o))
        {
            retVal = attemptToSerialize(o);
        }
        else
        {
            retVal = false;
        }

        return (retVal);
    }

    private static boolean implementsInterface(final Object o)
    {
        final boolean retVal;

        retVal = ((o instanceof Serializable) || (o instanceof Externalizable));

        return (retVal);
    }

    private static boolean attemptToSerialize(final Object o)
    {
        final OutputStream sink;
        ObjectOutputStream stream;

        stream = null;

        try
        {
            sink   = new ByteArrayOutputStream();
            stream = new ObjectOutputStream(sink);
            stream.writeObject(o);
            // could also re-serilalize at this point too
        }
        catch(final IOException ex)
        {
        	ex.printStackTrace();
            return (false);
        }
        finally
        {
            if(stream != null)
            {
                try
                {
                    stream.close();
                }
                catch(final IOException ex)
                {
                    // should not be able to happen
                }
            }
        }

        return (true);
    }
}
