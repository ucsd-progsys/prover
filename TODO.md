Ok, there are two compose: 
 
 - Axioms: 
   - Haskell Foo.compose :: (a -> b) -> (b -> c) -> a -> c goes to 
   - the logical compose :: Arrow (Arrow (Arrow (Arrow a b) (Arrow b c)) a)  c

- non axioms: 

- argument variables 


Defunctionalization of haskell things
-------------------------------------

Higher order Haskell functions should be de-higher-ordered.  Eg

```
compose :: (a -> b) -> (b -> c) -> a -> c 
```

Can be turned to either 

```
compose :: (Arrow a b) -> (Arrow b c) -> a -> c                (1)
```

or totally de-HO to 


```
compose :: Arrow (Arrow (Arrow (Arrow a b) (Arrow b c)) a)  c  (2)
```

Choosing (2) for consistency and treating `Arrow` as a function in the solver 


Parsing
-------
- comments
- OK, really need to do that!!!! check well formedness of axioms etc
- add reg test

- Separation of blocks now happens with a semi. Edit that
- fix printing !!!
