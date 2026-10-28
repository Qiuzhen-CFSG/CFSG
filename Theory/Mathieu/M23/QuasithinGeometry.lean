module

public import Theory.Mathieu.M23.QuasithinGeometry.Actions
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions
public import Theory.Mathieu.M23.QuasithinGeometry.StandardSystem

/-!
# Concrete M23 geometry for the quasithin recognition argument

The verified design supplies genuine heptad labels and the four-set stabilizer
identification. The heptad stabilizer is the split exceptional binary extension
of A7, with compatible affine and seven-point actions. The pair stabilizer is
PSL(3,4) extended by Frobenius, acting on the coordinatized derived plane.
The local intersections are identified through their actual ambient embeddings.

The concrete pair-graph action and four-set stabilizer form a uniqueness system;
its local graph is a base. M23 has one class of 3795 involutions and no odd-order
subgroup whose order is divisible by 3795. All witnesses and generation
conditions are discharged for the design automorphism model.

Source: Aschbacher--Smith, §5.2, printed pp.655--658; Aschbacher,
*Sporadic Groups*, Chapter 6 and §37.
-/
