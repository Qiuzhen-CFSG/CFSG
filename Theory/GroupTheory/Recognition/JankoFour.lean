module

public import Theory.GroupTheory.Recognition.JankoFour.LocalHypotheses
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry
public import Theory.GroupTheory.Recognition.JankoFour.Comparison
public import Theory.GroupTheory.Recognition.JankoFour.ModelHypotheses

/-!
# Recognition of groups of type J₄: source interface and gluing

The source hypothesis is `IsTypeJ4`: the intrinsic extraspecial F*(C_G(z))
of order 2¹³, the actual cubic extension quotient, and ambient returning
fusion. `recognize_of_equivalent_bases` supplies the final universal-completion
step with target `Janko4.Model`. `model_isTypeJ4` proves all the source
hypotheses on that literal matrix carrier, without a simplicity assumption.

The Aschbacher–Segev uniqueness theorem is not yet proved here. Its remaining
obligations are construction of the local geometry from these hypotheses,
equivalence of the local stabilizer maps, and the cycle-base theorem.

Sources: Aschbacher–Segev, Invent. Math. 105 (1991), 589–607, and their
exposition in *Groups, Combinatorics and Geometry*, pp.12–21. The intended
consumer is Aschbacher–Smith 8.2.14, printed p.723.
-/
