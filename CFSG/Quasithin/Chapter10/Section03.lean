module

public import Theory.SpecificGroups.PSL3Two.AlternatingFiveObstruction

/-!
# The terminal group-model obstruction in §10.3

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), §10.3, pp. 755–757, concludes the proof of Theorem 10.0.1 by
constructing a new counterexample component with quotient A₅. Corollary 10.2.13
applied to that component would identify the same quotient with L₃(2).

The theorem below proves that last incompatibility for the actual group models,
using the order obstruction in `Theory.SpecificGroups.PSL3Two`. It is independent
of the chapter-local constructions. The centralizer lemmas 10.3.1–10.3.3 and
the construction of the new maximal component are still needed to establish
Theorem 10.0.1; this module does not assert that theorem yet.
-/

namespace CFSG.Quasithin.Chapter10

/-- The quotient of the replacement component in the final paragraph of §10.3
cannot have both of the isomorphism types forced there. -/
public theorem incompatible_replacement_quotient
    {Q : Type*} [Group Q]
    (hA : Nonempty (Q ≃* alternatingGroup (Fin 5)))
    (hL : Nonempty (Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) :
    False := by
  obtain ⟨a⟩ := hA
  obtain ⟨l⟩ := hL
  exact Matrix.PSL3Two.not_nonempty_alternatingFive_equiv ⟨a.symm.trans l⟩

end CFSG.Quasithin.Chapter10
