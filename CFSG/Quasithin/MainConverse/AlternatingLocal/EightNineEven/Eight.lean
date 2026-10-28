module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.MainConverse.Transport
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.BinaryHigherEven
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Even characteristic of A₈

The constructed exceptional equivalence identifies A₈ with the actual central
quotient PSL₄(𝔽₂). The binary linear local calculation proves that every maximal
two-local has self-centralizing intrinsic two-core: its nontrivial two-subgroup
has a nonzero proper fixed space, and maximality identifies the local with that
space's parabolic. The parabolic's self-centralizing normal unipotent radical
lies in its two-core. Transport along the equivalence gives condition E for A₈.

The equivalence comes from the ATLAS port's faithful deleted permutation module
and exterior-square action on the same quadratic space; its construction and
attribution are in `Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8`.
The binary local calculation is independent of the alternating-group converse.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(3), printed pp.3–4, repeated on pp.481–482.
-/

namespace CFSG.Quasithin.MainConverse

/-- The actual alternating group on eight points satisfies source condition E. -/
public theorem alternatingEight_evenCharacteristic :
    IsEvenCharacteristic (alternatingGroup (Fin 8)) := by
  apply psl4_two_evenCharacteristic
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩

end CFSG.Quasithin.MainConverse
