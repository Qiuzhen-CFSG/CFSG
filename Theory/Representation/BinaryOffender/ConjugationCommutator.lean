module
public import Theory.Representation.BinaryOffender.ConjugationGeneration
public import Theory.Representation.ElementaryPerfectSplit

/-!
# From elementary displacement generation to group commutators

For the literal conjugation representation of C on an elementary abelian U,
full linear displacement generation implies [U,C]=U. Pull the group
commutator back to a binary subspace of U; every linear displacement lies
there, so the whole module does. This is the reverse of the transport in
ConjugationGeneration, with the same subgroup and action conventions.

The original Fano-orbit application is FixedCoreSource/Amalgam/LinearFixedFree.
Source: the group/module commutator convention in Aschbacher–Smith B.1,
and its use in 13.4.7, printed p.901.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Representation.BinaryOffender
variable {G : Type*} [Group G]

/-- Full linear displacement generation implies the literal group commutator equality. -/
theorem group_commutator_eq_of_elementary_moved
    (U C : Subgroup G) [IsElementaryAbelian 2 U]
    (hn : C ≤ normalizer (U : Set G))
    (hm : subspaceCommutator (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hn))) ⊤ ⊤ = ⊤) : ⁅U,C⁆ = U := by
  let R := ⁅U,C⁆
  let E := R.subgroupOf U
  let W : Submodule (ZMod 2) (Additive U) := AddSubgroup.toZModSubmodule 2 E.toAddSubgroup
  have hd : subspaceCommutator (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hn))) ⊤ ⊤ ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c,_,v,_,rfl⟩
    change (c.val * v.toMul.val * c.val⁻¹) / v.toMul.val ∈ R
    have hh := commutator_mem_commutator c.property v.toMul.property
    rw [commutator_comm] at hh
    simpa only [commutatorElement_def,div_eq_mul_inv] using hh
  rw [hm] at hd
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp hn
  · intro u hu
    exact hd (show Additive.ofMul (⟨u,hu⟩ : U) ∈ (⊤ : Submodule (ZMod 2) (Additive U)) from Submodule.mem_top)
end Representation.BinaryOffender
