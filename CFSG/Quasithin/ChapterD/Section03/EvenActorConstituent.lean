module
public import CFSG.Quasithin.ChapterD.Section03.EvenConstituent
public import Theory.Representation.NormalConstituentDisplacement
public import Theory.Representation.NormalSimpleConstituent

/-!
# Selecting even-linear constituents from the actual cubic actor

A starred actor moving a normal binary SL2 component recognizes every simple
component constituent when its rank is at most the field degree. A preserved
constituent inherits the actor's cubic bound. If a constituent moves, its
entire dimension injects into the actor displacement, hence is at most twice
the field degree. The small-degree classification again gives the natural
or Hermitian module, excluding the SL2(8) triple by its dimension.

No constituent invariance or isotypy is assumed. The original central Hall
consumer retains its literal component quotient and both seed orientations.
Source: Aschbacher--Smith D.3.9 and D.3.21, pp.199--207, using D.2.5
and the binary rank-one classification G.9.3 and K.3.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- A bounded starred actor constructs actual constituent models even when it
moves the chosen constituent. The fixed component marking is retained. -/
theorem even_constituent_of_bounded_starred_actor
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (e : L ≃* SL(2,F)) (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup G) (hA : A ∈ QhatStar ρ)
    (hsmall : cubicRatio ρ ≤ 2) (hrank : rank A ≤ n)
    (hmove : ¬ A ≤ centralizer (L : Set G))
    (U : Subrepresentation (ρ.comp L.subtype)) (hU : U.toRepresentation.IsIrreducible) :
    Module.finrank (ZMod 2) U.toSubmodule = 2*n ∧
      (SL2.BinarySmall.IsNatural (U.toRepresentation.comp e.symm.toMonoidHom) ∨
        ∃ s : ℕ, n = 2*s ∧ ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩;
          SL2.BinarySmall.IsHermitian (U.toRepresentation.comp e.symm.toMonoidHom) s) := by
  have hfaith := normal_simple_constituent_faithful ρ hf hi L U hU
  by_cases hstable : A ≤ subspaceStabilizer ρ U.toSubmodule
  · have hgen : ⁅L,A⁆ = L := IsComponent.commutator_eq_self_of_normalizes
      (show IsComponent G L from ⟨(inferInstance : L.Normal).isSubnormal,inferInstance⟩)
      (by rw [normalizer_eq_top]; exact le_top) (by
        intro he
        exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)))
    have hfix : fixedSpace ρ L = ⊥ := fixedSpace_eq_bot_of_normal_faithful_irreducible
      ρ hf hi L ((Subgroup.nontrivial_iff_ne_bot L).mp inferInstance)
    have hLU : L ≤ subspaceStabilizer ρ U.toSubmodule :=
      le_subspaceStabilizer ρ _ (fun l hl v hv => U.apply_mem_toSubmodule ⟨l,hl⟩ hv)
    have hnfix : ¬ U.toSubmodule ≤ fixedSpace ρ A := by
      intro hh
      have hz := le_fixedSpace_commutator_of_invariant ρ hLU hh
      rw [hgen,hfix] at hz
      exact ((Subrepresentation.irreducible_iff_isAtom U).mp hU).ne_bot
        (Subrepresentation.toSubmodule_injective (bot_unique hz))
    have hR := RPlusBound.restricted ρ
      (show A ∈ RPlusBound ρ 2 from ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hsmall⟩,
        QhatStar.mem_RPlus ρ hA⟩) U.toSubmodule hstable hnfix
    exact even_subspace_actor_recognition ρ L hL e n hn hF U hU hfaith _
      ⟨hR.1,isCubic_restrictedSubgroup ρ U.toSubmodule hA.1.2.2.1,hR.2⟩
  · obtain ⟨a,ha,han⟩ := Set.not_subset.mp hstable
    have hdim : Module.finrank (ZMod 2) U.toSubmodule ≤
        Module.finrank (ZMod 2) (ρ a-1).range := by
      by_contra! hh
      exact han ((subspace_map_eq_iff ρ U.toSubmodule a).mp
        (map_constituent_eq_self_of_displacement_lt ρ L a U hU hh))
    have hb := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hsmall)
    have hd : Module.finrank (ZMod 2) U.toSubmodule ≤ 2*n := hdim.trans
      ((NaturalTensor.operatorFixedCodim_le_fixedCodim ρ A ha).trans
        (hb.trans (Nat.mul_le_mul_left 2 hrank)))
    let σ : Representation (ZMod 2) SL(2,F) U.toSubmodule := U.toRepresentation.comp e.symm.toMonoidHom
    let : σ.IsIrreducible :=
      (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr hU
    rcases ChapterG.Section09.DefiningCharacteristic.binary_small_faithful_classification
        σ (hfaith.comp e.symm.injective) n hn hF (by omega) with h | h | h
    · exact ⟨h.2.1,Or.inl h.2.2⟩
    · exact ⟨h.2.1,Or.inr ⟨_,h.1.symm,h.2.2⟩⟩
    · have := h.2.1
      have := h.2.2.1
      omega
end CFSG.Quasithin.ChapterD
