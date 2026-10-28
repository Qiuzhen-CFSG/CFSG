module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveComponentAction
public import Theory.Alternating.OddCentralCovers

/-!
# Faithfulness of the chosen covered-A₆ constituent

A quasisimple odd-central cover mapping onto the triple A₆ cover is already
isomorphic to it: the alternating multiplier bounds its center by three,
and the prescribed surjection identifies the central quotients. Faithfulness
of the literal restricted action follows, and survives actual conjugation
of the invariant subspace.

These are the component transports used by `SeedAlternativesMovedSylowTripleSix`,
the covered-A₆ exclusion in Aschbacher--Smith D.3.5(5), printed p.196.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325

theorem surjective_injective_of_tripleSix
    {K R : Type*} [Group K] [Finite K] [IsQuasisimple K]
    [Group R] [Finite R] [IsQuasisimple R]
    (f : K →* R) (hf : Function.Surjective f)
    (ho : Odd (Nat.card (center K)))
    (q : (R ⧸ center R) ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center R) = 3) : Function.Injective f := by
  let : Nontrivial R := (q.surjective.comp (QuotientGroup.mk'_surjective (center R))).nontrivial
  let e := IsQuasisimple.centralQuotientEquiv f hf
  have hz : Nat.card (center K) ≤ 3 := by
    rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) (e.trans q) ho with h | h
    · omega
    · omega
  have hb : Nat.card K ≤ Nat.card R := by
    rw [card_eq_card_quotient_mul_card_subgroup (center K),
      card_eq_card_quotient_mul_card_subgroup (center R),Nat.card_congr e.toEquiv,hc]
    exact Nat.mul_le_mul_left _ hz
  exact (hf.bijective_of_nat_card_le hb).injective

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W)

theorem invariant_injective_of_restrictedActionSurjection
    (K : Subgroup H) (I : Submodule (ZMod 2) W)
    (hI : K ≤ subspaceStabilizer ρ I)
    (hi : Function.Injective (restrictedActionSurjection ρ I K hI)) :
    Function.Injective (invariantSubspace ρ K I hI).toRepresentation := by
  intro a b he
  apply hi
  apply Subtype.ext
  apply subspaceImageRepresentation_injective ρ I
  exact he

theorem invariant_injective_conjugate
    (K : Subgroup H) [K.Normal] (I : Submodule (ZMod 2) W)
    (hI : K ≤ subspaceStabilizer ρ I) (t : H)
    (hJ : K ≤ subspaceStabilizer ρ (I.map (ρ t)))
    (hi : Function.Injective (invariantSubspace ρ K I hI).toRepresentation) :
    Function.Injective (invariantSubspace ρ K (I.map (ρ t)) hJ).toRepresentation := by
  let σ := (invariantSubspace ρ K (I.map (ρ t)) hJ).toRepresentation
  apply σ.ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  have hfix : ∀ v ∈ I.map (ρ t), ρ g.val v = v := by
    intro v hv
    exact congrArg Subtype.val (LinearMap.congr_fun hg (⟨v,hv⟩ : I.map (ρ t)))
  let a : K := MulAut.conjNormal t⁻¹ g
  have ha : (invariantSubspace ρ K I hI).toRepresentation a = 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ (t⁻¹ * g.val * (t⁻¹)⁻¹) v.val = v.val
    rw [inv_inv,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
      hfix (ρ t v.val) (Submodule.mem_map_of_mem v.property)]
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have ha1 : a = 1 := hi (ha.trans (map_one _).symm)
  exact mem_bot.mpr ((MulAut.conjNormal t⁻¹ : MulAut K).injective
    (ha1.trans (map_one _).symm))

theorem restricted_tripleSix_faithful
    [Finite H] (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (I : Submodule (ZMod 2) W) (hI : K ≤ subspaceStabilizer ρ I)
    (hcore : pCore 2 H = ⊥)
    {R : Type*} [Group R] [Finite R] [IsQuasisimple R]
    (j : restrictedSubgroup ρ I K ≃* R)
    (q : (R ⧸ center R) ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center R) = 3) :
    Nonempty (K ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Function.Injective (invariantSubspace ρ K I hI).toRepresentation := by
  let r := restrictedActionSurjection ρ I K hI
  let f := j.toMonoidHom.comp r
  have hf : Function.Surjective f := j.surjective.comp (restrictedActionSurjection_surjective ρ I K hI)
  have ho := GLS3.Chapter5.OddCentralCovers.component_center_odd hcore K
    ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  have hi := surjective_injective_of_tripleSix f hf ho q hc
  obtain ⟨e⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode q hc
  refine ⟨⟨(MulEquiv.ofBijective f ⟨hi,hf⟩).trans e⟩,?_⟩
  apply invariant_injective_of_restrictedActionSurjection ρ K I hI
  intro x y hxy
  exact hi (congrArg j hxy)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
