module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Actions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Recognition.SmallDegree
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Dimensions
public import Theory.Representation.PSL3Two.ElementaryEightAction

/-!
# Natural recognition from an involution of displacement at most two

For a faithful action of the literal SL₃(2) on a finite elementary binary
group, an involution moving at most one dimension forces both the full moving
space and the quotient by fixed vectors to have dimension at most three.
The existing three-conjugate generation and duality bounds give these two
inequalities. `Recognition.linear_splitting` supplies the fixed complement.

The subgroup/subspace order isomorphism identifies these summands with the
literal action commutator and fixed subgroup. The moving subgroup has order
eight and a faithful restricted action, so a basis gives natural coordinates
and an automorphism marking of SL₃(2), with the required equivariance equation.
No splitting or natural-module hypothesis is assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), binary specialization of (1.4)--(1.5), pp.842--843, applied in
(4.3.1)(iii), p.883.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting.Recognition

variable {E : Type*} [Group E] [IsElementaryAbelian 2 E]

private abbrev subgroupSpace : Subgroup E ≃o Submodule (ZMod 2) (Additive E) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

private theorem moving_space_eq (ρ : SL →* MulAut E) :
    subgroupSpace (commutatorAction ρ.range E) = Coinvariants.ker (Offenders.linearize ρ) := by
  apply le_antisymm
  · change commutatorAction ρ.range E ≤
      (Coinvariants.ker (Offenders.linearize ρ)).toAddSubgroup.toSubgroup'
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨⟨a, g, rfl⟩, v, rfl⟩
    change -Additive.ofMul v + Offenders.linearize ρ g (Additive.ofMul v) ∈
      Coinvariants.ker (Offenders.linearize ρ)
    simpa only [sub_eq_add_neg, add_comm] using
      Coinvariants.sub_mem_ker (ρ := Offenders.linearize ρ) g (Additive.ofMul v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change ρ g v.toMul / v.toMul ∈ commutatorAction ρ.range E
    rw [div_eq_mul_inv, commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨ρ g, g, rfl⟩, v.toMul, mul_comm _ _⟩

private theorem fixed_space_eq (ρ : SL →* MulAut E) :
    subgroupSpace (FixedPoints.subgroup ρ.range E) = fixedSpace (Offenders.linearize ρ) ⊤ := by
  ext v
  constructor
  · intro hv g
    exact congrArg Additive.ofMul (hv ⟨ρ g.val, g.val, rfl⟩)
  · intro hv a
    obtain ⟨g, hg⟩ := a.property
    change a.val v.toMul = v.toMul
    rw [← hg]
    exact congrArg Additive.toMul (hv ⟨g, mem_top g⟩)

private theorem small_fixedCodim [Finite E] (ρ : SL →* MulAut E) (t : SL)
    (hsmall : Nat.card (commutatorAction (zpowers (ρ t)) E) ≤ 2) :
    fixedCodim (Offenders.linearize ρ) (zpowers t) ≤ 1 := by
  let C := commutatorAction (zpowers (ρ t)) E
  have hc : 2 ^ Module.finrank (ZMod 2) (subgroupSpace C) ≤ 2 ^ 1 := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subgroupSpace C)
    rw [Nat.card_zmod] at he
    rw [← he]
    exact hsmall
  have hd : Module.finrank (ZMod 2) (subgroupSpace C) ≤ 1 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  rw [fixedCodim_zpowers_eq_displacement_rank]
  apply (Submodule.finrank_mono (t := subgroupSpace C) ?_).trans hd
  rintro _ ⟨v, rfl⟩
  change ρ t v.toMul / v.toMul ∈ commutatorAction (zpowers (ρ t)) E
  rw [div_eq_mul_inv, commutatorAction_eq_closure]
  exact Subgroup.subset_closure ⟨⟨ρ t, mem_zpowers (ρ t)⟩, v.toMul, mul_comm _ _⟩

private noncomputable def movingAction (ρ : SL →* MulAut E) :
    SL →* MulAut (commutatorAction ρ.range E) := by
  letI : IsInvariant ρ.range E (commutatorAction ρ.range E) := commutatorAction_isInvariant
  exact (MulDistribMulAction.toMulAut ρ.range (commutatorAction ρ.range E)).comp ρ.rangeRestrict

omit [IsElementaryAbelian 2 E] in
private theorem movingAction_apply (ρ : SL →* MulAut E) (g : SL)
    (v : commutatorAction ρ.range E) : (movingAction ρ g v : E) = ρ g v := rfl

private theorem movingAction_injective [Finite E] (ρ : SL →* MulAut E)
    (hinj : Function.Injective (movingSubrepresentation (Offenders.linearize ρ)).toRepresentation) :
    Function.Injective (movingAction ρ) := by
  intro g h he
  apply hinj
  ext v
  let w : commutatorAction ρ.range E :=
    ⟨v.val.toMul, (show v.val ∈ subgroupSpace (commutatorAction ρ.range E) from
      (moving_space_eq ρ).symm ▸ v.property)⟩
  have hw := congrArg (fun a : MulAut (commutatorAction ρ.range E) => (a w : E)) he
  exact congrArg Additive.ofMul hw

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting.Recognition

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
open Recognition

variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- A faithful binary SL₃(2) action whose involution displacement subgroup has
order at most two splits as its intrinsic moving subgroup and fixed subgroup. The moving
subgroup has actual natural coordinates for one automorphism marking of SL₃(2). -/
theorem naturalActionSplitting_of_small_involution (ρ : SL →* MulAut E)
    (hfaithful : Function.Injective ρ) (hsmall : HasSmallInvolution ρ) :
    Nonempty (NaturalActionSplitting ρ) := by
  obtain ⟨t, ht, htwo, hcard⟩ := hsmall
  let σ := Offenders.linearize ρ
  have hn : ∃ g v, σ g v ≠ v := by
    by_contra! h
    apply ht
    apply hfaithful
    rw [map_one]
    ext v
    exact congrArg Additive.toMul (h t (Additive.ofMul v))
  have hcod : fixedCodim σ (zpowers t) ≤ 1 := small_fixedCodim ρ t hcard
  have hm := ModuleAlternatives.Models.commutator_finrank_le_three_mul σ t htwo ht
  have hf := ModuleAlternatives.Models.fixedCodim_top_le_three_mul σ t htwo ht
  obtain ⟨hd, hfaith, hcompl⟩ := linear_splitting σ hn (by omega) (by omega)
  have hcomplG : IsCompl (commutatorAction ρ.range E) (FixedPoints.subgroup ρ.range E) := by
    apply subgroupSpace.isCompl_iff.mpr
    rw [moving_space_eq, fixed_space_eq]
    exact hcompl
  have hcardW : Nat.card (commutatorAction ρ.range E) = 8 := by
    change Nat.card (subgroupSpace (commutatorAction ρ.range E)) = 8
    rw [moving_space_eq, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    decide
  let : IsElementaryAbelian 2 (commutatorAction ρ.range E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun v =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) v.val)) }
  obtain ⟨coordinates, marking, ha⟩ := Matrix.PSL3Two.exists_natural_marking
    (commutatorAction ρ.range E) hcardW (movingAction ρ) (movingAction_injective ρ hfaith)
  refine ⟨⟨marking, coordinates, hcomplG.sup_eq_top, hcomplG.disjoint, ?_⟩⟩
  intro g v w hw
  have he : w = movingAction ρ g v := Subtype.ext hw
  rw [he]
  exact ha g v

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
