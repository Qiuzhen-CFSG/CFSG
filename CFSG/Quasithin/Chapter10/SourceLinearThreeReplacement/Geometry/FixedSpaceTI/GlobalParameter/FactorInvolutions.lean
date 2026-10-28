module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.GlobalLower
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Actor

/-!
# Involutions on the original moved factors

In the positive fixed-space branch the actual moved factor is a central cover
of the natural binary three-space and has dimension four. A common normalizer
acts through the original component, so every nontrivial involutory action on
this factor fixes exactly four vectors. An element exchanging the two factors
fixes at most their intersection, which has at most two elements. These bounds
retain the central intersection and do not assume a direct product.

Source: Aschbacher--Smith 10.3.1, printed p.755, using I.1.6 and B.4.8(2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.GlobalParameter
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (s : SourceLinearThreeSurvivor T D)

local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

include s

/-- The nonzero full fixed part forces the literal moved factor to have order sixteen. -/
theorem moved_card_sixteen
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 16 :=
  BinaryThree.moved_card_eq_sixteen D ⟨s.quotient,⟨s.natural⟩⟩
    (moved_fixed_ne_bot D s hfix)

/-- The two exchanged factors can intersect only in the original fixed kernel. -/
theorem intersection_card_le_two :
    Nat.card (⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom : Subgroup G) ≤ 2 := by
  have hle : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom ≤ sourceMovedFixed D :=
    le_inf inf_le_left (inf_le_right.trans s.crossed)
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)).trans
    (BinaryThree.moved_fixed_card_le_two D ⟨s.quotient,⟨s.natural⟩⟩)

/-- Every actor exchanging the original components fixes at most two vectors
in the first moved factor; no order assumption is needed. -/
theorem exchanging_fixed_card_le_two {n : G} (hn : n ∈ D.maximalLocal)
    (hnL : n ∉ normalizer (L : Set G)) :
    Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer ({n} : Set G) : Subgroup G) ≤ 2 := by
  have hLn : L.map (MulAut.conj n).toMonoidHom =
      L.map (MulAut.conj s.exchange).toMonoidHom := by
    rcases source_nonnormal_maximal_pair D (survivor_nonnormal s)
      s.exchange_mem s.exchange_moves n hn with h | h
    · exact False.elim (hnL (mem_normalizer_iff_map_conj_eq.mpr h))
    · exact h
  have hWn : (⁅D.fullModule,L⁆).map (MulAut.conj n).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
    have hV (m : G) (hm : m ∈ D.maximalLocal) :
        D.fullModule.map (MulAut.conj m).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
    rw [map_commutator,map_commutator,hV n hn,
      hV s.exchange (le_normalizer_componentOrbit L T s.exchange_mem),hLn]
  have hle : ⁅D.fullModule,L⁆ ⊓ centralizer ({n} : Set G) ≤
      ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
    intro w hw
    refine ⟨hw.1,?_⟩
    rw [←hWn]
    have he : (MulAut.conj n) w = w :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hw.2).symm
    exact he ▸ mem_map_of_mem (MulAut.conj n).toMonoidHom hw.1
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)).trans
    (intersection_card_le_two D s)

/-- A nontrivial involutory common-normalizer action fixes exactly a four-group
in the original four-dimensional cover. The ambient actor may have larger order. -/
theorem preserving_fixed_card_four
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {n : G} (hn : n ∈ D.maximalLocal) (hnL : n ∈ normalizer (L : Set G))
    (hsq : ∀ w ∈ ⁅D.fullModule,L⁆, n*(n*w*n⁻¹)*n⁻¹ = w)
    (hmove : n ∉ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer ({n} : Set G) : Subgroup G) = 4 := by
  let W := ⁅D.fullModule,L⁆
  have hmodel : BinaryThreeNatural D := ⟨s.quotient,⟨s.natural⟩⟩
  obtain ⟨e,σ,p,hp,hσ,_⟩ := BinaryThree.moved_cover D hmodel
  have hnW : n ∈ normalizer (W : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅D.fullModule,L⁆).map _ = _
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hn),
      mem_normalizer_iff_map_conj_eq.mp hnL]
  obtain ⟨l,hl,hact⟩ := BinaryThree.common_normalizer_acts_through_component D hmodel hnL hnW
  let g := e (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)
  have haction (w : Additive W) : ((σ g w).toMul : G) = n*w.toMul*n⁻¹ :=
    (hσ ⟨l,hl⟩ w).trans (hact w.toMul w.toMul.property).symm
  have hg2 : g*g=1 := by
    apply OneCohomology.SLThreeCentralExtension.cover_faithful σ p hp
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [map_mul,map_one,Module.End.mul_apply,Module.End.one_apply]
    rw [haction,haction]
    exact hsq w.toMul w.toMul.property
  have hg1 : g ≠ 1 := by
    intro he
    apply hmove
    intro w hw
    have hh := haction (Additive.ofMul ⟨w,hw⟩)
    rw [he,map_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have horder : orderOf g = 2 :=
    orderOf_eq_prime_iff.mpr ⟨by simpa [pow_two] using hg2,hg1⟩
  have hd : Module.finrank (ZMod 2) (Additive W) = 4 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod,show Nat.card (Additive W) = 16 from moved_card_sixteen D s hfix] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) (hc.symm.trans (by decide : 16=2^4))
  have hcod := BinaryLinearThree.NaturalExtension.involution_codim_of_commutator_top
    σ hd hp.2.2 g horder
  have hf := fixedCodim_add_finrank σ (zpowers g)
  have hfd : Module.finrank (ZMod 2) (fixedSpace σ (zpowers g)) = 2 := by
    change fixedCodim σ (zpowers g) + _ = Module.finrank (ZMod 2) (Additive W) at hf
    omega
  have hiff (w : Additive W) :
      w ∈ fixedSpace σ (zpowers g) ↔ (w.toMul : G) ∈ centralizer ({n} : Set G) := by
    rw [mem_fixedSpace_zpowers_iff,mem_centralizer_singleton_iff]
    constructor
    · intro hw
      have hh := haction w
      rw [hw] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    · intro hw
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [haction]
      exact mul_inv_eq_iff_eq_mul.mpr hw.symm
  let E : fixedSpace σ (zpowers g) ≃ (W ⊓ centralizer ({n} : Set G) : Subgroup G) := {
    toFun := fun w => ⟨w.val.toMul,w.val.toMul.property,(hiff w.val).mp w.property⟩
    invFun := fun w => ⟨Additive.ofMul ⟨w,w.property.1⟩,(hiff _).mpr w.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [←Nat.card_congr E,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hfd]
  norm_num

/-- The actual first-factor index needed for the full automizer bound, covering
both preserving and exchanging actors. -/
theorem moving_factor_index_ge_four
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {n : G} (hn : n ∈ D.maximalLocal)
    (hsq : ∀ w ∈ ⁅D.fullModule,L⁆, n*(n*w*n⁻¹)*n⁻¹ = w)
    (hmove : n ∉ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    4 ≤ (centralizer ({n} : Set G)).relIndex ⁅D.fullModule,L⁆ := by
  have hc : Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer ({n} : Set G) : Subgroup G) ≤ 4 := by
    by_cases hnL : n ∈ normalizer (L : Set G)
    · exact (preserving_fixed_card_four D s hfix hn hnL hsq hmove).le
    · exact (exchanging_fixed_card_le_two D s hn hnL).trans (by decide)
  have he := card_mul_index ((centralizer ({n} : Set G)).subgroupOf ⁅D.fullModule,L⁆)
  have hcard : Nat.card ((centralizer ({n} : Set G)).subgroupOf ⁅D.fullModule,L⁆) =
      Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer ({n} : Set G) : Subgroup G) :=
    Nat.card_congr {
      toFun := fun x => ⟨x.val,x.val.property,x.property⟩
      invFun := fun x => ⟨⟨x,x.property.1⟩,x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change _ * (centralizer ({n} : Set G)).relIndex ⁅D.fullModule,L⁆ = _ at he
  rw [hcard,moved_card_sixteen D s hfix] at he
  nlinarith

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.GlobalParameter
