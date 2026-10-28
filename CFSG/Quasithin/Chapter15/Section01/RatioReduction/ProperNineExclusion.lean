module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ReducibleFactors
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.NineIrreducible
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FactorSubspace
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.ElementaryNineCore
/-!
# Excluding the literal elementary-nine proper orbit factor

The original factor carrier maps injectively to the centralizer quotient of
its actual binary subgroup. Its marked elementary-nine kernel is the
three-core. The original Sylow-stable proper subspace transports through
this same quotient, contradicting the proved elementary-nine extension
irreducibility under the original ordering and partner hypotheses.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_no_nine_proper_factor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let q : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let S := (T.subtype hM.1.2 : Subgroup M).map q
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ i (l : CyclicSource.LocalGeneration (d.factor i).action),
      letI := BinaryGroupAction.action (d.factor i).action
      letI : Finite (d.factor i).Space := Module.finite_of_finite (ZMod 2)
      letI : IsElementaryAbelian 2 (Multiplicative (d.factor i).Space) := BinaryGroupAction.elementary
      letI := l.normal
      ChapterD.Section02.ElementaryNineEndpoint (V := Multiplicative (d.factor i).Space)
        l.kernel l.involution →
      ∀ B : Submodule (ZMod 2) (Additive V), B ≠ ⊥ → B < (c.ambientFactor d i).space →
        (c.ambientFactor d i).actor ⊔
          (S ⊓ subspaceStabilizer ρ (c.ambientFactor d i).space) ≤ subspaceStabilizer ρ B → False := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let q := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  have hq : Function.Surjective q := MonoidHom.rangeRestrict_surjective _
  have hact (m : M) (v : Additive V) :
      ((ρ (q m) v).toMul : G) = (m:G) * v.toMul * (m:G)⁻¹ := rfl
  dsimp only
  intro U c d hd i l
  let := BinaryGroupAction.action (d.factor i).action
  let : Finite (d.factor i).Space := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (d.factor i).Space) := BinaryGroupAction.elementary
  let := l.normal
  intro h9 B hB0 hB hstable
  have hk : l.kernel = pCore 3 (d.factor i).Carrier :=
    l.kernel_eq_threeCore_of_elementary_nine h9.kernel_elementary h9.card_kernel
  let : IsElementaryAbelian 3 (pCore 3 (d.factor i).Carrier) := hk ▸ h9.kernel_elementary
  have hcard : Nat.card (pCore 3 (d.factor i).Carrier) = 9 := hk ▸ h9.card_kernel
  have hncyc : ¬ IsCyclic (pCore 3 (d.factor i).Carrier) := by
    intro hc
    let := hc
    have hh := IsElementaryAbelian.exponent_dvd_p 3 (pCore 3 (d.factor i).Carrier)
    rw [IsCyclic.exponent_eq_card,hcard] at hh
    norm_num at hh
  have htmove : l.involution ∉ centralizer (pCore 3 (d.factor i).Carrier : Set _) := by
    intro ht
    rw [←hk] at ht
    have hzero : ⁅l.kernel,zpowers l.involution⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr ht)
    exact l.nontrivial (l.commutator.symm.trans hzero)
  let F := c.ambientFactor d i
  let : F.actor.Normal := source_localAction_factor_actor_normal hG T hempty hM hmany hJ
    U c d hd 3 (by decide) i hncyc l.involution l.order_two htmove
  let hVM := localModule_le T hM.1.2
  let W := F.internalSubgroup hVM ρ
  let : W.Normal := F.internalSubgroup_normal hVM ρ q hact
  let r := F.internalProjection hVM ρ q hq hact
  let j := r.comp F.embedding.groupMap
  have hj : Function.Injective j := F.internalProjection_factor_injective hVM ρ q hq hact
  let : IsElementaryAbelian 3 (pCore 3 F.Carrier) := hk ▸ h9.kernel_elementary
  let P := (pCore 3 F.Carrier).map j
  let : P.Normal := F.internalProjection_core_normal hVM ρ q hq hact 3
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.map j
  let σ := NormalElementaryQuotient.representation W (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let e := F.internalSpaceEquiv hVM ρ
  have he (g : F.Carrier) (v : F.Space) : e (F.action g v) = σ (j g) (e v) :=
    F.internalProjection_intertwines hVM ρ q hq hact g v
  have hP : Nat.card P = 9 := by
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (pCore 3 F.Carrier) j hj).toEquiv).symm.trans hcard
  have hdim : Module.finrank (ZMod 2) (Additive W) = 4 := by
    rw [← e.finrank_eq]
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) F.Space = 2 ^ 4
    have hc : Nat.card F.Space = 2 ^ Module.finrank (ZMod 2) F.Space := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact hc.symm.trans ((Nat.card_congr (Multiplicative.toAdd (α := F.Space))).symm.trans h9.card_module)
  have hmoved : subspaceCommutator σ ⊤ P = ⊤ := by
    have hh := subspaceCommutator_map_embedding F.action σ j e.symm.toLinearMap (fun g v => by
      apply e.injective
      rw [he]
      change σ (j g) (e (e.symm v)) = e (e.symm (σ (j g) v))
      rw [e.apply_symm_apply,e.apply_symm_apply]) l.kernel ⊤
    have hfull : subspaceCommutator F.action ⊤ l.kernel = ⊤ := l.moved
    rw [Submodule.map_top,LinearEquiv.range,hfull] at hh
    have hkF : l.kernel = pCore 3 F.Carrier := hk
    rw [hkF] at hh
    apply Submodule.map_injective_of_injective e.symm.injective
    rw [←hh,Submodule.map_top,LinearEquiv.range]
  have hPR : P ≤ F.actor.map r := by
    change (pCore 3 F.Carrier).map (r.comp F.embedding.groupMap) ≤ F.actor.map r
    rw [←map_map]
    exact map_mono (map_le_range (f := F.embedding.groupMap) (H := pCore 3 F.Carrier))
  exact F.internal_not_irreducible_of_proper_subspace hVM ρ q hq hact
    (T.subtype hM.1.2 : Subgroup M) B hB0 hB hstable
    (source_nine_extension_irreducible hG T hempty hM hJ hu hne W P hP hdim hmoved
      (F.actor.map r) hPR)
end CFSG.Quasithin.Chapter15.Section01
