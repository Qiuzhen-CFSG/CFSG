module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CoreOneTwentyEight
public import Theory.GroupTheory.CentralSixteenQuinticOrder256
public import Theory.GroupTheory.SimpleFiveSixteenSectionAction

/-!
# The original core of order at most 256

Use the actual component action on the whole local core modulo its central
natural sixteen. If that action vanishes, a genuine quintic subgroup and
coprime splitting reduce the derived subgroup to that of a two-group of
order at most sixteen. It is cyclic. Otherwise the original two-perfect
component forces the quotient to be elementary of order sixteen, and the
whole original core has order 256.

The second alternative keeps the literal quotient and its nontrivial
component action. It does not select either four-dimensional A5 module,
assert a residual lift, or close the remaining nonsolvable branch.
Source application: Aschbacher--Smith 13.2.8(1), printed p.880.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- At the first remaining core order, either its derived subgroup is cyclic
or the actual central quotient is elementary sixteen and is moved by L. -/
theorem core_cyclic_or_elementary_sixteen_quotient
    (d : Context T L V V₁ V₂ V₃)
    (hsmall : Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≤ 256) :
    IsCyclic (⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,
      (L ⊔ (T : Subgroup G)).pCoreIn 2⁆ : Subgroup G) ∨
      (Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) = 256 ∧
        ∃ hV : (V.subgroupOf (L ⊔ (T : Subgroup G))).Normal,
          letI := hV
          let Q := (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)).map
            (QuotientGroup.mk' (V.subgroupOf (L ⊔ (T : Subgroup G))))
          Nat.card Q = 16 ∧ IsElementaryAbelian 2 Q ∧
            ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ ≠ V) := by
  let H := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf H
  let Q := pCore 2 H
  have hVH : V ≤ H := d.chosen.le_sylow.trans le_sup_right
  let hUn : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le d.chosen.normalizes d.flag.T_normalizes)
  let := hUn
  let π := QuotientGroup.mk' U
  let A := Q.map π
  let : A.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective U)
  let f : L →* H := inclusion le_sup_left
  let ρ : L →* MulAut A := (MulAut.conjNormal : (H ⧸ U) →* MulAut A).comp (π.comp f)
  have hUQ : U ≤ Q := by
    intro v hv
    obtain ⟨x,hx,he⟩ := d.chosen.le_core hv
    exact (show x=v from Subtype.ext he) ▸ hx
  have hcardU : Nat.card U = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv).trans d.module_card
  have hproduct : 16 * Nat.card A = Nat.card Q := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map Q π
    rwa [QuotientGroup.ker_mk',inf_of_le_right hUQ,hcardU] at hh
  have hcardA : Nat.card A ≤ 16 := by
    change Nat.card Q ≤ 256 at hsmall
    omega
  have hf : f.range = L.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
  have hcomm_iff : ρ = 1 ↔ ⁅H.pCoreIn 2,L⁆ ≤ V := by
    constructor
    · intro ha
      have hc : f.range.map π ≤ centralizer (A : Set (H ⧸ U)) := by
        rintro _ ⟨_,⟨l,rfl⟩,rfl⟩ a haA
        have he := congrArg (fun b : MulAut A => (b ⟨a,haA⟩ : H ⧸ U))
          (DFunLike.congr_fun ha l)
        change π (f l) * a * (π (f l))⁻¹ = a at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm
      have hcomm : ⁅Q,f.range⁆ ≤ U := by
        rw [←QuotientGroup.ker_mk' U,←Subgroup.map_eq_bot_iff,map_commutator]
        exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
      have hm := map_mono (f := H.subtype) hcomm
      rw [map_commutator,hf,map_subgroupOf_eq_of_le hVH,
        map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left)] at hm
      exact hm
    · intro hc
      apply MonoidHom.ext
      intro l
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      obtain ⟨x,hx,hxa⟩ := a.property
      change π (f l) * a.val * (π (f l))⁻¹ = a.val
      rw [←hxa]
      apply mul_inv_eq_iff_eq_mul.mpr
      have hxQ : (x : G) ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype hx
      have hcG := hc (commutator_mem_commutator hxQ l.property)
      have hcH : ⁅x,f l⁆ ∈ U := hcG
      have hz : π ⁅x,f l⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcH
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hz
      exact hz.symm
  by_cases ha : ρ = 1
  · left
    obtain ⟨B,hBL,hB,hfixed⟩ := d.exists_quintic_module_fixer_eq_bot
    have hBQ : B ≤ normalizer (H.pCoreIn 2 : Set G) :=
      (hBL.trans le_sup_left).trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
    have hcomm : ⁅H.pCoreIn 2,B⁆ ≤ V :=
      (commutator_mono le_rfl hBL).trans (hcomm_iff.mp ha)
    have hsize : Nat.card (H.pCoreIn 2) ≤ 256 := by
      rwa [pCoreIn,card_map_of_injective H.subtype_injective]
    exact cyclic_derived_of_central_sixteen_quintic_of_card_le_256
      (H.pCoreIn 2) V B (isPGroup_pCoreIn 2 H) d.chosen.le_core
      (le_centralizer_iff.mp d.chosen.core_centralizes) d.module_card hB hBQ
      hcomm hfixed hsize
  · right
    let : IsSimpleGroup (L ⧸ pCore 2 L) := d.quotient.isSimpleGroup
    have hfive : 5 ∣ Nat.card (L ⧸ pCore 2 L) := by
      rw [Nat.card_congr d.quotient.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    obtain ⟨hA,hAe⟩ := elementary_sixteen_of_nontrivial_simple_five_action
      d.twoPerfect hfive (pCore_isPGroup.map π) hcardA ρ ha
    have hQ : Nat.card Q = 256 := by rw [hA] at hproduct; omega
    refine ⟨hQ,hUn,hA,hAe,?_⟩
    intro he
    exact ha (hcomm_iff.mpr he.le)

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
