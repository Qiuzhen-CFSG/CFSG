module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChief
public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Natural
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SL2
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.SpecificGroups.SL2.OddFixedVectors

/-!
# The two natural chief factors and the Sylow quotient contribution

The original cubic fixes no nonzero vector of a natural SL₂(2ⁿ) module,
so that module contributes n to cubic chief length. A natural subgroup
inside T lies in O₂(L): its intersection with L is invariant, and a
trivial intersection would make the cubic fix the whole subgroup.
The actual Sylow quotient adds log₄(2ⁿ), using the original cubic image.
Thus n>1 gives the three-factor lower bound used in 5.1.23.

Natural-module recognition remains explicit. The Chapter 12 application
uses any such natural subgroup in the original Sylow, and retains the
previously constructed opposite projection. It does not assert that the
original source hypotheses construct that subgroup, or prove fixedness.
Source: Aschbacher--Smith 5.1.22--23, printed pp.645--646,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V C : Subgroup G} {n : ℕ}

/-- An actual cubic has no natural fixed vector. -/
theorem natural_cubic_fixed_eq_bot (hnat : IsNaturalModule L V n)
    (hC : Nat.card C = 3) (hCL : C ≤ L) :
    V ⊓ centralizer (C : Set G) = ⊥ := by
  have hdis : Disjoint C (L.pCoreIn 2) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 L).exists_card_eq
    rw [hC,hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hne : C ≠ ⊥ := by
    intro he
    have hc := card_eq_one.mpr he
    omega
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨F,_,_,_,_,e,f,hf⟩ := hnat
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let l : L := ⟨a,hCL a.property⟩
  have hqne : q l ≠ 1 := by
    intro he
    have hl : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp he)
    exact ha (Subtype.ext (Subgroup.disjoint_def.mp hdis a.property
      (mem_map_of_mem L.subtype hl)))
  have hq3 : q l ^ 3 = 1 := by
    rw [← map_pow]
    have ha3 : a ^ 3 = 1 := hC ▸ pow_card_eq_one' (x := a)
    have hh : l ^ 3 = 1 := Subtype.ext (congrArg (fun x : C => (x : G)) ha3)
    rw [hh,map_one]
  apply eq_bot_iff.mpr
  intro v hv
  have hfixed : (q l).val.mulVec (f ⟨v,hv.1⟩).toAdd = (f ⟨v,hv.1⟩).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    have hh := hf l ⟨v,hv.1⟩
    change (f.symm (Multiplicative.ofAdd ((q l).val.mulVec (f ⟨v,hv.1⟩).toAdd)) : G) = _ at hh
    rw [hh]
    change (a : G) * v * (a : G)⁻¹ = (f.symm (f ⟨v,hv.1⟩) : G)
    rw [f.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv.2 a a.property)
  have hz := Matrix.SL2.odd_power_fixed_eq_zero (q l) 3 (by decide) hq3 hqne _ hfixed
  exact mem_bot.mpr (congrArg (fun z : V => (z : G))
    (f.injective (hz.trans f.map_one.symm)))

/-- The natural module contributes exactly n noncentral cubic factors. -/
theorem natural_cubic_length (hnat : IsNaturalModule L V n)
    (hC : Nat.card C = 3) (hCL : C ≤ L) :
    conjugationCubicLength C V = n := by
  unfold conjugationCubicLength
  rw [← inf_relIndex_right, inf_comm, natural_cubic_fixed_eq_bot hnat hC hCL,
    relIndex_bot_left,hnat.card,mul_comm n 2,pow_mul]
  exact Nat.log_pow (by decide : 1 < 4) n

private theorem natural_le_core (hnat : IsNaturalModule L V n)
    (hVT : V ≤ (T : Subgroup G)) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hC : Nat.card C = 3) (hCL : C ≤ L) : V ≤ L.pCoreIn 2 := by
  have hLV : L ≤ normalizer (V : Set G) := by
    obtain ⟨_,_,_,_,_,hm⟩ := hnat
    exact hm.normalizes
  have hVL : V ≤ L := by
    rcases hnat.invariant_subgroup (V ⊓ L) inf_le_left
      ((le_inf hLV L.le_normalizer).trans inf_normalizer_le_normalizer_inf) with hz | he
    · have hcomm : ⁅V,C⁆ = ⊥ := bot_unique (le_inf
        (le_normalizer_iff_commutator_le_left.mp (hCL.trans hLV))
        ((commutator_mono le_rfl hCL).trans
          (le_normalizer_iff_commutator_le_right.mp (hVT.trans hTL))) |>.trans hz.le)
      have hv : V = ⊥ := by
        apply bot_unique
        exact (le_inf le_rfl (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
          (natural_cubic_fixed_eq_bot hnat hC hCL).le
      exact hv ▸ bot_le
    · exact he.ge.trans inf_le_right
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hVT) hVL hLV

/-- The natural subgroup and the literal quotient Sylow contribute separately. -/
theorem natural_cubic_sylow_length_lower_bound (hnat : IsNaturalModule L V n)
    (hVT : V ≤ (T : Subgroup G)) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hC : Nat.card C = 3) (hCL : C ≤ L)
    (hCP : C ≤ normalizer (((T : Subgroup G) ⊓ L) : Set G)) :
    n + Nat.log 4 (2 ^ n) ≤ conjugationCubicLength C ((T : Subgroup G) ⊓ L) := by
  let R := (T : Subgroup G) ⊓ L
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnat
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hPR : (P : Subgroup L) = R.subgroupOf L := by
    rw [hP]
    ext x
    change (x : G) ∈ (T : Subgroup G) ↔ (x : G) ∈ (T : Subgroup G) ⊓ L
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hAP : C.subgroupOf L ≤ normalizer (P : Set L) := by
    change C.subgroupOf L ≤ normalizer ((P : Subgroup L) : Set L)
    rw [hPR]
    apply le_normalizer_iff.mpr
    intro a ha x hx
    have haC : (a : G) ∈ C := ha
    have hxR : (x : G) ∈ R := hx
    change (a : G) * (x : G) * (a : G)⁻¹ ∈ R
    exact (mem_normalizer_iff.mp (hCP haC) (x : G)).mp hxR
  have hc := CubicComparison.sl2_sylow_length q hq (hk.symm ▸ pCore_isPGroup) P
    (C.subgroupOf L) ((Nat.card_congr (subgroupOfEquivOfLe hCL).toEquiv).trans hC) hAP
  have hcore : (L.pCoreIn 2).subgroupOf L = pCore 2 L :=
    comap_map_eq_self_of_injective L.subtype_injective _
  rw [hPR,hk,← hcore,CubicComparison.length_subgroupOf C R L hCL inf_le_right,
    CubicComparison.length_subgroupOf C (L.pCoreIn 2) L hCL (pCoreIn_le 2 L),hF] at hc
  have hle := conjugationCubicLength_mono C (natural_le_core
    (show IsNaturalModule L V n from ⟨F,inferInstance,inferInstance,inferInstance,hF,e,f,hf⟩)
    hVT hTL hC hCL)
  rw [natural_cubic_length
    (show IsNaturalModule L V n from ⟨F,inferInstance,inferInstance,inferInstance,hF,e,f,hf⟩)
    hC hCL] at hle
  change conjugationCubicLength C ((T : Subgroup G) ⊓ L) = _ at hc
  omega
/-- For n>1, these contributions give the three factors required in 5.1.23. -/
theorem natural_cubic_sylow_length_ge_three (hnat : IsNaturalModule L V n)
    (hVT : V ≤ (T : Subgroup G)) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hn : 1 < n) (hC : Nat.card C = 3) (hCL : C ≤ L)
    (hCP : C ≤ normalizer (((T : Subgroup G) ⊓ L) : Set G)) :
    3 ≤ conjugationCubicLength C ((T : Subgroup G) ⊓ L) := by
  have hlow := natural_cubic_sylow_length_lower_bound hnat hVT hTL hC hCL hCP
  have hlog : 1 ≤ Nat.log 4 (2 ^ n) := Nat.le_log_of_pow_le (by decide)
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by omega))
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
