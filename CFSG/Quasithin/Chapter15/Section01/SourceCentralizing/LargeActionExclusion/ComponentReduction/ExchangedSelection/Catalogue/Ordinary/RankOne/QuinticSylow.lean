module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.QuinticAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.Cubic
public import Theory.GroupTheory.PermutingSupCard

/-!
# The permuting quintic actor in the original component quotient

The original actor Y satisfies SY = YS and does not centralize L. The actual
cubic-rank facts of the specified quotient make L normal in G₁. Conjugation
therefore sends SY into the automorphism group of the same quotient. Its
order divides a product of a power of two and a power of five. Faithfulness
of descent through the perfect central cover preserves Y's nontriviality,
and the two-group outer quotient makes its image inner. Pulling the entire
action image back through the injective inner map gives a genuine subgroup
of the model, containing its full marked Sylow and having order divisible
by five. The actual quotient map and central covers are retained throughout.

The Mathieu and binary-linear consumers discharge the model facts; this is
not a classification assumption. The remaining ordinary catalogue assembly
stays with qt-e-15122-ordinary-pre-exclusion, and its earlier source premises
with the producers retained by qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith 15.1.21(ii), 15.1.22, and the intrinsic component
normality argument of A.3.18, printed pp.1098--1100 and pp.51--52.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original permuting quintic actor supplies an actual Sylow overgroup
in the marked quotient, with five dividing its order and no other odd prime. -/
theorem PreExclusionSource.quintic_two_five_sylow_overgroup
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] (e : (d.L ⧸ pCore 2 d.L) ≃* X)
    (hf : Theory.SpecificGroups.BinaryComponentResidual.Facts X) :
    ∃ (P : Sylow 2 X) (H : Subgroup X) (a b : ℕ),
      (P : Subgroup X) ≤ H ∧ 5 ∣ Nat.card H ∧ Nat.card H ∣ 2^a * 5^b := by
  let : Finite X := Finite.of_equiv (d.L ⧸ pCore 2 d.L) e.toEquiv
  let := s.quasisimple
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center d.L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',
      ←(s.ordinary hL).center_eq]
  let c : PerfectCentralCovering.Cover d.L X := ⟨q,hq,inferInstance,hker.le⟩
  let N := normalizer (d.L : Set G)
  let f := (c.autMap hker).comp d.L.normalizerMonoidHom
  have hLN : d.G1 ≤ N := by
    have he := (d.source_cubic_component hG h
      (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e hf)).1
    change d.G1 ≤ normalizer (d.L : Set G)
    rw [he]
    have hh := (primeToResidual 3 d.G1).le_normalizer_map d.G1.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  obtain ⟨Y,hY,hYN,hYn⟩ := s.rankOne_prime_actor_noncentral (h := h) hG hM hJ
  let U := d.S ⊔ Y
  have hUN : U ≤ N := sup_le (d.S_le_G1.trans hLN) hYN
  let A := (U.subgroupOf N).map f
  let B := (Y.subgroupOf N).map f
  have hB : IsPGroup 5 B :=
    (hY.prime_group.of_equiv (subgroupOfEquivOfLe hYN).symm).map f
  have hBne : B ≠ ⊥ := by
    intro he
    apply hYn
    intro y hy l hl
    have hh : f ⟨y,hYN hy⟩ = 1 := mem_bot.mp (he ▸ mem_map_of_mem f hy)
    have hh' : d.L.normalizerMonoidHom ⟨y,hYN hy⟩ = 1 :=
      (c.autMap_injective hker) (hh.trans (map_one (c.autMap hker)).symm)
    have ha := congrArg Subtype.val (DFunLike.congr_fun hh' (⟨l,hl⟩ : d.L))
    change y*l*y⁻¹=l at ha
    exact (mul_inv_eq_iff_eq_mul.mp ha).symm
  have hBI : B ≤ MulAut.innerSubgroup X := by
    let r := QuotientGroup.mk' (MulAut.innerSubgroup X)
    intro b hb
    apply (QuotientGroup.eq_one_iff _).mp
    obtain ⟨i,hi⟩ := hB ⟨b,hb⟩
    obtain ⟨j,hj⟩ := hf.2.2 (r b)
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 5 2).pow i j)
    · apply orderOf_dvd_of_pow_eq_one
      change (r b)^(5^i)=1
      rw [←map_pow,show b^(5^i)=1 from congrArg Subtype.val hi,map_one]
    · exact orderOf_dvd_of_pow_eq_one hj
  let k : X →* MulAut X := MulAut.conj
  have hki : Function.Injective k := conj_injective_of_center_eq_bot hf.1
  let H := A.comap k
  have hHA : H.map k ≤ A := map_comap_le k A
  have hBH : B ≤ H.map k := by
    rw [map_comap_eq]
    exact le_inf hBI (map_mono (comap_mono le_sup_right))
  have hfive : 5 ∣ Nat.card H := by
    have hh := (hB.card_eq_or_dvd.resolve_left (fun he => hBne (card_eq_one.mp he))).trans
      (card_dvd_of_le hBH)
    rwa [card_map_of_injective hki] at hh
  obtain ⟨P,hP⟩ := s.component_sylow
  let Q := P.mapSurjective (f := q) hq
  have hQH : (Q : Subgroup X) ≤ H := by
    rintro x ⟨l,hl,rfl⟩
    let ln : N := ⟨l,d.L.le_normalizer l.property⟩
    have hlS : (l : G) ∈ d.S := by
      have hh := hP ▸ mem_map_of_mem d.L.subtype hl
      exact hh.1
    have hfx : f ln = MulAut.conj (q l) := by
      ext z
      obtain ⟨w,rfl⟩ := hq z
      change c.autMap hker (d.L.normalizerMonoidHom ln) (q w) = _
      rw [c.autMap_apply hker]
      change q (l*w*l⁻¹)=_
      simp only [map_mul,map_inv,MulAut.conj_apply]
    change k (q l) ∈ A
    rw [←hfx]
    exact mem_map_of_mem f (show ln ∈ U.subgroupOf N from mem_sup_left hlS)
  have hS : IsPGroup 2 d.S := T.isPGroup'.to_le d.S_le_T
  obtain ⟨a,ha⟩ := hS.exists_card_eq
  obtain ⟨b,hb⟩ := hY.prime_group.exists_card_eq
  have hd : Disjoint d.S Y := disjoint_of_coprime_natCard (by
    rw [ha,hb]
    exact (by decide : Nat.Coprime 2 5).pow a b)
  have hUcard : Nat.card U = 2^a * 5^b := by
    rw [show U = d.S ⊔ Y from rfl,card_sup_eq_mul_of_permutes_of_disjoint _ _ hY.permutes hd,ha,hb]
  have hHAcard : Nat.card H ∣ Nat.card A := by
    have hh := card_dvd_of_le hHA
    rwa [card_map_of_injective hki] at hh
  have hAUcard : Nat.card A ∣ Nat.card U := by
    have hh := (U.subgroupOf N).card_map_dvd f
    rwa [Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv] at hh
  exact ⟨Q,H,a,b,hQH,hfive,hUcard ▸ hHAcard.trans hAUcard⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
