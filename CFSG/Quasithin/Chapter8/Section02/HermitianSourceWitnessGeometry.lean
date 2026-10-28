module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessSelection
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionCores
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionFF
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSolvableSelection

/-!
# Geometric selection from the original Hermitian witnesses

The original marked rank-one witness is transported into the ambient subgroup
lattice with its internal conjugator, Sylow intersection and full-core quotient.
The same quotient equivalence carries the Borel marking. Native two-conjugate
results identify the two-core and descend characteristic two. The literal
non-FF action excludes a trivial intersection; TI then identifies the relative
normalizer, and the concrete Borel geometry marks the Sylow center and its rank.

`GeometricSelected` records these proved geometric clauses without asserting
that the model degree divides the ambient E-generation parameter. The existing
`Selected` interface is preserved: conversion explicitly requires that extra
numerical statement. The core actor nevertheless has corank equal to the actual
model degree and bounds the original weak-closure parameter above. The companion
rank extension supplies a geometric upper bound instead of numerical divisibility.

The proof adapters below reuse the native two-conjugate results underlying the
older family-based proofs; they do not use a quotient-model generation rule.
The Chapter 12 consumer constructs this selection on the literal chosen orbit.
The torus exclusion on this interface and the field-four normalizer/centralizer
argument remain obligations of the full Hermitian exclusion.

Source: Aschbacher--Smith E.2.9--14 and 8.2.2--3, printed pp.221--228,714--716,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open Witnesses Witnesses.BenderPlacement
variable {G : Type*} [Group G] [Finite G]

@[expose] public section
/-- The actual rank-one pair before any assertion about the ambient
E-generation parameter. All quotient models retain their Borel markings. -/
structure GeometricFamily (H T M V I : Subgroup G) (k : ℕ) : Prop where
  elementary : IsElementaryAbelian 2 V
  nontrivial : V ≠ ⊥
  le_sylow : V ≤ T
  le_ambient : I ≤ H
  generate : ∃ x ∈ I, V ⊔ V.map (MulAut.conj x⁻¹).toMonoidHom = I
  sylow : ∃ S : Sylow 2 I, (S : Subgroup I) = T.subgroupOf I
  core_two_closed : IsTwoClosed (localCore M I)
  classified : RankOneAlternative (Star M I) (starImage M I M) k

/-- Geometric selection on the original action, independent of the ambient
E-generation parameter. The source quotient, center and Sylow are literal. -/
structure GeometricSelected (H T M V I : Subgroup G) [IsElementaryAbelian 2 V]
    (k : ℕ) (i : I) (S : Sylow 2 I) : Prop where
  family : GeometricFamily H T M V I k
  generate : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I
  sylow_eq : (S : Subgroup I) = T.subgroupOf I
  twoConjugate : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹
  core_eq : localCore M I = pCore 2 I
  characteristic_two : generalizedFitting I = pCore 2 I
  intersection_ne_bot : V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ≠ ⊥
  intersection_central : V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ≤
    (center I).map I.subtype
  local_normalizer : I ⊓ normalizer (V : Set G) ≤ M
  normalizer_eq : M ⊓ I = I ⊓ normalizer (V : Set G)
  positive : 0 < k
  models : RankOneAlternative (I ⧸ pCore 2 I) (coreImage I M) k
  center_eq : coreImage I V = embeddedCenter (coreImage I T)
  borel_eq : coreImage I M = normalizer (coreImage I T : Set (I ⧸ pCore 2 I))
  rank_eq : rank (coreImage I V) = k
  quadraticRatio_gt_one : 1 < quadraticRatio
    ((automizerRepresentation V).comp (inducedAutomizer V I).subtype)
end

private theorem GeometricFamily.twoConjugate {K : GroupClass} {H T M V I : Subgroup G} {k : ℕ}
    (h : HypothesisE28 K H T M V) (f : GeometricFamily H T M V I k)
    (S : Sylow 2 I) (hS : (S : Subgroup I) = T.subgroupOf I)
    (i : I) (hi : V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I) :
    TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹ := by
  let := h.elementary
  have hVI : V ≤ I := hi ▸ le_sup_left
  have hVH := hVI.trans f.le_ambient
  have hNI : I ⊓ normalizer (V : Set G) ≤ M :=
    (inf_le_inf_right _ f.le_ambient).trans h.normalizer_le
  have hlocal : V.subgroupOf H ≤ (M.subgroupOf H).pCoreIn 2 := by
    intro v hv
    obtain ⟨x, hx, he⟩ := h.le_local_core hv
    refine ⟨x, hx, ?_⟩
    exact Subtype.ext he
  have hVM : V ≤ M := by
    intro v hv
    exact (pCoreIn_le 2 (M.subgroupOf H)) (hlocal (show (⟨v, hVH hv⟩ : H) ∈ V.subgroupOf H from hv))
  have hcore : V.subgroupOf I ≤ (pCore 2 (M.subgroupOf I)).map (M.subgroupOf I).subtype := by
    let j : M.subgroupOf I →* M.subgroupOf H :=
      { toFun := fun x => ⟨⟨x.val.val, f.le_ambient x.val.property⟩, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.val) he))
    have hc : (pCore 2 (M.subgroupOf H)).comap j ≤ pCore 2 (M.subgroupOf I) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective j hj⟩
    intro v hv
    refine ⟨⟨v, hVM hv⟩, hc ?_, rfl⟩
    obtain ⟨x, hx, he⟩ := hlocal (show (⟨v.val, f.le_ambient v.property⟩ : H) ∈ V.subgroupOf H from hv)
    have he' : j ⟨v, hVM hv⟩ = x := Subtype.ext he.symm
    change j ⟨v, hVM hv⟩ ∈ pCore 2 (M.subgroupOf H)
    rwa [he']
  refine ⟨IsElementaryAbelian.subgroupOf hVI, ?_, ?_, ?_, hcore, f.core_two_closed, ?_⟩
  · rw [hS]
    exact comap_mono h.le_sylow
  · have hVS : V.subgroupOf I ≤ (S : Subgroup I) := by
      rw [hS]
      exact comap_mono h.le_sylow
    apply (normal_subgroupOf_iff_le_normalizer hVS).mpr
    rw [hS, ← subgroupOf_normalizer_eq hVI]
    exact comap_mono ((normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow)
  · rw [← subgroupOf_normalizer_eq hVI]
    intro x hx
    exact hNI ⟨x.property, hx⟩
  · apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hVI, restricted_right_conjugate_image I V hVI i,
      hi, ← MonoidHom.range_eq_map, range_subtype]


private theorem geometric_family_characteristic_two {K : GroupClass} {H T M V I : Subgroup G} {k : ℕ}
    (h : HypothesisE28 K H T M V) (f : GeometricFamily H T M V I k)
    (hfit : generalizedFitting H = pCore 2 H) :
    generalizedFitting I = pCore 2 I := by
  obtain ⟨S,hS,hP,hM⟩ := h.minimal
  obtain ⟨x,hx,hgen⟩ := f.generate
  have hVI : V ≤ I := hgen ▸ le_sup_left
  have hVH : V ≤ H := hVI.trans f.le_ambient
  let xH : H := ⟨x,f.le_ambient hx⟩
  have hgenH : V.subgroupOf H ⊔ (V.subgroupOf H).map
      (MulAut.conj xH⁻¹).toMonoidHom = I.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVH,
      restricted_right_conjugate_image H V hVH xH,
      map_subgroupOf_eq_of_le f.le_ambient,hgen]
  have hSN : (S : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H) := by
    rw [hS,←subgroupOf_normalizer_eq hVH]
    exact comap_mono ((normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow)
  have hn : pCore 2 H ≤ normalizer (I.subgroupOf H : Set H) := by
    rw [←hgenH]
    exact twoCore_le_normalizer_conjugate_join S (V.subgroupOf H) hSN xH⁻¹
  have hh := generalizedFitting_eq_pCore_of_normalized_by_pCore (I.subgroupOf H) hfit hn
  let e := subgroupOfEquivOfLe f.le_ambient
  have he := congrArg (Subgroup.map e.toMonoidHom) hh
  rwa [map_generalizedFitting_equiv,pCore_map_iso] at he


private theorem geometric_family_rank_one_core {K : GroupClass} {H T M V I : Subgroup G} {k : ℕ}
    (h : HypothesisE28 K H T M V) (f : GeometricFamily H T M V I k)
    (hr : RankOneAlternative (Star M I) (starImage M I M) k) :
    localCore M I = pCore 2 I := by
  let := h.elementary
  obtain ⟨x,hx,hgen⟩ := f.generate
  let i : I := ⟨x,hx⟩
  obtain ⟨S,hS⟩ := f.sylow
  have hp := GeometricFamily.twoConjugate h f S hS i hgen
  let := hp.elementary
  rcases hr with ⟨hk,e,_⟩ | ⟨m,hm,_,e,_⟩ | ⟨_,p,a,hpprime,ho,_,⟨e⟩⟩
  · exact hp.J_eq_twoCore_of_linear_two k (by omega)
      (GaloisField.card 2 k (by omega))
      (e.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm)
  · exact suzuki_core hp m hm e
  · have hproper : V.subgroupOf I ≠ ⊤ := by
      intro he
      have hn : M.subgroupOf I = ⊤ := by
        apply top_unique
        simpa only [he,normalizer_eq_top] using hp.normalizer_le
      have hc : Nat.card (Star M I) = 1 := by
        change Nat.card (I ⧸ (M.subgroupOf I).normalCore) = 1
        rw [hn,normalCore_eq_self]
        simp
      rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at hc
      omega
    have hcard : Nat.card ((V.subgroupOf I).map
        (QuotientGroup.mk' (localCore M I))) = 2 := by
      let E := (V.subgroupOf I).map (QuotientGroup.mk' (localCore M I))
      have hEp : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf I)).map _
      have hne : E ≠ ⊥ := by
        intro he
        have hv : V.subgroupOf I ≤ localCore M I := by
          simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
        exact hp.V_not_le_twoCore hproper
          (hp.le_twoCore_of_le_J _ (IsElementaryAbelian.isPGroup 2 _) hv)
      have hd : Nat.card E ∣ 2*p^a := by
        have hh := E.card_subgroup_dvd_card
        rwa [Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at hh
      obtain ⟨b,hb⟩ := hEp.exists_card_eq
      have hcop : Nat.Coprime (Nat.card E) (p^a) := by
        rw [hb]
        exact ho.coprime_two_left.pow b a
      exact ((Nat.dvd_prime Nat.prime_two).mp
        (hcop.dvd_of_dvd_mul_right hd)).resolve_left (fun he => hne (Subgroup.card_eq_one.mp he))
    exact (hp.odd_dihedral hcard).2.1.symm


private theorem geometric_family_borel_normalizes {K : GroupClass} {H T M V I : Subgroup G} {k : ℕ}
    [IsElementaryAbelian 2 V]
    (h : HypothesisE28 K H T M V) (f : GeometricFamily H T M V I k)
    (hr : RankOneAlternative (Star M I) (starImage M I M) k)
    (i : I) (hgen : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I)
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hZ : V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ≠ ⊥) :
    starImage M I M ≤ normalizer (starImage M I T : Set (Star M I)) := by
  obtain ⟨S,hS⟩ := f.sylow
  have hp := GeometricFamily.twoConjugate h f S hS i hgen
  let := hp.elementary
  let q := QuotientGroup.mk' (localCore M I)
  let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hR : (R : Subgroup (Star M I)) = starImage M I T := by
    change (S : Subgroup I).map q = _
    rw [hS]
    rfl
  have hRM : (R : Subgroup (Star M I)) ≤ starImage M I M :=
    map_mono (hp.sylow_le_normalizer.trans hp.normalizer_le)
  rw [←hR]
  rcases hr with ⟨hk,e,he⟩ | ⟨m,hm,_,e,he⟩ | ⟨_,p,a,hpprime,ho,_,⟨e⟩⟩
  · let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
    have hR'M : (R' : Subgroup _) ≤ PBorel (BinaryGaloisField k) :=
      (map_mono (f := e.toMonoidHom) hRM).trans_eq he
    have hn := (selectionModelSources.psl2 k hk R' hR'M).1
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_equiv_normalizer_eq,he]
    exact hn.le
  · let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
    have hR'M : (R' : Subgroup _) ≤ SuzukiBorelSubgroup m :=
      (map_mono (f := e.toMonoidHom) hRM).trans_eq he
    have hn := (selectionModelSources.suzuki m hm R' hR'M).1
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_equiv_normalizer_eq,he]
    exact hn.le
  · have hVI : V ≤ I := hgen ▸ le_sup_left
    have hn := relative_normalizer I M V i.val hgen hTI hNV hZ
    have hMN : M.subgroupOf I ≤ normalizer (V.subgroupOf I : Set I) := by
      rw [←subgroupOf_normalizer_eq hVI]
      intro x hx
      exact (hn.le ⟨hx,x.property⟩).2
    let E := starImage M I V
    have hEN : starImage M I M ≤ normalizer (E : Set (Star M I)) :=
      (map_mono (f := q) hMN).trans ((V.subgroupOf I).le_normalizer_map q)
    have hproper : V.subgroupOf I ≠ ⊤ := by
      intro he
      have hM : M.subgroupOf I = ⊤ := by
        apply top_unique
        simpa only [he,normalizer_eq_top] using hp.normalizer_le
      have hc : Nat.card (Star M I) = 1 := by
        change Nat.card (I ⧸ (M.subgroupOf I).normalCore) = 1
        rw [hM,normalCore_eq_self]
        simp
      rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at hc
      omega
    have hne : E ≠ ⊥ := by
      intro he
      have hv : V.subgroupOf I ≤ localCore M I := by
        simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
      exact hp.V_not_le_twoCore hproper
        (hp.le_twoCore_of_le_J _ (IsElementaryAbelian.isPGroup 2 _) hv)
    have heq := odd_dihedral_two_subgroup_normalizer (p^a) ho.pow e E
      ((IsElementaryAbelian.isPGroup 2 (V.subgroupOf I)).map q) hne
    have hER : E ≤ (R : Subgroup (Star M I)) := map_mono hp.le_sylow
    exact (hEN.trans_eq heq).trans (hER.trans (Subgroup.le_normalizer (H := (R : Subgroup (Star M I)))))


private theorem geometric_family_actor_dimension {K : GroupClass} {H T M V I : Subgroup G} {k : ℕ}
    (h : HypothesisE28 K H T M V) (f : GeometricFamily H T M V I k)
    (hfit : generalizedFitting H = pCore 2 H)
    (S : Sylow 2 I) (hS : (S : Subgroup I) = T.subgroupOf I)
    (i : I) (hgen : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I) :
    V.subgroupOf I ≠ ⊤ ∧ ∃ d : ℕ,
      Nat.card (starImage M I V) ≤ 2^d ∧
      d ≤ Nat.log 2 ((TwoConjugate.Z (V.subgroupOf I) i⁻¹).relIndex
        (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)) := by
  have hp := GeometricFamily.twoConjugate h f S hS i hgen
  have hfitI := geometric_family_characteristic_two h f hfit
  let := hp.elementary
  rcases f.classified with ⟨hk,e,_⟩ | ⟨m,hm,_,e,_⟩ | ⟨_,p,a,hpprime,ho,_,⟨e⟩⟩
  · have hproper := pair_proper_of_model hp e
    let ξ := e.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm
    have hcard := GaloisField.card 2 k (by omega)
    exact ⟨hproper,k,hp.star_card_le_linear_two k hcard ξ,
      hp.actor_rank_ge_linear_two_star hproper hfitI k (by omega) hcard ξ⟩
  · let : Fact (0 < m) := ⟨hm⟩
    have hproper := pair_proper_of_model hp e
    refine ⟨hproper,2*m+1,hp.star_card_le_suzuki m hm e,?_⟩
    have hd := hp.actor_rank_ge_suzuki hfitI m (by omega) e
    omega
  · have hproper := pair_proper_of_model hp e
    let E := starImage M I V
    have hEp : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf I)).map _
    have hne : E ≠ ⊥ := by
      intro he
      have hv : V.subgroupOf I ≤ localCore M I := by
        simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
      exact hp.V_not_le_twoCore hproper
        (hp.le_twoCore_of_le_J _ (IsElementaryAbelian.isPGroup 2 _) hv)
    have hd : Nat.card E ∣ 2*p^a := by
      have hh := E.card_subgroup_dvd_card
      rwa [Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at hh
    obtain ⟨b,hb⟩ := hEp.exists_card_eq
    have hcop : Nat.Coprime (Nat.card E) (p^a) := by
      rw [hb]
      exact ho.coprime_two_left.pow b a
    have hc : Nat.card E = 2 := ((Nat.dvd_prime Nat.prime_two).mp
      (hcop.dvd_of_dvd_mul_right hd)).resolve_left (fun he => hne (Subgroup.card_eq_one.mp he))
    exact ⟨hproper,1,by simpa only [pow_one] using hc.le,hp.actor_rank_pos hproper hfitI⟩

private theorem geometric_family_quadraticRatio_le_one_of_intersection_eq_bot
    {K : GroupClass} {H T M V I : Subgroup G} [IsElementaryAbelian 2 V] {k : ℕ}
    (h : HypothesisE28 K H T M V) (hfit : generalizedFitting H = pCore 2 H)
    (f : GeometricFamily H T M V I k) (i : I)
    (hgen : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I)
    (hz : V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom = ⊥) :
    quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V H).subtype) ≤ 1 := by
  obtain ⟨S,hS⟩ := f.sylow
  have hp := GeometricFamily.twoConjugate h f S hS i hgen
  obtain ⟨hproper,d,hstar,hd⟩ := geometric_family_actor_dimension h f hfit S hS i hgen
  have hVI : V ≤ I := hgen ▸ le_sup_left
  have hz' : TwoConjugate.Z (V.subgroupOf I) i⁻¹ = ⊥ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [selected_intersection_image I V hVI i,hz,Subgroup.map_bot]
  have hST : (S : Subgroup I).map I.subtype ≤ T := by
    rw [hS]
    exact map_comap_le _ _
  have hTN : T ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow
  let a := DihedralCubic.actorIn hp (hST.trans hTN)
  let ψ : TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹ →*
      inducedAutomizer V H :=
    (V.normalizerMonoidHom.rangeRestrict.comp a).codRestrict (inducedAutomizer V H)
      (fun x => mem_map_of_mem _ (h.le_ambient (hST
        (mem_map_of_mem I.subtype (DihedralCubic.A_le_sylow hp x.property)))))
  let ρ := (automizerRepresentation V).comp (inducedAutomizer V H).subtype
  let e := subgroupOfEquivOfLe hVI
  have hρ : Function.Injective ρ := (automizerRepresentation_injective V).comp
    (inducedAutomizer V H).subtype_injective
  have ha : ∀ (x : TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
      (v : V.subgroupOf I),
      (e.symm (ρ (ψ x) (Additive.ofMul (e v))).toMul : I) =
        (x : I) * v * (x : I)⁻¹ := by
    intro x v
    apply Subtype.ext
    rfl
  exact (hp.offender_of_P_elementary_and_star_dimension hproper
    (geometric_family_characteristic_two h f hfit) (hp.P_elementary_of_Z_eq_bot hz')
    e ρ hρ ψ ha d hstar hd).2


private theorem geometric_family_intersection_ne_bot_of_quadraticRatio_gt_one
    {K : GroupClass} {H T M V I : Subgroup G} [IsElementaryAbelian 2 V] {k : ℕ}
    (h : HypothesisE28 K H T M V) (hfit : generalizedFitting H = pCore 2 H)
    (f : GeometricFamily H T M V I k) (i : I)
    (hgen : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I)
    (hq : 1 < quadraticRatio
      ((automizerRepresentation V).comp (inducedAutomizer V H).subtype)) :
    V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ≠ ⊥ := by
  intro hz
  exact (not_le_of_gt hq)
    (geometric_family_quadraticRatio_le_one_of_intersection_eq_bot h hfit f i hgen hz)


private theorem geometric_family_rank_one_center {K : GroupClass} {H T M V I : Subgroup G} {k : ℕ}
    [IsElementaryAbelian 2 V]
    (h : HypothesisE28 K H T M V) (hfit : generalizedFitting H = pCore 2 H)
    (f : GeometricFamily H T M V I k)
    (hr : RankOneAlternative (Star M I) (starImage M I M) k)
    (i : I) (hgen : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I)
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hZ : V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ≠ ⊥) :
    starImage M I V = embeddedCenter (starImage M I T) := by
  obtain ⟨S,hS⟩ := f.sylow
  have hp := GeometricFamily.twoConjugate h f S hS i hgen
  let := hp.elementary
  let q := QuotientGroup.mk' (localCore M I)
  let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hR : (R : Subgroup (Star M I)) = starImage M I T := by
    change (S : Subgroup I).map q = _
    rw [hS]
    rfl
  have hRM : (R : Subgroup (Star M I)) ≤ starImage M I M :=
    map_mono (hp.sylow_le_normalizer.trans hp.normalizer_le)
  have hMN := geometric_family_borel_normalizes h f hr i hgen hTI hNV hZ
  rw [←hR] at hMN
  have hmark := (RankOneAlternative.sylow_marking selectionModelSources hr R hRM hMN).1
  have hVI : V ≤ I := hgen ▸ le_sup_left
  have hn := relative_normalizer I M V i.val hgen hTI hNV hZ
  have hMV : M.subgroupOf I ≤ normalizer (V.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hVI]
    intro x hx
    exact (hn.le ⟨hx,x.property⟩).2
  have hEV : starImage M I M ≤ normalizer (starImage M I V : Set (Star M I)) :=
    (map_mono (f := q) hMV).trans ((V.subgroupOf I).le_normalizer_map q)
  have hproper := (geometric_family_actor_dimension h f hfit S hS i hgen).1
  have hne : starImage M I V ≠ ⊥ := by
    intro he
    have hv : V.subgroupOf I ≤ localCore M I := by
      simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
    exact hp.V_not_le_twoCore hproper
      (hp.le_twoCore_of_le_J _ (IsElementaryAbelian.isPGroup 2 _) hv)
  let : IsElementaryAbelian 2 (starImage M I V) := IsElementaryAbelian.map q
  rw [←hR]
  exact rank_one_elementary_eq_center hr R (starImage M I V)
    (map_mono hp.le_sylow) hne (hmark ▸ hEV)


theorem exists_geometric_selected_of_family
    {K : GroupClass} {H T M V I : Subgroup G} [IsElementaryAbelian 2 V] {k : ℕ}
    (h : HypothesisE28 K H T M V) (hchar : generalizedFitting H = pCore 2 H)
    (f : GeometricFamily H T M V I k)
    (hr : RankOneAlternative (Star M I) (starImage M I M) k)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (i : I) (S : Sylow 2 I), GeometricSelected H T M V I k i S := by
  obtain ⟨x,hx,hgen⟩ := f.generate
  let i : I := ⟨x,hx⟩
  obtain ⟨S,hS⟩ := f.sylow
  have hNI : I ⊓ normalizer (V : Set G) ≤ M :=
    (inf_le_inf_right _ f.le_ambient).trans h.normalizer_le
  have hqH := selected_quadraticRatio_gt_one M H V h.normalizer_le hq
  have hZ := geometric_family_intersection_ne_bot_of_quadraticRatio_gt_one h hchar f i hgen hqH
  have hc := geometric_family_rank_one_core h f hr
  have hmodel := hr.map (coreQuotientEquiv M I hc)
  rw [starImage_map_coreQuotientEquiv] at hmodel
  have hz := geometric_family_rank_one_center h hchar f hr i hgen hTI hNV hZ
  obtain ⟨hzcore,hncore⟩ := core_markings_of_star M I T V hc hz
    (geometric_family_borel_normalizes h f hr i hgen hTI hNV hZ)
  have hTM : T ≤ M := by
    obtain ⟨R,hR,hP,hM⟩ := h.minimal
    intro t ht
    have htm := (ChapterB.minimalParabolicMax_spec R hP).2
    rw [hR,←hM] at htm
    exact htm (show (⟨t,h.le_ambient ht⟩ : H) ∈ T.subgroupOf H from ht)
  obtain ⟨hnorm,hrank⟩ := selected_model_markings selectionModelSources M I T V k S hS hTM hmodel hzcore hncore
  refine ⟨i,S,f,hgen,hS,GeometricFamily.twoConjugate h f S hS i hgen,hc,
    geometric_family_characteristic_two h f hchar,hZ,?_,hNI,?_,hr.models.1,
    hmodel,hzcore,hnorm,hrank,selected_quadraticRatio_gt_one M I V hNI hq⟩
  · exact intersection_central I V i.val hgen
  · exact relative_normalizer I M V i.val hgen hTI hNV hZ


private theorem quotientModel_rank_one {X : Type*} [Group X]
    {A : Subgroup X} {k : ℕ} (w : QuotientModel A k) :
    RankOneAlternative (X ⧸ A.normalCore) (A.map (QuotientGroup.mk' A.normalCore)) k := by
  cases w with
  | dihedral hd p a hp hp2 ha e =>
    exact Or.inr (Or.inr ⟨hd,p,a,hp,hp.odd_of_ne_two hp2,ha,⟨e⟩⟩)
  | linear hk e hb =>
    refine Or.inl ⟨hk,e.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)),?_⟩
    change (A.map (QuotientGroup.mk' A.normalCore)).map
      ((Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).toMonoidHom.comp e.toMonoidHom) = _
    rw [←map_map,hb]
    have hB : Matrix.SpecialLinearGroup.rankOneBorel (BinaryGaloisField k) =
        Borel (BinaryGaloisField k) := by
      ext g
      exact (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff g).trans (mem_Borel_iff g).symm
    rw [hB,PBorel_eq_map]
    rfl
  | suzuki m hm hd e hb =>
    obtain ⟨c,hc⟩ := hb
    refine Or.inr (Or.inl ⟨m,hm,hd,e.trans (MulAut.conj c⁻¹),?_⟩)
    change (A.map (QuotientGroup.mk' A.normalCore)).map
      ((MulAut.conj c⁻¹).toMonoidHom.comp e.toMonoidHom) = _
    rw [←map_map,hc,map_map]
    have he : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id (SuzukiMatrixGroup m) := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]

/-- Transport the actual witness into the original ambient group. The same
quotient equivalence transports its Borel; no ambient parameter is inferred. -/
theorem geometric_family_of_original_witness
    {H T M V : Subgroup G} (hVH : V ≤ H)
    (hV : IsElementaryAbelian 2 V) (hne : V ≠ ⊥) (hVT : V ≤ T)
    (R : Sylow 2 H) (hR : (R : Subgroup H) = T.subgroupOf H)
    {n : ℕ} (w : OriginalWitness R (M.subgroupOf H) (V.subgroupOf H) n) :
    ∃ I : Subgroup G, GeometricFamily H T M V I w.degree := by
  let J := w.pair.subgroup
  let I := J.map H.subtype
  let e : J ≃* I := J.equivMapOfInjective H.subtype H.subtype_injective
  let A := (M.subgroupOf H).subgroupOf J
  have hA : (M.subgroupOf I).comap e.toMonoidHom = A := by ext x; rfl
  have hC : (localCore M I).comap e.toMonoidHom = A.normalCore := by
    rw [←normalCore_comap_of_surjective e.toMonoidHom e.surjective,hA]
  have hCm : A.normalCore.map e.toMonoidHom = localCore M I := by
    rw [←hC,map_comap_eq,MonoidHom.range_eq_top.mpr e.surjective,top_inf_eq]
  let ec : A.normalCore ≃* localCore M I :=
    (e.subgroupMap A.normalCore).trans (MulEquiv.subgroupCongr hCm)
  have hclosed : IsTwoClosed (localCore M I) := by
    obtain ⟨P,hP⟩ := w.pair.core_two_closed
    let := hP
    refine ⟨P.mapSurjective (f := ec.toMonoidHom) ec.surjective,?_⟩
    exact Normal.map hP ec.toMonoidHom ec.surjective
  let eqt : (J ⧸ A.normalCore) ≃* Star M I :=
    QuotientGroup.equivOfSurjectiveComap e.toMonoidHom e.surjective _ _ hC
  have hAm : A.map e.toMonoidHom = M.subgroupOf I := by
    rw [←hA,map_comap_eq_self_of_surjective e.surjective]
  have hmark : (A.map (QuotientGroup.mk' A.normalCore)).map eqt.toMonoidHom =
      starImage M I M := by
    rw [map_map]
    have he : eqt.toMonoidHom.comp (QuotientGroup.mk' A.normalCore) =
        (QuotientGroup.mk' (localCore M I)).comp e.toMonoidHom := by
      ext x
      rfl
    rw [he,←map_map,hAm]
    rfl
  have hr := (quotientModel_rank_one w.model).map eqt
  rw [hmark] at hr
  have hgen : V ⊔ V.map (MulAut.conj w.pair.conjugator.val.val).toMonoidHom = I := by
    have hh := congrArg (fun B : Subgroup J => B.map (H.subtype.comp J.subtype)) w.pair.generate
    rw [map_pair] at hh
    have hm : ((V.subgroupOf H).subgroupOf J).map (H.subtype.comp J.subtype) = V := by
      rw [←map_map,map_subgroupOf_eq_of_le w.pair.le,map_subgroupOf_eq_of_le hVH]
    rw [hm,←MonoidHom.range_eq_map,MonoidHom.range_comp,J.range_subtype] at hh
    exact hh
  let S := w.pair.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS : (S : Subgroup I) = T.subgroupOf I := by
    apply map_injective I.subtype_injective
    change ((w.pair.sylow : Subgroup J).map e.toMonoidHom).map I.subtype = _
    rw [map_map]
    have hf : I.subtype.comp e.toMonoidHom = H.subtype.comp J.subtype := rfl
    rw [hf,←map_map,w.pair.sylow_eq,hR,map_inf _ _ _ H.subtype_injective,
      subgroupOf_map_subtype,subgroupOf_map_subtype]
    change (T ⊓ H) ⊓ I = T ⊓ I
    rw [inf_assoc,inf_eq_right.mpr (map_subtype_le J)]
  refine ⟨I,hV,hne,hVT,map_subtype_le J,?_,⟨S,hS⟩,hclosed,hr⟩
  refine ⟨w.pair.conjugator.val.val⁻¹,?_,?_⟩
  · exact I.inv_mem (mem_map_of_mem H.subtype w.pair.conjugator.property)
  · simpa only [inv_inv] using hgen

/-- An original marked witness gives every geometric clause of selection
on the same action, with its actual degree and without degree divisibility. -/
theorem geometric_selected_of_original_witness
    {K : GroupClass} {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 K H T M V) (hfit : generalizedFitting H = pCore 2 H)
    (R : Sylow 2 H) (hR : (R : Subgroup H) = T.subgroupOf H)
    {n : ℕ} (w : OriginalWitness R (M.subgroupOf H) (V.subgroupOf H) n)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      GeometricSelected H T M V I w.degree i S := by
  obtain ⟨I,f⟩ := geometric_family_of_original_witness (h.le_sylow.trans h.le_ambient)
    h.elementary (by intro he; exact h.outside_core (he ▸ bot_le)) h.le_sylow R hR w
  obtain ⟨i,S,s⟩ := exists_geometric_selected_of_family h hfit f f.classified hq hTI hNV
  exact ⟨I,i,S,s⟩

/-- Compatibility with the existing selected-family API. Its numerical
premise remains explicit, so geometric selection never asserts it implicitly. -/
theorem GeometricSelected.toSelected
    {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
    {k : ℕ} {i : I} {S : Sylow 2 I}
    (s : GeometricSelected H T M V I k i S) (hd : k ∣ generationParameter H) :
    Selected H T M V I k i S := by
  let f := s.family
  exact ⟨⟨f.elementary,f.nontrivial,f.le_sylow,f.le_ambient,f.generate,f.sylow,
    f.core_two_closed,Or.inl f.classified,hd⟩,s.generate,s.sylow_eq,s.twoConjugate,
    s.core_eq,s.characteristic_two,s.intersection_ne_bot,s.intersection_central,
    s.local_normalizer,s.normalizer_eq,s.positive,hd,s.models,s.center_eq,s.borel_eq,
    s.rank_eq,s.quadraticRatio_gt_one⟩

variable {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

omit [Finite G] in
private theorem geometric_generator_proper
    (s : GeometricSelected H T M V I k i S) : V.subgroupOf I ≠ ⊤ := by
  intro he
  have hS : (S : Subgroup I) = ⊤ := top_unique (he ▸ s.twoConjugate.le_sylow)
  have hp : IsPGroup 2 (⊤ : Subgroup I) := hS ▸ S.isPGroup'
  have hc : pCore 2 I = ⊤ := top_unique (le_sSup ⟨inferInstance, hp⟩)
  have hq : coreImage I V = ⊥ := by
    apply bot_unique
    rintro _ ⟨v, hv, rfl⟩
    change QuotientGroup.mk' (pCore 2 I) v = 1
    apply (QuotientGroup.eq_one_iff v).mpr
    rw [hc]
    exact mem_top _
  have hr := s.rank_eq
  rw [hq, Representation.BinaryOffender.rank_bot] at hr
  have hk := s.positive
  omega

/-- The selected core actor lies in T, acts nontrivially and has corank k.
Its literal kernel is the central intersection, so it bounds w above. -/
theorem GeometricSelected.core_actor_data (s : GeometricSelected H T M V I k i S)
    (hT : HypothesisE322 V T) :
    let A := V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    A ≤ T ∧ ¬ A ≤ centralizer (V : Set G) ∧
      subgroupCorank (V.map (MulAut.conj (i.val)⁻¹).toMonoidHom) A = k ∧
      A ⊓ centralizer (V : Set G) = V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ∧
      globalW V T ≤ k := by
  let A := V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hAT : A ≤ T := by
    have hm := map_mono (f := I.subtype) (pCore_isPGroup.le_sylow_of_normal S)
    rw [s.sylow_eq, subgroupOf_map_subtype] at hm
    exact inf_le_right.trans (hm.trans inf_le_left)
  have hAC : ¬ A ≤ centralizer (V : Set G) := by
    intro hc
    apply s.twoConjugate.commutator_V_A_ne_bot (geometric_generator_proper s)
      s.characteristic_two
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    intro a ha v hv
    apply Subtype.ext
    have ham : (a : G) ∈ A := by
      dsimp only [A]
      rw [← selected_actor_image I M V hVI S i s.twoConjugate]
      exact mem_map_of_mem I.subtype ha
    exact hc ham v.val hv
  have hcor : subgroupCorank (V.map (MulAut.conj (i.val)⁻¹).toMonoidHom) A = k := by
    rw [conjugate_core_corank I V i.val i.property,
      ← quotient_rank_eq_core_corank I V hVI]
    exact s.rank_eq
  refine ⟨hAT, hAC, hcor, selected_actor_kernel I M V hVI S i s.twoConjugate, ?_⟩
  rw [← hcor]
  exact globalW_le_corank_of_noncentralizing_normalizes hT i.val⁻¹
    (le_inf inf_le_left (hAT.trans hT.normalizes)) hAC


end CFSG.Quasithin.Chapter8.Section02.HermitianSource
