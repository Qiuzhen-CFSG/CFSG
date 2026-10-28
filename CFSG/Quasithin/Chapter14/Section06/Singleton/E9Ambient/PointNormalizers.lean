module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NineAmbientParallel.PointCentralizers
public import Theory.GroupTheory.PGroup.IndexTwoOmegaCenter

/-!
# The actual M-normalizer of the elementary-nine critical plane

The index-two point-centralizer has central omega subgroup exactly the plane
on the two original point lines. Its normalizer in J is the Sylow supplement
obtained by adjoining O₂(J). The full normalizer escapes Mc: a Sylow subgroup
in the conjugate point-centralizer containing this half-Sylow subgroup would
otherwise have both distinct points as its central omega subgroup.

Aligning the Sylow subgroup by an element of J, the two-overgroup theorem
14.1.18 puts this plane normalizer in M. Its movement of the original central
point identifies the plane with the original M-module. In particular the
whole J-span equals its moved subgroup and has order thirty-two.

All critical endpoints use the same J, T, quotient representation and core
maps. These restrictions supply an ambient step for the exceptional singleton
of 14.6.12; they do not exclude that case. The printed irreducibility shortcut
is not used. Sources: Aschbacher--Smith, 14.1.18, pp.980--981; 14.6.1--2,
pp.1020--1021; 14.6.12, p.1031; and F.9.13--17, pp.322--324 of
refs/quasithin.pdf, together with the elementary index-two omega-center bound.
-/

open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise

private theorem omega_card_bound {G : Type*} [Group G] [Finite G]
    (C S : Subgroup G) (hCS : C ≤ S) (hi : C.relIndex S = 2)
    (hz : Nat.card (omegaOneCenterAmbient S) = 2) :
    Nat.card (omegaOneCenterAmbient C) ≤ 4 := by
  have hb := card_omega_center_le_sq_of_index_two (C.subgroupOf S) hi
  have he : Nat.card (omegaOneCenterAmbient C) =
      Nat.card (omega₁ (center (C.subgroupOf S)) (p := 2)) := by
    conv_lhs => rw [← map_subgroupOf_eq_of_le hCS]
    rw [omegaOneCenterAmbient_map_injective _ S.subtype_injective,
      card_map_of_injective S.subtype_injective]
    simp only [omegaOneCenterAmbient, card_map_of_injective (C.subgroupOf S).subtype_injective,
      card_map_of_injective (center (C.subgroupOf S)).subtype_injective]
  have hz' : Nat.card (omega₁ (center S) (p := 2)) = 2 := by
    simpa only [omegaOneCenterAmbient,card_map_of_injective S.subtype_injective,
      card_map_of_injective (center S).subtype_injective] using hz
  rw [he]
  simpa only [hz',show (2 : ℕ)^2 = 4 from rfl] using hb

private theorem sylow_omega_eq {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (J : Subgroup G) (hTJ : (T : Subgroup G) ≤ J)
    (hc : J ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (S : Sylow 2 J) :
    omegaOneCenterAmbient ((S : Subgroup J).map J.subtype) =
      omegaOneCenterAmbient (T : Subgroup G) := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq J (T.subtype hTJ) S
  rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
  change omegaOneCenterAmbient
    (((T.subtype hTJ : Subgroup J).map (MulAut.conj g).toMonoidHom).map J.subtype) = _
  rw [Subgroup.map_map]
  have he : J.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp J.subtype := rfl
  rw [he,←Subgroup.map_map,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ,
    omegaOneCenterAmbient_map_injective _ (MulAut.conj (g : G)).injective]
  exact mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) (hc g.property))

private theorem sylow_overgroup_card {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (J : Subgroup G) (hTJ : (T : Subgroup G) ≤ J)
    (S : Sylow 2 J) : Nat.card S = Nat.card T := by
  calc
    Nat.card S = Nat.card (T.subtype hTJ) := by
      rw [S.card_eq_multiplicity,(T.subtype hTJ).card_eq_multiplicity]
    _ = Nat.card T := Nat.card_congr (subgroupOfEquivOfLe hTJ).toEquiv

private theorem half_sylow_normalizer_escape {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (C : Subgroup G) (hp : IsPGroup 2 C)
    (hi : 2 * Nat.card C = Nat.card T) (g : G)
    (hC : C ≤ centralizer
      ((omegaOneCenterAmbient (T : Subgroup G)).map (MulAut.conj g).toMonoidHom : Set G))
    (hne : (omegaOneCenterAmbient (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≠
      omegaOneCenterAmbient (T : Subgroup G)) :
    ¬ normalizer (C : Set G) ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Zg := Z.map (MulAut.conj g).toMonoidHom
  let H := centralizer (Z : Set G)
  let K := centralizer (Zg : Set G)
  let P : Sylow 2 G := T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hPomega : omegaOneCenterAmbient (P : Subgroup G) = Zg := by
    change omegaOneCenterAmbient ((T : Subgroup G).map (MulAut.conj g).toMonoidHom) = Zg
    exact omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective _
  have hTH : (T : Subgroup G) ≤ H := by
    intro t ht z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht |>.symm
  have hPK : (P : Subgroup G) ≤ K := by
    intro p hp z hz
    rw [←hPomega] at hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 p hp |>.symm
  have hPc : Nat.card P = Nat.card T :=
    card_map_of_injective (MulAut.conj g).injective
  obtain ⟨R,hCR₀⟩ := (hp.comap_subtype : IsPGroup 2 (C.subgroupOf K)).exists_le_sylow
  let Rg := (R : Subgroup K).map K.subtype
  have hCR : C ≤ Rg := by
    have hh := map_mono (f := K.subtype) hCR₀
    change (C.subgroupOf K).map K.subtype ≤ Rg at hh
    rwa [map_subgroupOf_eq_of_le (show C ≤ K from hC)] at hh
  have hRc : Nat.card Rg = Nat.card T :=
    (card_map_of_injective K.subtype_injective).trans
      ((sylow_overgroup_card P K hPK R).trans hPc)
  have hiR : C.relIndex Rg = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) C Rg bot_le hCR
    simp only [relIndex_bot_left,hRc] at hh
    have hpos : 0 < Nat.card C := Nat.card_pos
    nlinarith
  have hRN : Rg ≤ normalizer (C : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hCR).mp (normal_of_index_eq_two hiR)
  intro hN
  have hRH : Rg ≤ H := hRN.trans hN
  have hRp : IsPGroup 2 Rg := R.isPGroup'.map K.subtype
  obtain ⟨S,hRS₀⟩ := (hRp.comap_subtype : IsPGroup 2 (Rg.subgroupOf H)).exists_le_sylow
  have hRS : Rg ≤ (S : Subgroup H).map H.subtype := by
    have hh := map_mono (f := H.subtype) hRS₀
    change (Rg.subgroupOf H).map H.subtype ≤ (S : Subgroup H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hRH] at hh
  have he : Rg = (S : Subgroup H).map H.subtype := eq_of_le_of_card_ge hRS (by
    rw [card_map_of_injective H.subtype_injective,sylow_overgroup_card T H hTH S,hRc])
  have hz : omegaOneCenterAmbient Rg = Z := by
    rw [he]
    exact sylow_omega_eq T H hTH le_rfl S
  have hzg : omegaOneCenterAmbient Rg = Zg :=
    (sylow_omega_eq P K hPK (by simpa only [hPomega] using (le_rfl : K ≤ K)) R).trans hPomega
  exact hne (hzg.symm.trans hz)

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

open OddCriticalPair.OrthogonalSource


/-- The entire central omega subgroup of the critical point-centralizer is
exactly the plane on the two original point lines. -/
theorem source_singleton_nine_point_centralizer_omega
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
      C = J ⊓ i.conjugate Mc ∧
      omegaOneCenterAmbient C = D.V₁ ⊔ i.conjugate D.V₁ ∧
      normalizer (C : Set G) ≤ normalizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  let A := D.V₁ ⊔ i.conjugate D.V₁
  have hb := (source_rankTwo_critical_track_bounds
    hG T hempty hM hu hmany hcard e hab J hJ.1).1
  have hpU : i.conjugate D.V₁ ≤ D.UH := by
    rw [← (source_singleton_nine_paired_point_lines
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).1]
    exact (commutator_mono inf_le_left (i.large_le hb)).trans (moved_le a)
  have hAomega : A ≤ omegaOneCenterAmbient C := by
    apply sup_le
    · intro z hz
      have hzU := h.point_lt.le.trans (le_conjugateSpanBy D.V D.H) hz
      apply (mem_omegaOneCenterAmbient_iff _ _).mpr
      refine ⟨⟨h.UH_le_QH.trans (pCoreIn_le 2 J) hzU,?_⟩,
        elemPow_eq_one_of_isElementaryAbelian z hzU,?_⟩
      · exact (le_centralizer_iff.mp h.H_centralizes).trans
          (centralizer_le (hpU.trans (h.UH_le_QH.trans (pCoreIn_le 2 J)))) hz
      · intro c hc
        exact (h.H_centralizes hc.1 z hz).symm
    · intro z hz
      have hzU := hpU hz
      apply (mem_omegaOneCenterAmbient_iff _ _).mpr
      refine ⟨⟨h.UH_le_QH.trans (pCoreIn_le 2 J) hzU,?_⟩,
        elemPow_eq_one_of_isElementaryAbelian z hzU,?_⟩
      · exact ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
          (centralizer_le hpU)) hzU
      · intro c hc
        exact (hc.2 z hz).symm
  obtain ⟨S,hCS,hi,_⟩ := source_singleton_nine_point_centralizer_sylow
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have hZ : Nat.card (omegaOneCenterAmbient ((S : Subgroup J).map J.subtype)) = 2 := by
    rw [sylow_omega_eq T J h.T_le_H h.H_centralizes S]
    exact h.point_card
  have hAc : Nat.card A = 4 := (source_singleton_nine_paired_point_lines
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2.2.2.1
  have he : omegaOneCenterAmbient C = A :=
    (eq_of_le_of_card_ge hAomega (hAc ▸ omega_card_bound C _ hCS hi hZ)).symm
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_,he,?_⟩
  · change C = J ⊓ Mc.map (MulAut.conj i.representative).toMonoidHom
    rw [hMc,map_centralizer_equiv]
    rfl
  · intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change A.map (MulAut.conj x).toMonoidHom = A
    change x ∈ normalizer (C : Set G) at hx
    rw [←he,←omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective]
    exact congrArg omegaOneCenterAmbient
      (show C.map (MulAut.conj x).toMonoidHom = C from mem_normalizer_iff_map_conj_eq.mp hx)

/-- Both the critical point-centralizer and its central plane have exactly the
same Sylow normalizer inside the original J. -/
theorem source_singleton_nine_point_normalizers
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
      ∃ S : Sylow 2 J,
        C ≤ (S : Subgroup J).map J.subtype ∧
        C.relIndex ((S : Subgroup J).map J.subtype) = 2 ∧
        C ⊔ J.pCoreIn 2 = (S : Subgroup J).map J.subtype ∧
        J ⊓ normalizer (C : Set G) = (S : Subgroup J).map J.subtype ∧
        J ⊓ normalizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) =
          (S : Subgroup J).map J.subtype := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨p,_,hE,_,_,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let := hE
  have hSyl (S : Sylow 2 (J ⧸ pCore 2 J)) : IsMulCommutative S := by
    let := (source_singleton_nine_quotient_structure
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine).2 S |>.1
    infer_instance
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  let C₀ := C.subgroupOf J
  let N := J ⊓ normalizer (C : Set G)
  let N₀ := N.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := C₀.map q
  let F := N₀.map q
  have hC := (source_singleton_nine_point_centralizers
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).1
  obtain ⟨S,hCS,hi,hSN⟩ := source_singleton_nine_point_centralizer_sylow
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have hCN : C₀ ≤ N₀ := fun x hx => ⟨x.property,C.le_normalizer hx⟩
  have hn : N₀ ≤ normalizer (C₀ : Set J) := by
    rw [show C₀ = C.subgroupOf J from rfl,←subgroupOf_normalizer_eq (show C ≤ J from inf_le_left)]
    exact fun _ hx => hx.2
  have hNF : F ≤ normalizer (B : Set (J ⧸ pCore 2 J)) :=
    (map_mono (f := q) hn).trans (C₀.le_normalizer_map q)
  have hBp : IsPGroup 2 B := hC.comap_subtype.map q
  have hBcore : B ≤ F.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hBp (map_mono hCN) hNF
  have hBc : Nat.card B = 4 := (source_singleton_nine_point_centralizer_indices
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.1
  have hFcore : pCore 2 F ≠ ⊥ := by
    intro he
    have hh : F.pCoreIn 2 = ⊥ := by simp only [pCoreIn,he,Subgroup.map_bot]
    have hBbot : B = ⊥ := bot_unique (hh ▸ hBcore)
    rw [hBbot,card_bot] at hBc
    omega
  have hFp : IsPGroup 2 F := isPGroup_of_nontrivial_core_of_primitive_odd_residual
    (pCore_quotient_pCore_eq_bot 2) (hnine ▸ (by decide : Odd 9)) hmin hSyl F hFcore
  have hNp : IsPGroup 2 N₀ :=
    (hFp.comap_of_ker_isPGroup q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)).to_le
      (le_comap_map q N₀)
  have hSNe : N₀ = (S : Subgroup J) := S.is_maximal' hNp (by
    intro x hx
    exact ⟨x.property,hSN (mem_map_of_mem J.subtype hx)⟩)
  have hNe : N = (S : Subgroup J).map J.subtype := by
    have hh := congrArg (fun A : Subgroup J => A.map J.subtype) hSNe
    rwa [map_subgroupOf_eq_of_le (show N ≤ J from inf_le_left)] at hh
  have hQ : J.pCoreIn 2 ≤ (S : Subgroup J).map J.subtype := pCoreIn_le_sylow J S
  have hnot : ¬ J.pCoreIn 2 ≤ C := by
    intro hc
    have hidx := (source_singleton_nine_point_centralizer_indices
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).1
    rw [inf_eq_right.mpr hc,relIndex_self] at hidx
    omega
  have hjoin : C ⊔ J.pCoreIn 2 = (S : Subgroup J).map J.subtype := by
    have hle := sup_le hCS hQ
    have hh := relIndex_mul_relIndex C (C ⊔ J.pCoreIn 2)
      ((S : Subgroup J).map J.subtype) le_sup_left hle
    rw [hi] at hh
    have hp : (C.relIndex (C ⊔ J.pCoreIn 2) *
        (C ⊔ J.pCoreIn 2).relIndex ((S : Subgroup J).map J.subtype)).Prime :=
      hh.symm ▸ Nat.prime_two
    rcases Nat.prime_mul_iff.mp hp with ⟨_,h1⟩ | ⟨_,h1⟩
    · exact le_antisymm hle (relIndex_eq_one.mp h1)
    · exact (hnot (le_sup_right.trans (relIndex_eq_one.mp h1))).elim
  have hCA : C = J ⊓ centralizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) := by
    have hcZ : C ≤ centralizer (D.V₁ : Set G) := inf_le_left.trans h.H_centralizes
    have hcP : C ≤ centralizer (i.conjugate D.V₁ : Set G) := inf_le_right
    have hcA : C ≤ centralizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) :=
      le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hcZ) (le_centralizer_iff.mp hcP))
    exact le_antisymm (le_inf inf_le_left hcA)
      (le_inf inf_le_left (inf_le_right.trans (centralizer_le (show (i.conjugate D.V₁ : Set G) ⊆
        (D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) from
          fun _ hz => (le_sup_right : i.conjugate D.V₁ ≤ D.V₁ ⊔ i.conjugate D.V₁) hz))))
  have hNA : J ⊓ normalizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) ≤ N := by
    intro x hx
    refine ⟨hx.1,?_⟩
    rw [hCA]
    exact inf_normalizer_le_normalizer_inf ⟨J.le_normalizer hx.1,
      normalizer_le_normalizer_centralizer _ hx.2⟩
  have hAN : N ≤ J ⊓ normalizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) :=
    le_inf inf_le_left (inf_le_right.trans (source_singleton_nine_point_centralizer_omega
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2)
  exact ⟨S,hCS,hi,hjoin,hNe,(le_antisymm hNA hAN).trans hNe⟩

/-- The actual point-centralizer normalizer and point-plane normalizer both
escape the original Mc. -/
theorem source_singleton_nine_point_normalizer_escapes_Mc
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
      ¬ normalizer (C : Set G) ≤ Mc ∧
      ¬ normalizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) ≤ Mc := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  obtain ⟨S,hCS,hi,_⟩ := source_singleton_nine_point_centralizer_sylow
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  change C.relIndex ((S : Subgroup J).map J.subtype) = 2 at hi
  have hCc : 2 * Nat.card C = Nat.card T := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) C
      ((S : Subgroup J).map J.subtype) bot_le hCS
    simp only [relIndex_bot_left,hi,card_map_of_injective J.subtype_injective,
      sylow_overgroup_card T J h.T_le_H S] at hh
    exact (Nat.mul_comm _ _).trans hh
  have hne : (omegaOneCenterAmbient (T : Subgroup G)).map
      (MulAut.conj i.representative).toMonoidHom ≠ omegaOneCenterAmbient (T : Subgroup G) := by
    change i.conjugate D.V₁ ≠ D.V₁
    intro he
    have hh := (source_singleton_nine_paired_point_lines
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2.2.1
    rw [he,inf_idem] at hh
    have hp := h.point_card
    rw [hh,card_bot] at hp
    omega
  have hnot := half_sylow_normalizer_escape T C
    (source_singleton_nine_point_centralizers
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).1
    hCc i.representative inf_le_right hne
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hN : ¬ normalizer (C : Set G) ≤ Mc := by
    rw [hMc]
    exact hnot
  exact ⟨hN,fun hn => hN ((source_singleton_nine_point_centralizer_omega
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2.trans hn)⟩

omit hab in
private theorem source_normal_plane_eq_module
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hZA : centralInvolutions T ≤ A) (hAc : Nat.card A = 4)
    (hTN : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hnot : ¬ normalizer (A : Set G) ≤ Mc) : A = localModule T M := by
  have hZc : Nat.card (centralInvolutions T) = 2 :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfam := (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hlocal : IsTwoLocal (normalizer (A : Set G)) :=
    ⟨A,fun he => by rw [he,card_bot] at hAc; omega,
      IsElementaryAbelian.isPGroup 2 A,rfl⟩
  obtain ⟨N,hAN,hN⟩ := Finite.exists_le_maximal hlocal
  have hNm : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hN,hTN.trans hAN⟩
  rw [hfam,Set.mem_insert_iff,Set.mem_singleton_iff] at hNm
  have hNM : normalizer (A : Set G) ≤ M := by
    rcases hNm with rfl | rfl
    · exact hAN
    · exact (hnot hAN).elim
  obtain ⟨x,hx,hxMc⟩ := SetLike.not_le_iff_exists.mp hnot
  let Z := centralInvolutions T
  let Zx := Z.map (MulAut.conj x).toMonoidHom
  have hZxA : Zx ≤ A := (map_mono hZA).trans_eq (mem_normalizer_iff_map_conj_eq.mp hx)
  have hZxV : Zx ≤ localModule T M := by
    rintro _ ⟨z,hz,rfl⟩
    exact subset_closure ⟨x,hNM hx,z,hz,rfl⟩
  have hZV : Z ≤ localModule T M := le_conjugateSpanBy _ _
  have hdis : Z ⊓ Zx = ⊥ := inf_eq_bot_of_card_two_of_ne _ _ hZc
    ((card_map_of_injective (MulAut.conj x).injective).trans hZc) (by
      intro he
      apply hxMc
      rw [hMc]
      exact normalizer_le_centralizer_of_card_two Z hZc
        (mem_normalizer_iff_map_conj_eq.mpr he.symm))
  have hnorm : Zx ≤ normalizer (Z : Set G) :=
    (hZxA.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hZA))).trans (Subgroup.centralizer_le_normalizer _)
  have hfour : Nat.card (Z ⊔ Zx : Subgroup G) = 4 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z Zx hnorm
    rw [hZc,card_map_of_injective (MulAut.conj x).injective,hZc,hdis,card_bot,one_mul] at hh
    exact hh.symm
  have hWA : Z ⊔ Zx = A := eq_of_le_of_card_ge (sup_le hZA hZxA) (by rw [hAc,hfour])
  have hWV : Z ⊔ Zx = localModule T M := eq_of_le_of_card_ge (sup_le hZV hZxV)
    (by rw [hcard,hfour])
  exact hWA.symm.trans hWV

/-- The critical central plane is a J-conjugate of the original M-plane.
Its full normalizer is the same conjugate of M. -/
theorem source_singleton_nine_point_plane_placement
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
      ∃ g : J,
        omegaOneCenterAmbient C = (localModule T M).conjBy (g : G) ∧
        normalizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) = M.conjBy (g : G) ∧
        normalizer (C : Set G) ≤ M.conjBy (g : G) ∧
        J ⊓ normalizer (C : Set G) = (T : Subgroup G).conjBy (g : G) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  let A := D.V₁ ⊔ i.conjugate D.V₁
  obtain ⟨_,hO,hN⟩ := source_singleton_nine_point_centralizer_omega
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  change omegaOneCenterAmbient C = A at hO
  change normalizer (C : Set G) ≤ normalizer (A : Set G) at hN
  obtain ⟨S,_,_,_,hNS,hAS⟩ := source_singleton_nine_point_normalizers
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J (T.subtype h.T_le_H) S
  have hSg : (S : Subgroup J).map J.subtype = (T : Subgroup G).conjBy (g : G) := by
    rw [←hg,Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
    change (((T.subtype h.T_le_H : Subgroup J).map (MulAut.conj g).toMonoidHom).map J.subtype) = _
    rw [Subgroup.map_map]
    have he : J.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp J.subtype := rfl
    rw [he,←Subgroup.map_map,Sylow.coe_subtype,map_subgroupOf_eq_of_le h.T_le_H]
    rfl
  have hZN : D.V₁.conjBy (g : G)⁻¹ = D.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer _) (h.H_centralizes (J.inv_mem g.property)))
  let A' := A.conjBy (g : G)⁻¹
  let : IsElementaryAbelian 2 A := hO ▸ omegaOneCenterAmbient_elementaryAbelian C
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  have hZA : D.V₁ ≤ A' := by
    have hh := map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom)
      (show D.V₁ ≤ A from le_sup_left)
    change D.V₁.conjBy (g : G)⁻¹ ≤ A' at hh
    rwa [hZN] at hh
  have hTA : (T : Subgroup G) ≤ normalizer (A' : Set G) := by
    have hh := map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom)
      (hAS.ge.trans inf_le_right)
    rw [map_equiv_normalizer_eq,hSg] at hh
    change ((T : Subgroup G).conjBy (g : G)).conjBy (g : G)⁻¹ ≤ normalizer (A' : Set G) at hh
    rwa [conjBy_inv] at hh
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMcg : Mc.conjBy (g : G) = Mc :=
    mem_normalizer_iff_map_conj_eq.mp (Mc.le_normalizer (hMc.ge (h.H_centralizes g.property)))
  have hnot : ¬ normalizer (A' : Set G) ≤ Mc := by
    intro hn
    have hh := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hn
    rw [map_equiv_normalizer_eq] at hh
    change normalizer ((A.conjBy (g : G)⁻¹).conjBy (g : G) : Set G) ≤ Mc.conjBy (g : G) at hh
    rw [conjBy_inv',hMcg] at hh
    exact (source_singleton_nine_point_normalizer_escapes_Mc
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2 hh
  have hAc : Nat.card A' = 4 := (card_map_of_injective (MulAut.conj (g : G)⁻¹).injective).trans
    (source_singleton_nine_paired_point_lines
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2.2.2.1
  have hAeq := source_normal_plane_eq_module hG T hempty hM hu hmany hcard e A' hZA hAc hTA hnot
  have hAV : A = (localModule T M).conjBy (g : G) := by
    have hh := congrArg (fun B : Subgroup G => B.conjBy (g : G)) hAeq
    change (A.conjBy (g : G)⁻¹).conjBy (g : G) = _ at hh
    rwa [conjBy_inv'] at hh
  have hNM : normalizer (A : Set G) = M.conjBy (g : G) := by
    rw [hAV]
    change normalizer ((localModule T M).map (MulAut.conj (g : G)).toMonoidHom : Set G) = _
    rw [←map_equiv_normalizer_eq,←Chapter15.Section03.InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
    rfl
  exact ⟨g,hO.trans hAV,hNM,hN.trans_eq hNM,hNS.trans hSg⟩

/-- The M-plane placement removes the whole fixed summand: the original
span is its moved subgroup and has order thirty-two. -/
theorem source_singleton_nine_whole_span_moved
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ _i : h.CriticalEndpoint,
      D.UH = ⁅D.UH,J⁆ ∧ Nat.card D.UH = 32 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let W := ⁅D.UH,J⁆
  have hJW : J ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  have hb := (source_rankTwo_critical_track_bounds
    hG T hempty hM hu hmany hcard e hab J hJ.1).1
  have hAW : D.V₁ ⊔ i.conjugate D.V₁ ≤ W :=
    (source_singleton_nine_paired_point_lines
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2.1.trans
      (commutator_mono le_rfl (i.large_le hb))
  obtain ⟨g,hO,_,_,_⟩ := source_singleton_nine_point_plane_placement
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have hAeq : D.V₁ ⊔ i.conjugate D.V₁ = (localModule T M).conjBy (g : G) :=
    (source_singleton_nine_point_centralizer_omega
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.1.symm.trans hO
  have hVW : localModule T M ≤ W := by
    rw [hAeq] at hAW
    have hh := map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom) hAW
    change ((localModule T M).conjBy (g : G)).conjBy (g : G)⁻¹ ≤ W.conjBy (g : G)⁻¹ at hh
    have hWg : W.conjBy (g : G)⁻¹ = W :=
      mem_normalizer_iff_map_conj_eq.mp (hJW (J.inv_mem g.property))
    rw [conjBy_inv,hWg] at hh
    exact hh
  have he : D.UH = W := le_antisymm (conjugateSpanBy_le hVW hJW) (moved_le a)
  obtain ⟨s,_,_⟩ := source_singleton_nine_support_planes
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  refine ⟨he,?_⟩
  rw [he]
  exact (source_singleton_nine_lifted_supports hG T hempty hM hu hmany hcard e hab J hJ hs a s).2.2.2.2

end CFSG.Quasithin.Chapter14.Section06
