module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicCore

/-!
# Invariant subgroups in the original first-parabolic argument

Write A = O²(L ∩ I), S = T ∩ I and I₁ = AS. An I₁-invariant subgroup
P contained in Mc centralizes the original point Z, hence its A-span V.
For P contained in M and escaping Mc, original 14.6.6(3) factors L over
O²(L ∩ PS). This residual lies in P because P is normal in PS with a
two-group quotient. Two-perfection then forces A into P. Thus both local
branches of 14.6.10(3) follow without the source's direct-product calculation.

For P escaping both locals, PS is another maximal outside subgroup:
it contains the nontrivial two-core of I and has the same Sylow intersection.
The conditional assembly retains precisely the earlier 14.6.9 factorization
for such subgroups contained in I. That earlier source theorem is not proved
here. The final application excludes the normal-complement alternatives at
the beginning of 14.6.10(5), with exactly the same remaining premise.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.6.10(3) and the opening of (5),
printed pp.1028–1029. The local escaping-intersection consumer discharges its
factorization using the proved original 14.6.6(3), printed p.1023.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_sup_le (P S : Subgroup G)
    (hn : S ≤ normalizer (P : Set G)) (hp : IsPGroup 2 S) :
    (pResidual 2 (P ⊔ S : Subgroup G)).map (P ⊔ S).subtype ≤ P := by
  let J := P ⊔ S
  let : (P.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hn)
  have hq : IsPGroup 2 (J ⧸ P.subgroupOf J) :=
    isPGroup_quotient_of_sup_eq_top (P.subgroupOf J) (S.subgroupOf J)
      hp.comap_subtype (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  have hr : pResidual 2 J ≤ P.subgroupOf J := sInf_le ⟨inferInstance,hq⟩
  rintro x ⟨a,ha,rfl⟩
  exact hr ha

private theorem invariant_residual_le_of_cover (L I J P : Subgroup G)
    (hJI : J ≤ I)
    (hn : (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype ≤
      normalizer (P : Set G))
    (hRP : (pResidual 2 (L ⊓ J : Subgroup G)).map (L ⊓ J).subtype ≤ P)
    (hcover : (L : Set G) =
      ((pResidual 2 (L ⊓ J : Subgroup G)).map (L ⊓ J).subtype : Set G) *
        (L.pCoreIn 2 : Set G)) :
    (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype ≤ P := by
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let D := (pResidual 2 (L ⊓ J : Subgroup G)).map (L ⊓ J).subtype
  have hDR : D ≤ R := embedded_pResidual_mono 2 (inf_le_inf_left L hJI)
  have hRL : R ≤ L := (map_subtype_le _).trans inf_le_left
  let N := P.subgroupOf R
  let Q := (L.pCoreIn 2).subgroupOf R
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hsup : N ⊔ Q = ⊤ := by
    apply top_unique
    intro x _
    have hx : (x : G) ∈ (L : Set G) := hRL x.property
    rw [hcover] at hx
    obtain ⟨d,hd,q,hq,he⟩ := Set.mem_mul.mp hx
    have hdR : d ∈ R := hDR hd
    have hqR : q ∈ R := by
      have heq : q = d⁻¹ * (x : G) := by rw [←he]; group
      rw [heq]
      exact R.mul_mem (R.inv_mem hdR) x.property
    have hmem := (N ⊔ Q).mul_mem (mem_sup_left (show (⟨d,hdR⟩ : R) ∈ N from hRP hd))
      (mem_sup_right (show (⟨q,hqR⟩ : R) ∈ Q from hq))
    have he' : (⟨d,hdR⟩ : R) * ⟨q,hqR⟩ = x := Subtype.ext he
    exact he' ▸ hmem
  have htop : N = ⊤ := (isPPerfect_embedded_pResidual 2 (L ⊓ I)) N inferInstance
    (isPGroup_quotient_of_sup_eq_top N Q (isPGroup_pCoreIn 2 L).comap_subtype hsup)
  intro r hr
  exact (show (⟨r,hr⟩ : R) ∈ N from htop ▸ mem_top _)

private theorem plane_span_eq (Z V A : Subgroup G)
    (hZV : Z ≤ V) (hNV : A ≤ normalizer (V : Set G))
    (hZ : Nat.card Z = 2) (hV : Nat.card V = 4)
    (hout : ¬ A ≤ centralizer (Z : Set G)) : conjugateSpanBy Z A = V := by
  let W := conjugateSpanBy Z A
  have hZW : Z ≤ W := le_conjugateSpanBy Z A
  have hWV : W ≤ V := conjugateSpanBy_le hZV hNV
  have hd : Nat.card W ∣ 4 := hV ▸ card_dvd_of_le hWV
  have hge : 2 ≤ Nat.card W := hZ ▸ Nat.card_le_card_of_injective
    (Subgroup.inclusion hZW) (Subgroup.inclusion_injective _)
  have hle : Nat.card W ≤ 4 := Nat.le_of_dvd (by decide) hd
  have hc : Nat.card W = 2 ∨ Nat.card W = 4 := by
    interval_cases h : Nat.card W <;> norm_num at *
  rcases hc with hc | hc
  · have he : Z = W := eq_of_le_of_card_ge hZW (by omega)
    have hn : A ≤ normalizer (Z : Set G) := by
      rw [he]
      exact le_normalizer_conjugateSpanBy Z A
    exact (hout (hn.trans (normalizer_le_centralizer_of_card_two Z hZ))).elim
  · apply eq_of_le_of_card_ge hWV
    omega

namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal


/-- The first intersection residual spans the original plane from its point. -/
theorem source_intersection_point_span
    (I : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (hcover : (sourceResidual M Mc : Set G) =
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((sourceResidual M Mc).pCoreIn 2 : Set G)) :
    conjugateSpanBy (centralInvolutions T)
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype) = localModule T M := by
  obtain ⟨hSyl,_⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI
  obtain ⟨_,_,_,hout⟩ := source_intersection_parabolic_data hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct I hI.2.1 hSyl hcover
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hZ,hMc,_⟩ :=
    source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e
  apply plane_span_eq _ _ _ (le_conjugateSpanBy _ _)
    (((map_subtype_le _).trans inf_le_left).trans
      ((sourceResidual_le M Mc).trans (le_normalizer_conjugateSpanBy _ M))) hZ hcard
  rwa [←hMc]

/-- The partner-local branch of original 14.6.10(3). -/
theorem source_invariant_subgroup_in_partner
    (I P : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (hcover : (sourceResidual M Mc : Set G) =
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((sourceResidual M Mc).pCoreIn 2 : Set G))
    (hN : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ normalizer (P : Set G))
    (hP : P ≤ Mc) : P ≤ M ⊓ centralizer (localModule T M : Set G) := by
  have hMc : Mc = centralizer (centralInvolutions T : Set G) := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hMc,_⟩ :=
      source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e
    exact hMc
  have hC := le_centralizer_conjugateSpanBy_of_normalizes P (centralInvolutions T)
    _ hN (hMc ▸ hP)
  rw [source_intersection_point_span hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I hI hcover] at hC
  have hCM : centralizer (localModule T M : Set G) ≤ M := by
    simpa only [Section02.rankTwoSeed_eq_localModule] using
      (Section02.source_lemma_14_2_4 hG T hempty hM hunique hmany hcard e).seed_centralizer_le
  exact le_inf (hC.trans hCM) hC

/-- Both local branches of original 14.6.10(3). -/
theorem source_invariant_subgroup_in_local
    (I P : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (hcover : (sourceResidual M Mc : Set G) =
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((sourceResidual M Mc).pCoreIn 2 : Set G))
    (hPI : P ≤ I)
    (hN : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I) ≤
        normalizer (P : Set G))
    (hPM : P ≤ M ∨ P ≤ Mc) :
    (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ P ∨
        P ≤ M ⊓ centralizer (localModule T M : Set G) := by
  by_cases hPMc : P ≤ Mc
  · exact Or.inr (source_invariant_subgroup_in_partner hG T hempty hM hunique
      hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I P hI hcover
      (le_sup_left.trans hN) hPMc)
  have hPM := hPM.resolve_right hPMc
  left
  let S := (T : Subgroup G) ⊓ I
  let J := P ⊔ S
  have hJM : J ≤ M := sup_le hPM (inf_le_left.trans hM.1.2)
  have hJI : J ≤ I := sup_le hPI inf_le_right
  have hTuJ : (T : Subgroup G) ⊓ centralizer ({u} : Set G) ≤ J :=
    (le_inf inf_le_left hI.2.1).trans le_sup_right
  have hout : ¬ J ⊓ M ≤ Mc := by
    rw [inf_eq_left.mpr hJM]
    exact fun hh => hPMc (le_sup_left.trans hh)
  have hJcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct J hTuJ hout).1
  apply invariant_residual_le_of_cover (sourceResidual M Mc) I J P hJI
    (le_sup_left.trans hN) _ hJcover
  exact (embedded_pResidual_mono 2 (inf_le_right : sourceResidual M Mc ⊓ J ≤ J)).trans
    (residual_sup_le P S (le_sup_right.trans hN) (T.isPGroup'.to_le inf_le_left))

/-- The local branches of original 14.6.10(3) for the escaping-intersection
choice: the required earlier factorization is discharged by 14.6.6(3). -/
theorem source_invariant_subgroup_in_local_of_escape
    (I P : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (hout : ¬ I ⊓ M ≤ Mc)
    (hPI : P ≤ I)
    (hN : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I) ≤
        normalizer (P : Set G))
    (hPM : P ≤ M ∨ P ≤ Mc) :
    (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ P ∨
        P ≤ M ⊓ centralizer (localModule T M : Set G) := by
  exact source_invariant_subgroup_in_local hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I P hI
    (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct I hI.2.1 hout).1 hPI hN hPM

/-- Original 14.6.10(3), with only the earlier 14.6.9 factorization retained
for maximal outside subgroups contained in the original I. -/
theorem source_lemma_14_6_10_3_of_factorizations
    (I P : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hfactor : ∀ J : Subgroup G, J ≤ I →
      J ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) →
      (sourceResidual M Mc : Set G) =
        ((pResidual 2 (sourceResidual M Mc ⊓ J : Subgroup G)).map
          (sourceResidual M Mc ⊓ J).subtype : Set G) *
            ((sourceResidual M Mc).pCoreIn 2 : Set G))
    (hPI : P ≤ I)
    (hN : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I) ≤
        normalizer (P : Set G)) :
    (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ P ∨
        P ≤ M ⊓ centralizer (localModule T M : Set G) := by
  have hcover := hfactor I le_rfl hI
  by_cases hPM : P ≤ M ∨ P ≤ Mc
  · exact source_invariant_subgroup_in_local hG T hempty hM hunique hmany hcard e hab
      H hH u hu hindex hmove hproduct hU3 hlocal I P hI.1 hcover hPI hN hPM
  have hnotM : ¬ P ≤ M := fun hh => hPM (Or.inl hh)
  have hnotMc : ¬ P ≤ Mc := fun hh => hPM (Or.inr hh)
  left
  let S := (T : Subgroup G) ⊓ I
  let J := P ⊔ S
  have hJI : J ≤ I := sup_le hPI inf_le_right
  have hSJ : S ≤ J := le_sup_right
  obtain ⟨hSyl,_⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
  obtain ⟨SI,hSI⟩ := hSyl
  have hQIS : I.pCoreIn 2 ≤ S := by
    change I.pCoreIn 2 ≤ (T : Subgroup G) ⊓ I
    rw [← hSI]
    exact pCoreIn_le_sylow I SI
  have hIn : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hcoreJ : I.pCoreIn 2 ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I) (hQIS.trans hSJ) (hJI.trans hIn)
  have hJH : J ∈ Chapter1.H G := by
    intro hz
    exact hI.1.1 (le_bot_iff.mp (hz ▸ hcoreJ))
  have hJout : J ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M :=
    ⟨hJH,(le_inf inf_le_left hI.1.2.1).trans hSJ,
      fun hh => hnotMc (le_sup_left.trans hh),fun hh => hnotM (le_sup_left.trans hh)⟩
  have hJstar := (lemma14_6_4 hI hJout hSJ).1
  apply invariant_residual_le_of_cover (sourceResidual M Mc) I J P hJI
    (le_sup_left.trans hN) _ (hfactor J hJI hJstar)
  exact (embedded_pResidual_mono 2 (inf_le_right : sourceResidual M Mc ⊓ J ≤ J)).trans
    (residual_sup_le P S (le_sup_right.trans hN) (T.isPGroup'.to_le inf_le_left))

/-- The actual first application in 14.6.10(5): the normal-complement
alternatives of F.6.18(2) are impossible. The remaining input is the same
earlier 14.6.9 factorization as in the preceding invariant-subgroup theorem. -/
theorem source_normal_complement_exclusion_of_factorizations
    (I P : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hfactor : ∀ J : Subgroup G, J ≤ I →
      J ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) →
      (sourceResidual M Mc : Set G) =
        ((pResidual 2 (sourceResidual M Mc ⊓ J : Subgroup G)).map
          (sourceResidual M Mc ⊓ J).subtype : Set G) *
            ((sourceResidual M Mc).pCoreIn 2 : Set G))
    (hPI : P ≤ I) (hN : I ≤ normalizer (P : Set G))
    (hgen : P ⊔ ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) = I)
    (hmeet : P ⊓ sourceResidual M Mc ≤ (sourceResidual M Mc).pCoreIn 2) : False := by
  let L := sourceResidual M Mc
  let LI := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let S := (T : Subgroup G) ⊓ I
  have hLIL : LI ≤ L := (map_subtype_le _).trans inf_le_left
  have hLII : LI ≤ I := (map_subtype_le _).trans inf_le_right
  have hI1I : LI ⊔ S ≤ I := sup_le hLII inf_le_right
  have hcover := hfactor I le_rfl hI
  rcases source_lemma_14_6_10_3_of_factorizations hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I P hI hfactor hPI
    (hI1I.trans hN) with hLP | hPC
  · obtain ⟨hSyl,_⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
      hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
    obtain ⟨_,_,_,hout⟩ := source_intersection_parabolic_data hG T hempty hM hunique
      hmany hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover
    obtain ⟨_,_,_,_,_,hcore,_⟩ := source_lemma_14_1_18 hG T hempty hM hunique
      hmany hcard e
    apply hout
    have hLIcore : LI ≤ L.pCoreIn 2 := (le_inf hLP hLIL).trans hmeet
    exact hLIcore.trans ((hcore.le.trans inf_le_right).trans
      (InitialSource.localModule_centralizer_le_partner T M hunique))
  · apply hI.1.2.2.2
    rw [←hgen]
    exact sup_le (hPC.trans inf_le_left)
      (sup_le (hLIL.trans (sourceResidual_le M Mc)) (inf_le_left.trans hM.1.2))

end CFSG.Quasithin.Chapter14.Section06
