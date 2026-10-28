module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.E9Ambient.PointNormalizers
public import Theory.GroupTheory.SylowCentralizerOfNormalizer
public import Theory.GroupTheory.RelativeSylowFrattini

/-!
# The full ambient plane action on the critical point centralizer

In the elementary-nine branch, let A be the plane on the original point
and its critical conjugate, and let C be the centralizer of the latter
inside J. The known Sylow normalizer of C normalizes A, and its intersection
with C_G(A) is exactly C. Restriction of Sylow subgroups therefore makes C
Sylow in the full plane centralizer. Frattini's argument gives
C_G(A) N_G(C) = N_G(A), the actual conjugate of M already identified in
PointNormalizers. The correction factor lies in C_G(A), so it preserves
the action on the same plane.

Both full abelian Mc-spans, with the original critical conjugator, are
normal two-subgroups of C_G(A); hence both lie in C. This uses the two
original point commutators to put A in both spans. No abstract normalizer
callback or new ambient identification is assumed.

These are further ambient restrictions, not the elementary-nine exclusion.
Source: Aschbacher--Smith, 14.6.12, printed p.1031, using 14.1.18,
Hypothesis 14.5.1 and F.9.13--17, refs/quasithin.pdf; Sylow restriction and
Frattini's argument supply the ambient normalizer step.
-/

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


/-- The original point centralizer is Sylow in the full plane centralizer.
Every plane-normalizer action lifts to its normalizer by a correction in the
same plane centralizer, and both full Mc-spans lie in it. -/
theorem source_singleton_nine_plane_frattini
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
      let A := D.V₁ ⊔ i.conjugate D.V₁
      let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
      let K := centralizer (A : Set G)
      (∃ R : Sylow 2 K, (R : Subgroup K).map K.subtype = C) ∧
      K ⊔ normalizer (C : Set G) = normalizer (A : Set G) ∧
      (∀ x ∈ normalizer (A : Set G), ∃ c ∈ K, c * x ∈ normalizer (C : Set G)) ∧
      conjugateSpanBy (localModule T M) Mc ⊔
        i.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ C := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let A := D.V₁ ⊔ i.conjugate D.V₁
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  let K := centralizer (A : Set G)
  obtain ⟨g,_,_,_,hNS⟩ := source_singleton_nine_point_plane_placement
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  let S : Sylow 2 G := T.mapSurjective
    (f := (MulAut.conj (g : G)).toMonoidHom) (MulAut.conj (g : G)).surjective
  have hSN : (S : Subgroup G) = J ⊓ normalizer (C : Set G) := hNS.symm
  have hCN : normalizer (C : Set G) ≤ normalizer (A : Set G) :=
    (source_singleton_nine_point_centralizer_omega
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2
  have hCA : C ≤ K := by
    apply le_centralizer_iff.mp
    apply sup_le
    · exact (le_centralizer_iff.mp h.H_centralizes).trans (centralizer_le inf_le_left)
    · exact le_centralizer_iff.mp inf_le_right
  have hCS : C ≤ (S : Subgroup G) := by
    rw [hSN]
    exact le_inf inf_le_left C.le_normalizer
  have hSC : (S : Subgroup G) ⊓ K = C := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans (hSN.le.trans inf_le_left))
        (inf_le_right.trans (centralizer_le (show i.conjugate D.V₁ ≤ A from le_sup_right)))
    · exact le_inf hCS hCA
  obtain ⟨R,hR⟩ := S.exists_centralizer_sylow_of_normalizes A
    (hSN.le.trans (inf_le_right.trans hCN))
  have hRC : (R : Subgroup K).map K.subtype = C := hR.trans hSC
  have hKC : normalizer (A : Set G) ≤ normalizer (K : Set G) :=
    normalizer_le_normalizer_centralizer A
  have hKN : K ≤ normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _
  have hfr := relative_sylow_frattini K (normalizer (A : Set G)) hKN hKC R
  rw [hRC,inf_eq_right.mpr hCN] at hfr
  have hprod := relative_sylow_frattini_product K (normalizer (A : Set G)) hKN hKC R
  rw [hRC,inf_eq_right.mpr hCN] at hprod
  refine ⟨⟨R,hRC⟩,hfr,?_,?_⟩
  · intro x hx
    have hx' : x ∈ (normalizer (A : Set G) : Set G) := hx
    rw [hprod] at hx'
    obtain ⟨k,hk,n,hn,rfl⟩ := hx'
    have hkn : k⁻¹ * (k * n) ∈ normalizer (C : Set G) := by
      rw [inv_mul_cancel_left]
      exact hn
    exact ⟨k⁻¹,K.inv_mem hk,hkn⟩
  let W := conjugateSpanBy (localModule T M) Mc
  let W' := i.conjugate W
  let : IsElementaryAbelian 2 (localModule T M) := h.elementary
  let : IsMulCommutative W := hab
  let : IsElementaryAbelian 2 W := conjugateSpanBy_elementary_of_commutative _ _
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map _
  have hMc : Mc = centralizer (D.V₁ : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hJMc : J ≤ Mc := by rw [hMc]; exact h.H_centralizes
  have hUW : D.UH ≤ W := conjugateSpanBy_mono le_rfl hJMc
  have hUW' : i.conjugate D.UH ≤ W' := map_mono hUW
  have hb := (source_rankTwo_critical_track_bounds
    hG T hempty hM hu hmany hcard e hab J hJ.1).1
  have hAcomm := (source_singleton_nine_paired_point_lines
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2.1
  have hAUB : A ≤ D.UH ⊓ i.conjugate D.UH := hAcomm.trans (i.commutator hb)
  have hAW : A ≤ W := (hAUB.trans inf_le_left).trans hUW
  have hAW' : A ≤ W' := (hAUB.trans inf_le_right).trans hUW'
  have hWK : W ≤ K := (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
    (centralizer_le hAW)
  have hW'K : W' ≤ K := (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
    (centralizer_le hAW')
  have hKW : K ≤ normalizer (W : Set G) := by
    apply le_trans _ (le_normalizer_conjugateSpanBy _ _)
    rw [hMc]
    exact centralizer_le (show D.V₁ ≤ A from le_sup_left)
  have hKW' : K ≤ normalizer (W' : Set G) := by
    have hn := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (le_normalizer_conjugateSpanBy (localModule T M) Mc)
    rw [map_equiv_normalizer_eq,hMc,map_centralizer_equiv] at hn
    rw [←hMc] at hn
    exact (centralizer_le (show i.conjugate D.V₁ ≤ A from le_sup_right)).trans hn
  have hWC : W ≤ C := (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
    hWK hKW).trans ((pCoreIn_le_sylow K R).trans_eq hRC)
  have hW'C : W' ≤ C := (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W')
    hW'K hKW').trans ((pCoreIn_le_sylow K R).trans_eq hRC)
  exact sup_le hWC hW'C

end CFSG.Quasithin.Chapter14.Section06
