module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalOrdinaryComponent

/-!
# The original singular span lies in the actual overcomponent core

The returned nonsingular pair belongs to the intrinsic two-core of the
same normal overcomponent K. Its singular product generates the point
line. Intersecting that core with the original perpendicular gives an
invariant subgroup containing the point line and a nonsingular point.
The original F.9 irreducibility therefore fills the whole perpendicular.
Normality of K then puts its full singular-centralizer conjugate span in
the same intrinsic core.

The source application obtains F.9 from the proved global intersection
bound. It retains the original pair, ambient Sylow and common residual,
and does not assume nonsingular control or faithfulness of K.

Source: the original polar geometry and F.9 reduction in Section12.6,
Aschbacher--Smith, printed pp.830--831.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Irreducibility enlarges the actual returned pair's core containment
to the entire perpendicular, and normality enlarges it to the full span. -/
theorem OrthogonalMarking.nonsingular_pair_span_le_normal_core
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn)
    (hZ : ZV L V = ⊥) (T : Sylow 2 G) (u w : V)
    (hu : D.Nonsingular u) (hw : D.Nonsingular w)
    (hz : u*w ≠ 1) (hs : ¬ D.Nonsingular (u*w))
    (hf : ((D.fullSetup hZ T (u*w)).f9 (Gv ((u*w : V) : G))).Hypothesis)
    (K : Subgroup G) (hKN : Gv ((u*w : V) : G) ≤ normalizer (K : Set G))
    (huCore : (u : G) ∈ K.pCoreIn 2) (hwCore : (w : G) ∈ K.pCoreIn 2) :
    (D.fullSetup hZ T (u*w)).V₅ ≤ K.pCoreIn 2 ∧
      (D.fullSetup hZ T (u*w)).UH (Gv ((u*w : V) : G)) ≤ K.pCoreIn 2 := by
  classical
  let z : V := u*w
  let E := D.fullSetup hZ T z
  let W := E.V₅ ⊓ K.pCoreIn 2
  have hNC : Gv (z : G) ≤ normalizer (K.pCoreIn 2 : Set G) :=
    hKN.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hpoint : E.V₁ ≤ W := le_inf E.V₁_le_V₅
    (zpowers_le.mpr ((K.pCoreIn 2).mul_mem huCore hwCore))
  have hnorm : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (le_inf hf.local_normalizes (hf.local_le.trans hNC)).trans
      inf_normalizer_le_normalizer_inf
  have hne : W ≠ E.V₁ := by
    intro he
    have hu5 := (D.nonsingular_pair_mem_singular_perpendicular hZ T u w hu hw hs).1
    have hmem : (u : G) ∈ E.V₁ := he ▸ (show (u : G) ∈ W from ⟨hu5,huCore⟩)
    change (u : G) ∈ zpowers (z : G) at hmem
    have hzo : orderOf (z : G) = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property)
      (fun he => hz (Subtype.ext he))
    rw [mem_zpowers_iff_mem_range_orderOf,hzo] at hmem
    obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp hmem
    have hi2 : i < 2 := Finset.mem_range.mp hi
    interval_cases i
    · apply nonsingular_ne_one D hu
      apply Subtype.ext
      simpa only [pow_zero,Subgroup.coe_one] using hei.symm
    · have huz : u = z := Subtype.ext (by simpa only [pow_one] using hei.symm)
      exact hs ((congrArg D.Nonsingular huz).mp hu)
  have hwhole : W = E.V₅ := (hf.irreducible W hpoint inf_le_left hnorm).resolve_left hne
  have hplus : E.V₅ ≤ K.pCoreIn 2 := hwhole ▸ (inf_le_right : W ≤ K.pCoreIn 2)
  exact ⟨hplus,conjugateSpanBy_le hplus hNC⟩

/-- The same actual ordinary normal overcomponent contains the full
singular perpendicular and its conjugate span in its intrinsic two-core. -/
theorem SourceHypothesis.exists_original_hs_normal_overcomponent_core_span
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ u w : V,
      D.Nonsingular u ∧ D.Nonsingular w ∧ w ≠ u ∧
      ∃ P : Sylow 2 G, ∃ t ∈ (P : Subgroup G),
        (MulAut.conj t) (u : G) = w ∧ (MulAut.conj t) (w : G) = u ∧
        let z := u*w
        z ≠ 1 ∧ ¬ D.Nonsingular z ∧
        (T : Subgroup G) ≤ Gv (z : G) ∧ (P : Subgroup G) ≤ Gv (z : G) ∧
        ¬ Gv (z : G) ≤ M L ∧ (D.fullSetup hZ T z).Gz ∈ (D.fullSetup hZ T z).Hz ∧
        let B := Gv (u : G) ⊓ Gv (z : G)
        let J := (primeToResidual 3 B).map B.subtype
        J ≤ Kv (u : G) ⊓ Kv (w : G) ∧
        (P : Subgroup G) ≤ normalizer (J : Set G) ∧
        Group.IsPerfect J ∧ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∧
        ¬ ⁅V,J⁆ ≤ (Gv (z : G)).pCoreIn 2 ∧
        ∃ K : Subgroup G, K ≤ Gv (z : G) ∧
          (K.subgroupOf (Gv (z : G))).IsCComponent ∧
          IsQuasisimple (K ⧸ pCore 2 K) ∧ J ≤ K ∧
          Gv (z : G) ≤ normalizer (K : Set G) ∧
          (u : G) ∈ K.pCoreIn 2 ∧ (w : G) ∈ K.pCoreIn 2 ∧
          ¬ ⁅V,K⁆ ≤ (Gv (z : G)).pCoreIn 2 ∧
          (D.fullSetup hZ T z).V₅ ≤ K.pCoreIn 2 ∧
          (D.fullSetup hZ T z).UH (Gv (z : G)) ≤ K.pCoreIn 2 := by
  obtain ⟨hZ,u,w,hu,hw,huw,P,t,ht,htu,htw,hz,hs,hTz,hPz,hout,hHz,
    hJC,hPJ,hperf,hquot,hmoveJ,K,hKG,hKC,hordinary,hJK,hKN,huCore,hwCore,hmoveK⟩ :=
    H.exists_original_hs_ordinary_normal_overcomponent D hTV hTI v hv he
  let z : V := u*w
  let E := D.fullSetup hZ T z
  have hnz : (T : Subgroup G) ≤ normalizer (E.V₁ : Set G) := by
    apply hTz.trans
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [Nonabelian.Setup.V₁,zpowers_eq_closure,centralizer_closure]
    rfl
  have hHz' : Gv (z : G) ∈ E.Hz := by rwa [E.Gz_eq] at hHz
  have hf := H.original_f9_of_earlier_geometry D hZ z hz hTV hnz
    (H.original_hs_conjugate_intersection_bound D hTV hTI v hv he) hHz'
  have hspan := D.nonsingular_pair_span_le_normal_core hZ T u w hu hw hz hs
    hf K hKN huCore hwCore
  exact ⟨hZ,u,w,hu,hw,huw,P,t,ht,htu,htw,hz,hs,hTz,hPz,hout,hHz,
    hJC,hPJ,hperf,hquot,hmoveJ,K,hKG,hKC,hordinary,hJK,hKN,huCore,hwCore,hmoveK,hspan⟩

end CFSG.Quasithin.Chapter12.Section06
