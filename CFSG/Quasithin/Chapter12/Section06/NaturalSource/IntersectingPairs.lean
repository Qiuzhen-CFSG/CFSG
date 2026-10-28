module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.F9
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.PointPerpendicular
public import Theory.GroupTheory.PCoreRestriction

/-!
# Original intersecting-pair two-groups in 12.6.24

The singular-point orbit transports V5 <= O2(C_G(z)) to each nonzero
singular point. Two distinct points in a subgroup A <= V have polar
hyperplanes spanning V; restricting their point-centralizer cores gives
V <= O2(C_G(A)) <= O2(N_G(A)). Thus a conjugate sharing those points
with V generates a two-group with V.

If an intersection contains a nonsingular point, the earlier centralizer
control instead puts the conjugate inside M, where V <= O2(M). This
proves the literal pair condition of 12.6.24(5) without a plane-positioning
premise. Fixed-space vanishing, point invariance, the intersection bound,
and nonsingular centralizer control remain the earlier source obligations
of qt-d-12634-central and the final assembly.

Source: Aschbacher--Smith, 12.6.24(3--5), printed pp.830--831.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open BinaryPermutation BinaryPermutation.TerminalOrthogonal.Eight
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

include hZ in
/-- The original L-action transports any nonzero singular point to any other. -/
theorem SourceHypothesis.original_singular_point_orbit
    (hz : z ≠ 1) (hs : ¬ D.Nonsingular z)
    (w : V) (hw : w ≠ 1) (hsw : ¬ D.Nonsingular w) :
    ∃ l : L, conjugation L V S.chosen.normalizes l z = w := by
  have hz0 : (D.fullCoordinates hZ z).toAdd ≠ 0 := by
    intro hh
    exact hz ((D.fullCoordinates hZ).injective (hh.trans (D.fullCoordinates hZ).map_one.symm))
  have hw0 : (D.fullCoordinates hZ w).toAdd ≠ 0 := by
    intro hh
    exact hw ((D.fullCoordinates hZ).injective (hh.trans (D.fullCoordinates hZ).map_one.symm))
  obtain ⟨a,ha⟩ := EightGeometry.singular_transitive _ _ hz0 hw0
    (by by_contra hh; exact hs ((D.fullCoordinates_nonsingular_iff hZ z).mp hh))
    (by by_contra hh; exact hsw ((D.fullCoordinates_nonsingular_iff hZ w).mp hh))
  obtain ⟨l,hl⟩ := D.groupEquiv.surjective.comp
    (QuotientGroup.mk'_surjective (conjugation L V S.chosen.normalizes).ker) a
  change D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker l) = a at hl
  refine ⟨l,?_⟩
  apply (D.fullCoordinates hZ).injective
  have he := D.fullCoordinates_equivariant hZ l z
  rw [hl] at he
  exact he.trans ha

/-- Every original singular perpendicular lies in its own point centralizer two-core. -/
theorem SourceHypothesis.original_singular_perpendicular_core
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hout : ¬ (D.fullSetup hZ T z).Gz ≤ M L)
    (w : V) (hw : w ≠ 1) (hsw : ¬ D.Nonsingular w) :
    (D.fullSetup hZ T z).pointPerpendicular w ≤ (Gv w.val).pCoreIn 2 := by
  let E := D.fullSetup hZ T z
  have hGz := E.Gz_mem_Hz hz hTz hout
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hGz
  have hcore : E.V₅ ≤ E.Gz.pCoreIn 2 :=
    (le_conjugateSpanBy E.V₅ E.Gz).trans h.UH_le_QH
  obtain ⟨l,hl⟩ := S.original_singular_point_orbit D hZ z hz
    (S.original_point_singular D hZ z hz hTz) w hw hsw
  let a : normalizer (V : Set G) := ⟨l.val,S.chosen.normalizes l.property⟩
  let p := (D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker l)).val
  have hp : ∀ u : E.V, (E.coordinates (E.V.normalizerMonoidHom a u)).toAdd =
      naturalRepresentation (Fin 8) p (E.coordinates u).toAdd :=
    fun u => D.fullCoordinates_equivariant hZ l u
  have hc := E.pointPerpendicular_core_transport hz hcore a p hp
  have he : E.V.normalizerMonoidHom a E.z = w := hl
  rw [he] at hc
  exact hc

/-- Two distinct singular points of A put V in the centralizer and normalizer cores of A. -/
theorem SourceHypothesis.original_two_singular_point_core
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hout : ¬ (D.fullSetup hZ T z).Gz ≤ M L)
    (A : Subgroup G) (hAV : A ≤ V)
    (v w : V) (hv : v ≠ 1) (hw : w ≠ 1) (hvw : v ≠ w)
    (hvA : v.val ∈ A) (hwA : w.val ∈ A)
    (hsv : ¬ D.Nonsingular v) (hsw : ¬ D.Nonsingular w) :
    V ≤ (centralizer (A : Set G)).pCoreIn 2 ∧
      V ≤ (normalizer (A : Set G)).pCoreIn 2 := by
  let E := D.fullSetup hZ T z
  let C := centralizer (A : Set G)
  have hVC : V ≤ C := (le_centralizer V).trans (centralizer_le hAV)
  have hlocal (u : V) (hu : u ≠ 1) (huA : u.val ∈ A) (hs : ¬ D.Nonsingular u) :
      E.pointPerpendicular u ≤ C.pCoreIn 2 := by
    have hCu : C ≤ Gv u.val := centralizer_le (Set.singleton_subset_iff.mpr huA)
    exact (le_inf ((E.pointPerpendicular_le u).trans hVC)
      (S.original_singular_perpendicular_core D hZ z hz hTV hTz hbound hout u hu hs)).trans
        (inf_pCoreIn_le_of_le 2 hCu)
  have hcore : V ≤ C.pCoreIn 2 := by
    change E.V ≤ C.pCoreIn 2
    rw [←E.pointPerpendicular_sup v w hvw]
    exact sup_le (hlocal v hv hvA hsv) (hlocal w hw hwA hsw)
  refine ⟨hcore,hcore.trans (pCoreIn_mono_of_normalizes
    (Subgroup.centralizer_le_normalizer _) ?_)⟩
  exact (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance

/-- Original 12.6.24(5), with no additional plane-positioning or pair hypothesis. -/
theorem SourceHypothesis.original_intersecting_pair_isTwoGroup
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hout : ¬ (D.fullSetup hZ T z).Gz ≤ M L)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (g : G) (hi : (D.fullSetup hZ T z).V₁ < V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let E := D.fullSetup hZ T z
  let W := V.map (MulAut.conj g).toMonoidHom
  let A := V ⊓ W
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hWA : W ≤ centralizer (A : Set G) := (le_centralizer W).trans (centralizer_le inf_le_right)
  obtain ⟨x,hx,hxn⟩ := SetLike.exists_of_lt hi
  let w : V := ⟨x,hx.1⟩
  have hw : w ≠ 1 := by intro he; apply hxn; rw [show x=1 from congrArg Subtype.val he]; exact E.V₁.one_mem
  by_cases hs : D.Nonsingular w
  · have hWM : W ≤ M L := hWA.trans
      ((centralizer_le (Set.singleton_subset_iff.mpr hx)).trans (hns w hs))
    have hVM : V ≤ (M L).pCoreIn 2 := S.chosen.le_componentCore.trans
      (pCoreIn_mono_of_normalizes L.le_normalizer (le_refl (M L)))
    exact isPGroup_sup_of_le_pCoreIn hVM hWM (IsElementaryAbelian.isPGroup 2 W)
  · have hzA : z.val ∈ A := hi.le (mem_zpowers _)
    have hzw : z ≠ w := by
      intro he
      apply hxn
      rw [show x=z.val from (congrArg Subtype.val he).symm]
      exact mem_zpowers _
    have hcore := (S.original_two_singular_point_core D hZ z hz hTV hTz hbound hout
      A inf_le_left z w hz hw hzw hzA hx
      (S.original_point_singular D hZ z hz hTz) hs).1
    exact isPGroup_sup_of_le_pCoreIn hcore hWA (IsElementaryAbelian.isPGroup 2 W)

end CFSG.Quasithin.Chapter12.Section06
