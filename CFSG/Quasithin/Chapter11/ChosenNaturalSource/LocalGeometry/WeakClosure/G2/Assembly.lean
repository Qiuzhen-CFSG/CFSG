module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Inputs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Bounds
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Module

/-!
# Conditional assembly of the G₂ weak-closure clauses

The actual r-bound puts the root-generated three-space in V and V^g.
Equality of the plane families, generation by their residuals and the
preceding 11.1.3 uniqueness then force g into N_G(L). The full M-orbit of
V is already proved elementary abelian, so this contradicts the assumed
noncentral action of V^g on V. Thus every zeroth generator centralizes V.
The companion bounds module supplies the two normalizer bounds, positive w,
and the C₁ bound, and the last theorem applies them to the rank-one consumer.

This is not an unconditional proof of 11.2.2(5--6). RootPlaneData and
R1FamilyLocalization still need their B.4.6 model constructions; the exact
earlier parameter, plane-component and three-space-normalizer conclusions
remain explicit for their existing source owners.
Source: Aschbacher--Smith, 11.2.2, pp.767--768, and 11.5.1, p.778.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
open ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (marking : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 marking))

/-- The source three-space is a genuine nontrivial subgroup of the intersection
of the original modules. This retains any central part of V. -/
theorem RootPlaneData.common_threeSpace {g : G} (h : RootPlaneData D S marking f g)
    (hr : (2 * S.field.degree : ℕ∞) < @globalR G _ V) :
    h.threeSpace ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom ∧ h.threeSpace ≠ ⊥ := by
  let := D.elementary
  obtain ⟨l, hl⟩ := h.marked_threeSpace
  have hUV : h.threeSpace ≤ V := by
    rw [hl]
    exact (map_mono (D.centralQuotientPreimage_le _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (D.normalizes l.property))
  refine ⟨le_inf hUV (h.rootSpan.le_conjugate hr), ?_⟩
  rw [hl]
  intro he
  exact f.V_ne_bot 2 ((map_eq_bot_iff_of_injective _ (MulAut.conj (l : G)).injective).mp he)

private theorem conjugate_centralizes_of_mem_M (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) (g : G)
    (hg : g ∈ normalizer (L : Set G)) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  let W := componentOrbit V (normalizer (L : Set G))
  let : IsElementaryAbelian 2 W := Preliminary.fullModule_elementary D S
  have hVW : V ≤ W := le_componentOrbit V _
  have hgW : V.map (MulAut.conj g).toMonoidHom ≤ W :=
    le_iSup_of_le (⟨g, hg⟩ : normalizer (L : Set G)) le_rfl
  exact hgW.trans ((Subgroup.le_centralizer W).trans (Subgroup.centralizer_le hVW))

/-- The common-plane and root calculations imply zeroth centralization.
No centralization or weak-closure normalizer bound is an input. -/
theorem zero_centralizes_of_root_planes
    (hr : (2 * S.field.degree : ℕ∞) < @globalR G _ V)
    (hcomponents : PlaneComponents L (f.Vi 1))
    (hroots : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      Nonempty (RootPlaneData D S marking f g)) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  refine le_inf (indexedWeakClosure_le V (T : Subgroup G) 0) ?_
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hgT⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  by_contra hnon
  obtain ⟨h⟩ := hroots g hgT hnon
  have hUA := (h.common_threeSpace D S marking f hr).1.trans inf_le_right
  have hgM := mem_normalizer_of_common_planes L (f.Vi 1) h.threeSpace g
    (h.common_planes hUA) (h.original_generation hUA) (h.conjugate_generation hUA)
    (fun I hI => by
      have hconj : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      have hi : I ∈ planeFamily (L.map (MulAut.conj (1 : G)).toMonoidHom)
          ((f.Vi 1).map (MulAut.conj (1 : G)).toMonoidHom) h.threeSpace := by
        simpa only [hconj, Subgroup.map_id] using hI
      simpa only [hconj, Subgroup.map_id] using hcomponents 1 h.threeSpace I hi)
    (fun I hI => (hcomponents g h.threeSpace I hI).1)
  exact hnon (conjugate_centralizes_of_mem_M D S g hgM)

/-- All requested bounds, conditional only on the named earlier source clauses
and the two explicit B.4.6 geometry constructions. In particular m=2n. -/
theorem clauses_of_geometry
    (hr : (2 * S.field.degree : ℕ∞) < @globalR G _ V)
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hcomponents : PlaneComponents L (f.Vi 1))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hloc : R1FamilyLocalization D S f)
    (hroots : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      Nonempty (RootPlaneData D S marking f g)) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ normalizer (L : Set G) ∧
      0 < globalW V (T : Subgroup G) ∧
      centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G) ∧
      indexedWeakClosure V (f.Ri 0) 0 = indexedWeakClosure V (T : Subgroup G) 0 ∧
      normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G) := by
  have hw := zero_centralizes_of_root_planes D S marking f hr hcomponents hroots
  obtain ⟨hN, hwpos, heq, hNR⟩ := normalizer_bounds_of_zero_centralizes D S f hw
  exact ⟨hw, hN, hwpos, weakCentralizer_centralizer_le_of_family D S f hs hloc hthree,
    heq, hNR⟩

/-- The existing 11.5.1 consumer now receives both bounds derived above;
its outside subgroup and relative Sylow retain their literal ambient maps. -/
theorem rankOne_impossible_of_root_planes
    (hr : (2 * S.field.degree : ℕ∞) < @globalR G _ V)
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hcomponents : PlaneComponents L (f.Vi 1))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hloc : R1FamilyLocalization D S f)
    (hroots : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      Nonempty (RootPlaneData D S marking f g))
    (H₁ : Subgroup G) (P : Sylow 2 H₁)
    (hP : (P : Subgroup H₁).map H₁.subtype = f.Ri 0)
    (hn : generationParameter H₁ = 1) (hout : ¬ H₁ ≤ normalizer (L : Set G)) : False :=
  rankOne_impossible_of_geometry D S f hs hloc hthree
    (zero_centralizes_of_root_planes D S marking f hr hcomponents hroots) H₁ P hP hn hout

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
