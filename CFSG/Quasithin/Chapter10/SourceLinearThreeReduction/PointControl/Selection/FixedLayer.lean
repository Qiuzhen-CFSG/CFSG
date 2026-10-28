module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Thompson
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.Transport

/-!
# Fixed vectors and Baumann orbits in the selected non-A₅ module

If the L₀-fixed layer is fixed by T₁=N_T(L), half-Sylow uniqueness controls
every nonidentity vector in that layer. Thus an escaping opposite point
distinguishes the two original components, and its Sylow centralizer
normalizes L. No fixed vector is discarded from the conclusion.

For the Baumann branch, a conjugate fixing the point suffices: local Sylow
saturation and Baumann weak closure move it into the original C_T(v).
The source module geometry and Baumann normalizer containment remain
explicit. Source: Aschbacher--Smith, 10.1.2, 10.2.8--9, pp.742,749--750.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Fixation by T₁ upgrades an L₀-fixed vector to a half-join-fixed vector. -/
theorem fixed_element_centralizer_le
    (hhalf : HalfSylowUnique D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
      centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G))
    {v : G} (hv : v ∈ D.fullModule) (hvne : v ≠ 1)
    (hv0 : v ∈ centralizer (localOrbit T L : Set G)) :
    centralizer ({v} : Set G) ≤ D.maximalLocal := by
  apply fixed_element_centralizer_le_of_halfSylowUnique D hhalf hv hvne
  change v ∈ centralizer (↑(localOrbit T L ⊔
    ((T : Subgroup G) ⊓ normalizer (L : Set G))) : Set G)
  have hc : localOrbit T L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)) ≤
      centralizer ({v} : Set G) :=
    sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (hv0 x hx))
      (fun x hx => mem_centralizer_singleton_iff.mpr ((hfix ⟨hv,hv0⟩) x hx))
  exact fun x hx => mem_centralizer_singleton_iff.mp (hc hx)

/-- An escaping opposite point cannot lie in the fixed layer, and hence
its Sylow centralizer stabilizes the original component. -/
theorem escaping_point_stabilizes
    (hhalf : HalfSylowUnique D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
      centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hvne : v ≠ 1) (hout : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal) :
    v ∉ centralizer (localOrbit T L : Set G) ∧
      (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  have hv0 : v ∉ centralizer (localOrbit T L : Set G) := fun h =>
    hout (fixed_element_centralizer_le D hhalf hfix (partner_le_fullModule D ht hv) hvne h)
  refine ⟨hv0,?_⟩
  exact (inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
    (source_nonnormal_element_centralizer_stabilizes D
      (fun hn => htn (hn ht)) (hcross hv) hv0)

/-- The literal fixed-layer and Baumann-orbit inputs suffice for every
locally saturated escaping point, including points initially fixed by L₀. -/
theorem pointSylowControl_of_baumann_orbits
    (hhalf : HalfSylowUnique D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
      centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (horbit : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom,
      v ≠ 1 → v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
      ∃ m ∈ D.maximalLocal, (ChapterB.baumann (T : Subgroup G)).map
        (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G)) :
    PointSylowControl D t := by
  intro v hv hvne hout hs
  obtain ⟨hv0,hstab⟩ := escaping_point_stabilizes D hhalf hfix ht htn hcross hv hvne hout
  exact ⟨source_element_sylow_normalizer_of_baumann_centralizes D hB
    (source_point_baumann_fixed_of_conjugate_fixed D hs (horbit v hv hvne hv0 hs)),hstab⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection
