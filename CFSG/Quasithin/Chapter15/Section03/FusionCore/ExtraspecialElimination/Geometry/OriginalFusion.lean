module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Local
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Fusion

/-!
# The original fusion inputs for the extraspecial geometry

The proved 15.3.47 alternative is the F.9 normalizer test. If the large
span at C_G(Z) is elementary abelian, fusion control makes conjugates
containing Z commute. Total singularity and the singular orbit transport
each nontrivial intersection to one containing that same Z. These are the
actual inputs used to construct normalized critical endpoints.

Source: Aschbacher--Smith, 15.3.46--47 and 15.3.49(e), combined manuscript
(1 March 2004), printed pp.1141 and 1143.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V P : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original 15.3.47 alternative supplies the F.9 normalizer test. -/
theorem normalizer_test_of_earlier_inputs
    (d : FusionCore.NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P) :
    ConjugateNormalizerTest V (fixedPlane V (planeStabilizer T P)) := by
  intro x hx hne
  exact (lemma_15_3_47_of_earlier_inputs d h hP x hx).resolve_left hne

/-- The elementary span at the actual centralizer of Z supplies F.9.8(f).
Total singularity and the proved singular orbit handle every nontrivial
intersection, not just intersections already containing the fixed line. -/
theorem intersecting_conjugates_commute_of_earlier_inputs
    (d : FusionCore.NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    [IsMulCommutative (localSpan V Mc)] :
    ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨_, c⟩ := orthogonalCoordinateModel_and_fusionCalculations d h hP
  have hfusion := controlsFusion_of_orthogonal_calculations c h
  have hcentral := nonsingular_centralizer_le_of_orthogonal_calculations c h
  have hsing := totallySingular_intersection_of_fusion d.form h.normalizer_eq hfusion hcentral
  have hZ : centralInvolutions T = zpowers (c.z : G) := by
    let z : centralInvolutions T := ⟨c.z, c.z_central⟩
    have hz : z ≠ 1 := by
      intro he
      apply c.z_ne_one
      apply Subtype.ext
      exact congrArg (fun w : centralInvolutions T => (w : G)) he
    have he : zpowers z = ⊤ := zpowers_eq_top_of_prime_card h.central_order hz
    have hm := congrArg (Subgroup.map (centralInvolutions T).subtype) he
    rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm.symm
  have hclosure : centralizerConjugateClosure V (c.z : G) = localSpan V Mc :=
    AbelianAmalgam.centralizerConjugateClosure_eq_localSpan (hMc.trans (congrArg
      (fun Z : Subgroup G => centralizer (Z : Set G)) hZ))
  let : IsMulCommutative (centralizerConjugateClosure V (c.z : G)) :=
    hclosure.symm ▸ inferInstance
  intro g hg
  by_cases hgm : g ∈ M
  · have hmap : V.map (MulAut.conj g).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (d.normalizes hgm)
    rw [hmap]
    exact commutator_self_eq_bot_iff.mpr inferInstance
  · refine commutator_conjugate_eq_bot_of_intersection_fusion V (c.z : G) g ?_ hg ?_
    · intro a ha
      obtain ⟨m, hm, he⟩ := hfusion c.z c.z.property a ha
      exact ⟨m, d.normalizes hm, he⟩
    · intro x hx hxne
      have hs : d.form (Additive.ofMul (⟨x, hx.1⟩ : V)) = 0 :=
        (hsing g hgm).2 ⟨x, hx.1⟩ hx
      obtain ⟨m, hm, he⟩ := (c.singular_orbit ⟨x, hx.1⟩
        (fun hh => hxne (congrArg Subtype.val hh)) hs).symm
      exact ⟨m, d.normalizes hm, he⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry
