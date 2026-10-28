module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Perpendicular
public import Theory.Representation.G2BinaryNondegeneratePlane.Orbits

/-!
# Marking every original nondegenerate plane

Transport nondegeneracy to the literal coordinate image, then apply the proved
G₂(2) transitivity on nondegenerate planes. Conjugate the full-automizer chart
and the linear coordinates together. The original alternating form is unchanged,
and the actual binary derived subgroup remains in the actor image.

Source: Aschbacher--Smith 13.3.12, printed p.889, citing Asc87, 5.1.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
theorem coordinate_plane_nondegenerate
    (E : Additive V ≃ₗ[K] W) (A : Subgroup G) (hAV : A ≤ V)
    (hcard : Nat.card A = 4)
    (hn : ((UnitaryGeometry.markedForm E).restrict
      (UnitaryGeometry.ambientSpace (V := V) A)).Nondegenerate) :
    Module.finrank K (pointCoordinateSubspace E A) = 2 ∧
      (form.restrict (pointCoordinateSubspace E A)).Nondegenerate := by
  let S := UnitaryGeometry.ambientSpace (V := V) A
  have hP : S.map E.toLinearMap = pointCoordinateSubspace E A := by
    ext w
    obtain ⟨v, rfl⟩ := E.surjective w
    rw [mem_pointCoordinateSubspace]
    constructor
    · rintro ⟨u, hu, huv⟩
      exact E.injective huv ▸ hu
    · intro hv
      exact ⟨v, hv, rfl⟩
  have hN : (form.restrict (S.map E.toLinearMap)).Nondegenerate := by
    have h := hn.congr (E.submoduleMap S)
    have hb : LinearMap.BilinForm.congr (E.submoduleMap S)
        ((UnitaryGeometry.markedForm E).restrict S) = form.restrict (S.map E.toLinearMap) := by
      ext x y
      change form (E ((E.submoduleMap S).symm x).val)
        (E ((E.submoduleMap S).symm y).val) = form x.val y.val
      rw [LinearEquiv.submoduleMap_symm_apply, LinearEquiv.submoduleMap_symm_apply,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rwa [hb] at h
  refine ⟨?_, hP ▸ hN⟩
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have hc := card_pointCoordinateSubspace E A hAV
  rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_zmod, hcard] at hc
  exact hc

omit [Finite G] in
theorem exists_plane_chart
    (f : Automizer V →* Atlas.G2.Model K) (E : Additive V ≃ₗ[K] W)
    (he : ∀ a v, E (automizerRepresentation V a v) = rho (f a) (E v))
    (hd : commutator (Atlas.G2.Model K) ≤ f.range)
    (A : Subgroup G) (hAV : A ≤ V) (hcard : Nat.card A = 4)
    (hn : ((UnitaryGeometry.markedForm E).restrict
      (UnitaryGeometry.ambientSpace (V := V) A)).Nondegenerate) :
    ∃ (f' : Automizer V →* Atlas.G2.Model K) (E' : Additive V ≃ₗ[K] W),
      (∀ a v, E' (automizerRepresentation V a v) = rho (f' a) (E' v)) ∧
      commutator (Atlas.G2.Model K) ≤ f'.range ∧
      pointCoordinateSubspace E' A = plane ∧
      UnitaryGeometry.markedForm E' = UnitaryGeometry.markedForm E := by
  obtain ⟨hfin, hnon⟩ := coordinate_plane_nondegenerate E A hAV hcard hn
  obtain ⟨g, hg⟩ := nondegenerate_plane_transitive (pointCoordinateSubspace E A) hfin hnon
  let f' := (MulAut.conj g).toMonoidHom.comp f
  let eg : W ≃ₗ[K] W := LinearEquiv.ofBijective (rho g) (rho.apply_bijective g)
  let E' := E.trans eg
  refine ⟨f', E', ?_, ?_, ?_, ?_⟩
  · intro a v
    change rho g (E (automizerRepresentation V a v)) = rho (g * f a * g⁻¹) (rho g (E v))
    rw [he]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  · have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hd
    have hcomm : (commutator (Atlas.G2.Model K)).map (MulAut.conj g).toMonoidHom =
        commutator (Atlas.G2.Model K) := Subgroup.Normal.map_conj_eq _ g
    rw [hcomm] at hh
    simpa only [f', MonoidHom.range_comp] using hh
  · have hh : pointCoordinateSubspace E' A =
        (pointCoordinateSubspace E A).map (rho g) := by
      ext w
      obtain ⟨v, rfl⟩ := E'.surjective w
      rw [mem_pointCoordinateSubspace]
      constructor
      · intro hv
        exact ⟨E v, (mem_pointCoordinateSubspace E A v).mpr hv, rfl⟩
      · rintro ⟨z, hz, hze⟩
        have hzv : z = E v := eg.injective hze
        exact (mem_pointCoordinateSubspace E A v).mp (hzv ▸ hz)
    exact hh.trans hg
  · ext v w
    exact form_invariant g (E v) (E w)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
