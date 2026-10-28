module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFiveActors.Radical
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Source radical hyperplanes and their four equal module spaces

The marked comparison takes U and its polar annihilator in V₂ to the
coordinate pair U × ann(U). Transporting the fixed and actual commutator
spaces gives the four equalities and dimension five for every hyperplane
of the source radical.

Source: Aschbacher–Smith H.9.2(4), printed pp.390–391.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFiveActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 5 M V)

/-- The literal source sum U ⊕ (V₂ ∩ Uᗮ), using the unique source form. -/
noncomputable def radicalSpace (U : Submodule (ZMod 2) S.natural) :
    Submodule (ZMod 2) V :=
  U.map S.natural.subtype ⊔
    S.dual ⊓ LinearMap.BilinForm.orthogonal S.quadratic.polarBilin (U.map S.natural.subtype)

/-- The displayed source sum is a direct sum. -/
theorem radicalSpace_disjoint (U : Submodule (ZMod 2) S.natural) :
    Disjoint (U.map S.natural.subtype)
      (S.dual ⊓ LinearMap.BilinForm.orthogonal S.quadratic.polarBilin (U.map S.natural.subtype)) :=
  S.complement.disjoint.mono (Submodule.map_subtype_le _ _) inf_le_left

private theorem polar_natural (u : S.natural) (v : V) :
    S.quadratic.polarBilin (u : V) v = (S.model.coordinates v).2 (S.naturalCoordinates u) := by
  calc
    S.quadratic.polarBilin (u : V) v =
        BinaryNaturalDual.quadratic.polarBilin (S.model.coordinates u) (S.model.coordinates v) := by
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
        S.quadratic_apply, map_add]
    _ = _ := by
      rw [S.model.natural_marking, BinaryNaturalDual.polar_apply]
      simp only [LinearMap.zero_apply, zero_add]

theorem mem_orthogonal_iff (U : Submodule (ZMod 2) S.natural) (v : V) :
    v ∈ LinearMap.BilinForm.orthogonal S.quadratic.polarBilin (U.map S.natural.subtype) ↔
      (S.model.coordinates v).2 ∈ (coordinateSpace S U).dualAnnihilator := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_dualAnnihilator]
  constructor
  · intro h x hx
    obtain ⟨u,hu,rfl⟩ := hx
    exact (polar_natural S u v).symm.trans (h u (Submodule.mem_map_of_mem hu))
  · intro h w hw
    obtain ⟨u,hu,rfl⟩ := hw
    exact (polar_natural S u v).trans (h _ (Submodule.mem_map_of_mem hu))

theorem radicalSpace_map (U : Submodule (ZMod 2) S.natural) :
    (radicalSpace S U).map S.model.coordinates.toLinearMap =
      (coordinateSpace S U).prod (coordinateSpace S U).dualAnnihilator := by
  have hd (v : V) : v ∈ S.dual ↔ (S.model.coordinates v).1 = 0 :=
    MarkedGeometry.mem_dual_iff_of_marking S.model.coordinates S.model.dualCoordinates
      S.model.dual_marking v
  ext z
  constructor
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨u,hu,rfl⟩ := hu
    change (S.model.coordinates ((u : V) + w)).1 ∈ coordinateSpace S U ∧
      (S.model.coordinates ((u : V) + w)).2 ∈ (coordinateSpace S U).dualAnnihilator
    rw [map_add, S.model.natural_marking]
    simp only [Prod.fst_add, Prod.snd_add, (hd w).mp hw.1, add_zero, zero_add]
    exact ⟨Submodule.mem_map_of_mem hu, (mem_orthogonal_iff S U w).mp hw.2⟩
  · intro hz
    obtain ⟨u,hu,he⟩ := hz.1
    let w := S.model.dualCoordinates.symm z.2
    have hw : S.model.coordinates (w : V) = (0,z.2) := by
      rw [S.model.dual_marking, S.model.dualCoordinates.apply_symm_apply]
    refine ⟨(u : V) + w, Submodule.mem_sup.mpr ⟨u, Submodule.mem_map_of_mem hu,
      w, ⟨w.property, ?_⟩, rfl⟩, ?_⟩
    · apply (mem_orthogonal_iff S U (w : V)).mpr
      rw [hw]
      exact hz.2
    · change S.model.coordinates ((u : V) + w) = z
      rw [map_add, S.model.natural_marking, hw]
      exact Prod.ext (by simpa using he) (by simp)

/-- All four source fixed/commutator spaces are the same literal polar sum. -/
theorem hyperplane_formulas (U : Submodule (ZMod 2) S.natural)
    (hU : Module.finrank (ZMod 2) U = 3) (A : Subgroup M)
    (hA : A ≤ radical S U) (hidx : A.relIndex (radical S U) = 2) :
    S.fixed A = commutator S ⊤ A ∧
      commutator S ⊤ A = S.fixed (radical S U) ∧
      S.fixed (radical S U) = commutator S ⊤ (radical S U) ∧
      commutator S ⊤ (radical S U) = radicalSpace S U ∧
      Module.finrank (ZMod 2) (S.fixed A) = 5 := by
  let A' := A.map S.model.group.toMonoidHom
  have hA' : A' ≤ BinaryNaturalDual.FiveActors.radicalActor (coordinateSpace S U) := by
    rw [← radical_map]
    exact Subgroup.map_mono hA
  have hi : A'.relIndex (BinaryNaturalDual.FiveActors.radicalActor (coordinateSpace S U)) = 2 := by
    rw [← radical_map, Subgroup.relIndex_map_map_of_injective _ _ S.model.group.injective]
    exact hidx
  have hU' := (coordinateSpace_finrank S U).trans hU
  obtain ⟨h₁,h₂,h₃,h₄⟩ := BinaryNaturalDual.FiveActors.hyperplane_radical_formulas
    (AutomorphismModel.coordinateAction S.degree) _ hU' A' hA' hi
  have htop : (⊤ : Submodule (ZMod 2) V).map S.model.coordinates.toLinearMap = ⊤ := by simp
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply Submodule.map_injective_of_injective S.model.coordinates.injective
    rw [S.fixed_map, commutator_map, htop]
    exact h₁
  · apply Submodule.map_injective_of_injective S.model.coordinates.injective
    rw [commutator_map, htop, S.fixed_map, radical_map]
    exact h₂
  · apply Submodule.map_injective_of_injective S.model.coordinates.injective
    rw [S.fixed_map, commutator_map, htop, radical_map]
    exact h₃
  · apply Submodule.map_injective_of_injective S.model.coordinates.injective
    rw [commutator_map, htop, radical_map, radicalSpace_map]
    exact h₄
  · rw [S.fixed_finrank]
    exact BinaryNaturalDual.FiveActors.finrank_fixedSpace_radicalActor_hyperplane
      (AutomorphismModel.coordinateAction S.degree) _ hU' A' hA' hi

end CFSG.Quasithin.ChapterH.NaturalDual.SourceFiveActors
