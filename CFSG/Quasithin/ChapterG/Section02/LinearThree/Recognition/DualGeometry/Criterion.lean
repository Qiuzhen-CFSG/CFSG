module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.PointMap

/-!
# All root clauses for the dual G.2.5 geometry

The ambient marked-root calculation supplies displacement into the first
pair image and fixation of that image. Concrete flag transitivity transports
these bounds to every incident point-plane pair. Equivariance and disjointness
then force fixation of every other point image in the axis. This verifies
every field of the source projective criterion on the actual binary section.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1–4 and G.2.5, printed pp.327–328,335–336.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
open Subgroup Setup Projective
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
namespace FlagCriterion
variable {F K V M : Type*} [Field F] [Group K] [AddCommGroup V] [Module F V]
  [AddCommGroup M] [Module (ZMod 2) M]
  (γ : Representation F K V) (ρ : Representation (ZMod 2) K M)

/-- Equivariance and one incident flag calculation imply all root clauses. -/
theorem criterion_of_flag (P : Point F V) (C : Submodule F V)
    (φ : Point F V → Submodule (ZMod 2) M)
    (ht : ∀ (A : Point F V) (B : Submodule F V),
      Module.finrank F B + 1 = Module.finrank F V → A.val ≤ B →
      ∃ x : K, P.val.map (γ x) = A.val ∧ C.map (γ x) = B)
    (he : ∀ x (A B : Point F V), B.val = A.val.map (γ x) → φ B = (φ A).map (ρ x))
    (hd : ∀ A B, A ≠ B → Disjoint (φ A) (φ B))
    (hspan : (⨆ A, φ A) = ⊤)
    (hm : ∀ k ∈ rootGroup γ P.val C, ∀ v : M, ρ k v - v ∈ φ P)
    (hf : ∀ k ∈ rootGroup γ P.val C, ∀ v ∈ φ P, ρ k v = v) :
    Criterion γ ρ φ := by
  have hall (A : Point F V) (B : Submodule F V) (hdim : Module.finrank F B + 1 = Module.finrank F V) (hAB : A.val ≤ B)
      (k : K) (hk : k ∈ rootGroup γ A.val B) :
      (∀ v : M, ρ k v - v ∈ φ A) ∧ (∀ v ∈ φ A, ρ k v = v) := by
    obtain ⟨x, hx, hC⟩ := ht A B hdim hAB
    have hroot : x⁻¹ * k * x ∈ rootGroup γ P.val C := by
      refine ⟨(root_conjugate_mem γ P A B x k hx hAB hk).1, ?_⟩
      intro v hv
      have hvB : γ x v ∈ B := hC ▸ (show γ x v ∈ C.map (γ x) from ⟨v, hv, rfl⟩)
      simp only [map_mul, Module.End.mul_apply, hk.2 _ hvB, γ.inv_self_apply]
    have hφ := he x P A hx.symm
    have hid (v : M) : ρ x (ρ (x⁻¹ * k * x) v) = ρ k (ρ x v) := by
      simp only [map_mul, Module.End.mul_apply, ρ.self_inv_apply]
    constructor
    · intro v
      rw [hφ]
      refine ⟨ρ (x⁻¹ * k * x) (ρ x⁻¹ v) - ρ x⁻¹ v, hm _ hroot _, ?_⟩
      rw [map_sub, hid, ρ.self_inv_apply]
    · intro v hv
      rw [hφ] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      rw [← hid, hf _ hroot w hw]
  refine ⟨he, ?_, ?_, hd, hspan⟩
  · intro A B hdim hAB k hk v
    exact (hall A B hdim hAB k hk).1 v
  · intro A B hdim hAB D hDB k hk v hv
    by_cases hAD : A = D
    · subst D
      exact (hall A B hdim hAB k hk).2 v hv
    have hD : D.val.map (γ k) = D.val := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hk.2 z (hDB hz)]
        exact hz
      · intro hw
        exact ⟨w, hw, hk.2 w (hDB hw)⟩
    have hvD : ρ k v - v ∈ φ D := by
      apply (φ D).sub_mem _ hv
      have hh : ρ k v ∈ (φ D).map (ρ k) := ⟨v, hv, rfl⟩
      rw [← he k D D hD.symm] at hh
      exact hh
    have hz : ρ k v - v = 0 :=
      (Submodule.disjoint_def.mp (hd A D hAD)) _ ((hall A B hdim hAB k hk).1 v) hvD
    exact sub_eq_zero.mp hz

end FlagCriterion
namespace PointMap
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {hLI : D.L ≤ I D g h} (e : StarComparison D g h hLI)
  (σ : Representation (ZMod 2) (D.star D.L) M)
  (s : Representation.BinaryConjugationSection (I D g h) (S₃ D g h) (S₂ D g h)
    (σ.comp e.projection))

/-- The printed root calculation on the actual binary section. -/
theorem marked_root (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hrad : UpperRadicalIdentification d e) (a : D.star D.L)
    (ha : a ∈ rootGroup (dualAction d) (dualPoint d).val d.point.dualAnnihilator) :
    (∀ v : M, σ a v - v ∈ mark d e σ s 0 1) ∧
      (∀ v ∈ mark d e σ s 0 1, σ a v = v) := by
  change a ∈ rootGroup (dualAction d) (pairPlane d).dualAnnihilator d.point.dualAnnihilator at ha
  rw [← dual_rootGroup] at ha
  have hu : a ∈ rootGroup (naturalAction d) d.point d.point :=
    ⟨ha.1, fun v hv => ha.2 v (Submodule.mem_sup_left hv)⟩
  rw [← hrad] at hu
  obtain ⟨u, hu, rfl⟩ := hu
  have hpoint := ModelGeometry.marked_root_stabilizes_second d (e.projection u) ha
  have hpart : (u : G) ∈ pointFixingPart D g :=
    ⟨hu, conjugatePoint_normalizes d hUT e u ⟨g, d.g_mem⟩ hpoint⟩
  obtain ⟨_, hm, hfix, _⟩ := pointFixingPart_root_step d hUT hf hLI hU hUg
  rw [commutator_comm] at hm hfix
  have hmark : mark d e σ s 0 1 =
      SectionGeometry.image s (W D g h ⊓ conjugate (W D g h) g) := by
    rw [mark, (frameW_values d hLI).1, (frameW_values d hLI).2.1]
  rw [hmark]
  exact ⟨SectionGeometry.moved_mem_image s _ _ hm u hpart,
    SectionGeometry.fixes_image s _ _ hfix u hpart⟩

/-- Every field of the genuine dual projective recognition criterion, derived
from the ambient root calculation and the concrete SL₃ flag geometry. -/
theorem criterion (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hrad : UpperRadicalIdentification d e) :
    Criterion (dualAction d) σ (map d e σ s) := by
  refine FlagCriterion.criterion_of_flag (dualAction d) σ (dualPoint d) d.point.dualAnnihilator
    (map d e σ s) ?_ (equivariant d e σ s hUT hf hrad)
    (disjoint d e σ s hUT hf hrad) (spanning d e σ s hUT hf hrad) ?_ ?_
  · intro A B hdim hAB
    have hV : Module.finrank F (Module.Dual F (Fin 3 → F)) = 3 := by simp
    have hB : Module.finrank F B = 2 := by omega
    apply ModelGeometry.dual_exists_flag_map d (dualPoint d) A d.point.dualAnnihilator B
    · rw [Subspace.finrank_dualAnnihilator, d.point_dimension]
      simp
    · exact hB
    · exact Subspace.dualAnnihilator_le_dualAnnihilator_iff.mpr
        (show d.point ≤ pairPlane d from le_sup_left)
    · exact hAB
  · intro a ha v
    rw [mark_eq d e σ s hUT hf hrad]
    exact (marked_root d e σ s hUT hf hU hUg hrad a ha).1 v
  · intro a ha v hv
    rw [mark_eq d e σ s hUT hf hrad] at hv
    exact (marked_root d e σ s hUT hf hU hUg hrad a ha).2 v hv
end PointMap

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
