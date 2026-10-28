module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.NaturalGeometry.PointMap

/-!
# Every root clause for the natural upper G.2.5 point map

The earlier point-radical identification lifts its actors to U. The
normalization bound gives [U,S]≤W, while the Frattini bound gives
[U,W]≤V₁≤S₃. These are the displacement and fixed-space conditions at
the marked point. Conjugating a root to that point proves the general
displacement bound and fixes its center image. Equivariance and pairwise
disjointness then show that a root fixes every other point image in its
axis. This proves every field of the actual G.1.3 criterion.

`UpperRadicalIdentification` is exactly the earlier G.2.5(1) input on the
compatible projection, supplied by qt-g025-structure. It is not a module
recognition assumption. The earlier structural inputs are discharged by
qt-g02-linear-three; full I-invariance is discharged by qt-g025-recognition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.3–4, printed pp.327–328, and G.2.5(7), printed pp.335–336.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
variable {F K V M : Type*} [Field F] [Group K] [AddCommGroup V] [Module F V]
  [AddCommGroup M] [Module (ZMod 2) M]
  (γ : Representation F K V) (ρ : Representation (ZMod 2) K M)

/-- Conjugating a root to a chosen point gives an element of its full point radical. -/
theorem root_conjugate_mem (P A : Point F V) (B : Submodule F V)
    (x k : K) (hx : P.val.map (γ x) = A.val) (hAB : A.val ≤ B)
    (hk : k ∈ rootGroup γ A.val B) :
    x⁻¹ * k * x ∈ rootGroup γ P.val P.val := by
  constructor
  · intro v
    have hd := hk.1 (γ x v)
    rw [← hx] at hd
    obtain ⟨w, hw, he⟩ := hd
    have he' := congrArg (γ x⁻¹) he
    simp only [map_sub, γ.inv_self_apply] at he'
    change γ (x⁻¹ * k * x) v - v ∈ P.val
    rw [map_mul, map_mul]
    change γ x⁻¹ (γ k (γ x v)) - v ∈ P.val
    rw [← he']
    exact hw
  · intro v hv
    have hvA : γ x v ∈ A.val := hx ▸ (show γ x v ∈ P.val.map (γ x) from ⟨v, hv, rfl⟩)
    simp only [map_mul, Module.End.mul_apply, hk.2 _ (hAB hvA), γ.inv_self_apply]

/-- The global root clauses follow from the point radical at a single mark,
equivariance and disjointness. No flag-transitivity premise is needed. -/
theorem criterion_of_point_radical (P : Point F V)
    (φ : Point F V → Submodule (ZMod 2) M)
    (ht : ∀ A : Point F V, ∃ x : K, P.val.map (γ x) = A.val)
    (he : ∀ x (A B : Point F V), B.val = A.val.map (γ x) → φ B = (φ A).map (ρ x))
    (hd : ∀ A B, A ≠ B → Disjoint (φ A) (φ B))
    (hspan : (⨆ A, φ A) = ⊤)
    (hm : ∀ k ∈ rootGroup γ P.val P.val, ∀ v : M, ρ k v - v ∈ φ P)
    (hf : ∀ k ∈ rootGroup γ P.val P.val, ∀ v ∈ φ P, ρ k v = v) :
    Criterion γ ρ φ := by
  have hall (A : Point F V) (B : Submodule F V) (hAB : A.val ≤ B)
      (k : K) (hk : k ∈ rootGroup γ A.val B) :
      (∀ v : M, ρ k v - v ∈ φ A) ∧ (∀ v ∈ φ A, ρ k v = v) := by
    obtain ⟨x, hx⟩ := ht A
    have hroot := root_conjugate_mem γ P A B x k hx hAB hk
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
  · intro A B _ hAB k hk v
    exact (hall A B hAB k hk).1 v
  · intro A B _ hAB D hDB k hk v hv
    by_cases hAD : A = D
    · subst D
      exact (hall A B hAB k hk).2 v hv
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
      (Submodule.disjoint_def.mp (hd A D hAD)) _ ((hall A B hAB k hk).1 v) hvD
    exact sub_eq_zero.mp hz

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.SectionGeometry
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] {H S E : Subgroup G}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {ρ : Representation (ZMod 2) H M}
  (s : Representation.BinaryConjugationSection H S E ρ)

def displacement (l : H) (a : S) : S :=
  ⟨⁅(l : G), (a : G)⁆, (S.mul_mem
    ((mem_normalizer_iff.mp (s.normalized l.property) a).mp a.property) (S.inv_mem a.property))⟩

theorem displacement_coordinates (l : H) (a : S) :
    (s.coordinates (displacement s l a)).toAdd = ρ l (s.coordinates a).toAdd - (s.coordinates a).toAdd := by
  let b : S := ⟨(l : G) * a * (l : G)⁻¹,
    (mem_normalizer_iff.mp (s.normalized l.property) a).mp a.property⟩
  change (s.coordinates (b * a⁻¹)).toAdd = _
  rw [map_mul, map_inv]
  simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
  rw [s.equivariant l a]

theorem moved_mem_image (A B : Subgroup G) (hcomm : ⁅A, S⁆ ≤ B)
    (l : H) (hl : (l : G) ∈ A) (v : M) : ρ l v - v ∈ image s B := by
  obtain ⟨a, ha⟩ := s.onto (Multiplicative.ofAdd v)
  exact (mem_image s B _).mpr ⟨displacement s l a,
    hcomm (commutator_mem_commutator hl a.property), by
      rw [displacement_coordinates, ha]; rfl⟩

theorem fixes_image (A B : Subgroup G) (hcomm : ⁅A, B⁆ ≤ E)
    (l : H) (hl : (l : G) ∈ A) (v : M) (hv : v ∈ image s B) : ρ l v = v := by
  obtain ⟨a, ha, rfl⟩ := (mem_image s B _).mp hv
  have hc := hcomm (commutator_mem_commutator hl ha)
  have he := (s.coordinates_eq_one_iff (displacement s l a)).mpr hc
  have hz : (s.coordinates (displacement s l a)).toAdd = 0 := he
  rw [displacement_coordinates] at hz
  exact sub_eq_zero.mp hz

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.SectionGeometry

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open Subgroup Projective Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {hLI : D.L ≤ I D g h} (e : StarComparison D g h hLI)
  (σ : Representation (ZMod 2) (D.star D.L) M)
  (s : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
    (σ.comp e.projection))

/-- G.2.5(1), expressed on the actual compatible quotient projection:
the image of U is the full point-parabolic radical. -/
def UpperRadicalIdentification : Prop :=
  (D.U.subgroupOf (I D g h)).map e.projection = rootGroup (naturalAction d) d.point d.point

theorem naturalPointMap_criterion (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h)
    (hrad : UpperRadicalIdentification d e) :
    Criterion (naturalAction d) σ (naturalPointMap d e σ s) := by
  apply criterion_of_point_radical (naturalAction d) σ (naturalPoint d) _
    (naturalPoint_transitive d) (naturalPointMap_equivariant d e σ s)
    (naturalPointMap_disjoint d e σ s hUT hf) (naturalPointMap_spanning d e σ s hgen)
  · intro k hk v
    rw [naturalPointMap_mark]
    change k ∈ rootGroup (naturalAction d) d.point d.point at hk
    rw [← hrad] at hk
    obtain ⟨u, hu, rfl⟩ := hk
    have hcomm : ⁅D.U, S D g h⁆ ≤ W D g h :=
      le_inf (le_normalizer_iff_commutator_le_left.mp hU)
        (le_normalizer_iff_commutator_le_right.mp
          ((show D.U ≤ I D g h from le_sup_left.trans le_sup_left).trans
            (I_normalizes_core D g h)))
    exact SectionGeometry.moved_mem_image s D.U (W D g h) hcomm u hu v
  · intro k hk v hv
    rw [naturalPointMap_mark] at hv
    change k ∈ rootGroup (naturalAction d) d.point d.point at hk
    rw [← hrad] at hk
    obtain ⟨u, hu, rfl⟩ := hk
    have hcomm : ⁅D.U, W D g h⁆ ≤ S₃ D g h :=
      (commutator_mono le_rfl inf_le_left).trans
        ((derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf).trans
          (d.setup.point_le.trans ((d.series_inclusions hUT hf hLI).1.trans
            (d.series_inclusions hUT hf hLI).2.1)))
    exact SectionGeometry.fixes_image s D.U (W D g h) hcomm u hu v hv

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
