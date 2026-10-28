module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Marked
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Point

/-!
# Quadratic actors in the two Hermitian tensor radicals

For parameters (a,b) and (c,d), quadraticity forces the two diagonal
Hermitian pairings and the mixed pairing to vanish. For the plane radical,
apply the second displacement to the last diagonal matrix unit. For the
point radical, use the two lower diagonal units and a lower off-diagonal
entry of trace one. Fixing a nonzero parameter makes division by one of
its coordinates an injection of the actor into the actual fixed field.
Thus every nontrivial quadratic subgroup of either radical has at most
2^n elements, and an elementary actor in the marked unitriangular image
has rank at most n.

These computations use the literal action X ↦ g X σ(g)ᵀ. They do not
identify the fixed-space centralizer in H.4.4(2) with the moved-space
centralizer: the root has moved dimension 4n and fixed dimension 5n.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.4,
printed pp.455–456/PDF pp.466–467.
-/

@[expose] public section

open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender Matrix.PSL3Even.UnipotentGeometry
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Tensor
variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

omit M hM [NeZero n] in
private theorem scalar_fixed_of_pair (a c : E n) (ha : a ≠ 0)
    (h : a * sigma n c = c * sigma n a) : sigma n (c / a) = c / a := by
  rw [map_div₀]
  apply (div_eq_div_iff ((map_ne_zero (sigma n)).mpr ha) ha).mpr
  simpa only [mul_comm] using h

omit M hM in
private theorem card_le_of_hermitian_pairs {P : Type*} (f : P → E n × E n)
    (hf : Function.Injective f) (u : P) (hu : f u ≠ 0)
    (hp : ∀ v : P,
      (f u).1 * sigma n (f v).1 = (f v).1 * sigma n (f u).1 ∧
      (f u).2 * sigma n (f v).2 = (f v).2 * sigma n (f u).2 ∧
      (f u).1 * sigma n (f v).2 = (f v).1 * sigma n (f u).2) :
    Nat.card P ≤ 2 ^ n := by
  by_cases ha : (f u).1 = 0
  · have hb : (f u).2 ≠ 0 := by
      intro hb
      exact hu (Prod.ext ha hb)
    let t : P → F n := fun v => ⟨(f v).2 / (f u).2,
      scalar_fixed_of_pair n _ _ hb (hp v).2.1⟩
    have ht : Function.Injective t := by
      intro v w hvw
      have hvw2 : (f v).2 = (f w).2 :=
        (div_left_inj' hb).mp (congrArg Subtype.val hvw)
      have hv1 : (f v).1 = 0 := by
        have h := (hp v).2.2
        rw [ha, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_right ((map_ne_zero (sigma n)).mpr hb)
      have hw1 : (f w).1 = 0 := by
        have h := (hp w).2.2
        rw [ha, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_right ((map_ne_zero (sigma n)).mpr hb)
      exact hf (Prod.ext (hv1.trans hw1.symm) hvw2)
    exact (Nat.card_le_card_of_injective t ht).trans_eq (card_F n)
  · let t : P → F n := fun v => ⟨(f v).1 / (f u).1,
      scalar_fixed_of_pair n _ _ ha (hp v).1⟩
    have ht : Function.Injective t := by
      intro v w hvw
      have hvw1 : (f v).1 = (f w).1 :=
        (div_left_inj' ha).mp (congrArg Subtype.val hvw)
      have hvw2 : (f v).2 = (f w).2 := by
        apply (sigma n).injective
        apply mul_left_cancel₀ ha
        rw [(hp v).2.2, (hp w).2.2, hvw1]
      exact hf (Prod.ext hvw1 hvw2)
    exact (Nat.card_le_card_of_injective t ht).trans_eq (card_F n)

/-- The last diagonal test vector detects all three plane parameter equations. -/
theorem plane_quadratic_pair (A : Subgroup M)
    (hq : IsQuadratic (overgroupAction n M) A) (a b c d : E n)
    (hab : coverToOvergroup n M hM (planeElement n a b) ∈ A)
    (hcd : coverToOvergroup n M hM (planeElement n c d) ∈ A) :
    a * sigma n c = c * sigma n a ∧ b * sigma n d = d * sigma n b ∧
      a * sigma n d = c * sigma n b := by
  let X : Space n := (Representation.HermitianTensorThree.coordinates n).symm
    (![0,0,1], ![0,0,0])
  have h : action n (planeElement n a b) (action n (planeElement n c d) X - X) =
      action n (planeElement n c d) X - X := hq _ hab _ hcd X
  have h11 := congrArg (fun Y : Space n => Y.val 1 1) h
  have h00 := congrArg (fun Y : Space n => Y.val 0 0) h
  have h10 := congrArg (fun Y : Space n => Y.val 1 0) h
  simp [action_apply, planeElement_matrix, adjoint, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_three, X, Representation.HermitianTensorThree.coordinates] at h11 h00 h10
  refine ⟨?_, ?_, ?_⟩
  · apply CharTwo.add_eq_zero.mp
    linear_combination h11
  · apply CharTwo.add_eq_zero.mp
    linear_combination h00
  · apply CharTwo.add_eq_zero.mp
    linear_combination h10

/-- Trace-one off-diagonal test vectors detect the mixed point parameter equation. -/
theorem point_quadratic_pair (A : Subgroup M)
    (hq : IsQuadratic (overgroupAction n M) A) (a b c d : E n)
    (hab : coverToOvergroup n M hM (pointElement n a b) ∈ A)
    (hcd : coverToOvergroup n M hM (pointElement n c d) ∈ A) :
    a * sigma n c = c * sigma n a ∧ b * sigma n d = d * sigma n b ∧
      a * sigma n d = c * sigma n b := by
  have h (X : Space n) :
      (action n (pointElement n a b) (action n (pointElement n c d) X - X)).val 0 0 =
      (action n (pointElement n c d) X - X).val 0 0 :=
    congrArg (fun Y : Space n => Y.val 0 0) (hq _ hab _ hcd X)
  have h11 := h ((Representation.HermitianTensorThree.coordinates n).symm
    (![0,1,0], ![0,0,0]))
  have h22 := h ((Representation.HermitianTensorThree.coordinates n).symm
    (![0,0,1], ![0,0,0]))
  have hm (t : E n) := h ((Representation.HermitianTensorThree.coordinates n).symm
    (![0,0,0], ![0,0,t]))
  simp [action_apply, pointElement_matrix, adjoint, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_three, Representation.HermitianTensorThree.coordinates] at h11 h22 hm
  refine ⟨?_, ?_, ?_⟩
  · apply CharTwo.add_eq_zero.mp
    linear_combination h11
  · apply CharTwo.add_eq_zero.mp
    linear_combination h22
  · obtain ⟨t,ht⟩ := FieldSections.exists_trace_one n
    apply CharTwo.add_eq_zero.mp
    have hm1 := hm 1
    simp only [map_one, mul_one] at hm1
    linear_combination (norm := ring_nf) -hm t + sigma n t * hm1 - (a * sigma n d + c * sigma n b) * ht
    simp [CharTwo.two_eq_zero]

omit M hM in
private theorem card_le_of_radical_params {G : Type*} [Group G]
    (A : Subgroup G) (hne : A ≠ ⊥) (f : E n × E n → G) (hzero : f 0 = 1)
    (hcover : ∀ g : A, ∃ p, f p = g)
    (hpair : ∀ u v, f u ∈ A → f v ∈ A →
      u.1 * sigma n v.1 = v.1 * sigma n u.1 ∧
      u.2 * sigma n v.2 = v.2 * sigma n u.2 ∧
      u.1 * sigma n v.2 = v.1 * sigma n u.2) : Nat.card A ≤ 2 ^ n := by
  choose c hc using hcover
  have hinj : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    rw [← hc x, ← hc y, hxy]
  obtain ⟨u,hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hcu : c u ≠ 0 := by
    intro hcu
    apply hu
    apply Subtype.ext
    rw [← hc u, hcu, hzero]
    rfl
  apply card_le_of_hermitian_pairs n c hinj u hcu
  intro v
  apply hpair
  · rw [hc u]; exact u.property
  · rw [hc v]; exact v.property

theorem card_quadratic_le_point (A : Subgroup M) (hA : A ≠ ⊥)
    (hAP : A ≤ pointActor n M hM) (hq : IsQuadratic (overgroupAction n M) A) :
    Nat.card A ≤ 2 ^ n := by
  apply card_le_of_radical_params n A hA
    (fun p => coverToOvergroup n M hM (pointElement n p.1 p.2))
  · change unipotentToOvergroup n M hM 1 = 1
    exact map_one _
  · intro g
    obtain ⟨a,b,hab⟩ := (pointActor_elements n M hM g).mp (hAP g.property)
    exact ⟨(a,b),hab⟩
  · intro u v hu hv
    exact point_quadratic_pair n M hM A hq u.1 u.2 v.1 v.2 hu hv

theorem card_quadratic_le_plane (A : Subgroup M) (hA : A ≠ ⊥)
    (hAP : A ≤ planeActor n M hM) (hq : IsQuadratic (overgroupAction n M) A) :
    Nat.card A ≤ 2 ^ n := by
  apply card_le_of_radical_params n A hA
    (fun p => coverToOvergroup n M hM (planeElement n p.1 p.2))
  · change unipotentToOvergroup n M hM 1 = 1
    exact map_one _
  · intro g
    obtain ⟨a,b,hab⟩ := (planeActor_elements n M hM g).mp (hAP g.property)
    exact ⟨(a,b),hab⟩
  · intro u v hu hv
    exact plane_quadratic_pair n M hM A hq u.1 u.2 v.1 v.2 hu hv

/-- The two radical alternatives exhaust elementary actors in the marked image. -/
theorem quadratic_rank_le_of_le_unipotent (A : Subgroup M) (hA : IsElementaryTwo A)
    (hAU : A ≤ unipotentActor n M hM) (hq : IsQuadratic (overgroupAction n M) A) :
    rank A ≤ n := by
  have hc : Nat.card A ≤ 2 ^ n := by
    rcases elementary_le_radical n M hM A hA hAU with hp | hp
    · exact card_quadratic_le_point n M hM A hA.1 hp hq
    · exact card_quadratic_le_plane n M hM A hA.1 hp hq
  rw [hA.card_eq_two_pow_rank] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

end CFSG.Quasithin.ChapterK.Linear.Tensor
