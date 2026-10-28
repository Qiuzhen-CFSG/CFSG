module
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator

/-!
# Simultaneous point, Sylow and root coordinates for the natural constituent

A nonzero fixed vector and a nonidentity element of its SL₂(4) stabilizer
can be marked as the binary point and upper-1 root. A scalar multiple of a
determinant-one basis change preserves the point while normalizing the root.
A four-group fixing that point is then the full upper root group. Its
normalizer preserves the F₄-line and contains the displayed diagonal cubic.

These are the coordinate choices in Aschbacher–Smith, Lemma 14.4.10,
combined manuscript of 1 March 2004, printed pp.1010–1011. The application
in Geometry retains the actual component quotient and subgroup placements.
-/

open Representation.SL2FourNatural Representation.BinaryOffender
open Subgroup
@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Geometry.Model
abbrev e1 : V := ![1, 0]
def fixer (p : V) : Subgroup SL where
  carrier := {g | action g p = p}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change action g p = p at hg
    change action h p = p at hh
    change action (g * h) p = p
    simpa only [map_mul, LinearEquiv.mul_apply, hh] using hg
  inv_mem' := by
    intro g hg
    apply (action g).injective
    simpa using hg.symm
private lemma fixer_members (g : SL) : g ∈ fixer e1 ↔ ∃ a : F, g = upper a := by
  constructor
  · intro hg
    change action g e1 = e1 at hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp only [action_apply, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_one, mul_zero, add_zero] at h0 h1
    have hd := g.property
    rw [Matrix.det_fin_two, h0, h1] at hd
    simp only [one_mul, mul_zero, sub_zero] at hd
    refine ⟨g 0 1, ?_⟩
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> simp [upper, h0, h1, hd]
  · rintro ⟨a, rfl⟩
    change action (upper a) e1 = e1
    simp [upper_action, e1]
private lemma fixer_card : Nat.card (fixer e1) = 4 := by
  let e : F ≃ fixer e1 :=
    { toFun := fun a => ⟨upper a, (fixer_members _).mpr ⟨a, rfl⟩⟩
      invFun := fun g => g.val 0 1
      left_inv := fun a => rfl
      right_inv := by
        intro g
        obtain ⟨a, ha⟩ := (fixer_members g.val).mp g.property
        apply Subtype.ext
        simp only [ha]
        rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, card_field]
private lemma fixed_root (g : SL) (hg : action g e1 = e1) : ∃ a : F, g = upper a :=
  (fixer_members g).mp hg
private lemma diagonal_data (a : F) (ha : a ≠ 0) :
    ∃ b : SL, a • action b e1 = e1 ∧ b * upper 1 * b⁻¹ = upper a := by
  have hd : ( !![a ^ 2, 0; 0, a] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    revert ha a
    decide +kernel
  refine ⟨⟨!![a ^ 2, 0; 0, a], hd⟩, ?_, ?_⟩ <;> revert hd ha a <;> decide +kernel
private lemma cubic_conj_upper (a : F) :
    ∃ b : F, PointCommutator.cubic * upper a * PointCommutator.cubic⁻¹ = upper b := by
  revert a
  decide +kernel
private lemma cubic_inv_conj_upper (a : F) :
    ∃ b : F, PointCommutator.cubic⁻¹ * upper a * PointCommutator.cubic = upper b := by
  revert a
  decide +kernel
lemma cubic_normalizes : PointCommutator.cubic ∈ normalizer (fixer e1 : Set SL) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨a, rfl⟩ := (fixer_members g).mp hg
    exact (fixer_members _).mpr (cubic_conj_upper a)
  · intro hg
    obtain ⟨a, ha⟩ := (fixer_members _).mp hg
    obtain ⟨b, hb⟩ := cubic_inv_conj_upper a
    apply (fixer_members _).mpr
    refine ⟨b, ?_⟩
    rw [← hb, ← ha]
    group
private lemma fixed_of_mem (v : V) (hv : v ∈ upperFixed) (g : SL) (hg : g ∈ fixer e1) :
    action g v = v := by
  obtain ⟨a, rfl⟩ := (fixer_members g).mp hg
  exact (upper_fixed_iff v).mpr ((mem_upperFixed v).mp hv) a
private lemma normalizer_preserves (g : SL) (hg : g ∈ normalizer (fixer e1 : Set SL))
    (v : V) (hv : v ∈ upperFixed) : action g v ∈ upperFixed := by
  apply (mem_upperFixed _).mpr
  apply (upper_fixed_iff _).mp
  intro a
  have hconj : g⁻¹ * upper a * g ∈ fixer e1 := by
    have hh := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) (upper a)).mp
      ((fixer_members _).mpr ⟨a, rfl⟩)
    simpa only [inv_inv] using hh
  have hf := fixed_of_mem v hv _ hconj
  calc
    action (upper a) (action g v) = action g (action (g⁻¹ * upper a * g) v) := by
      change (action (upper a) * action g) v = (action g * action (g⁻¹ * upper a * g)) v
      rw [← map_mul, ← map_mul]
      exact congrArg (fun z : SL => action z v) (by group)
    _ = action g v := by rw [hf]
lemma normalizer_stabilizes : normalizer (fixer e1 : Set SL) ≤
    subspaceStabilizer PointCommutator.representation upperFixed := by
  intro g hg v
  change action g v ∈ upperFixed ↔ v ∈ upperFixed
  constructor
  · intro hv
    have hh := normalizer_preserves g⁻¹ (Subgroup.inv_mem _ hg) (action g v) hv
    simpa using hh
  · exact normalizer_preserves g hg v
/-- A scalar multiple of a determinant-one basis change. -/
noncomputable def rebase (b : SL) (c : F) (hc : c ≠ 0) : V ≃ₗ[ZMod 2] V :=
  ((Matrix.SpecialLinearGroup.toLin' b).trans (LinearEquiv.smulOfNeZero F V c hc)).restrictScalars _
lemma rebase_apply (b : SL) (c : F) (hc : c ≠ 0) (v : V) :
    rebase b c hc v = c • action b v := rfl
lemma rebase_equivariant (b g : SL) (c : F) (hc : c ≠ 0) (v : V) :
    action g (rebase b c hc v) = rebase b c hc (action (b⁻¹ * g * b) v) := by
  rw [rebase_apply, rebase_apply]
  have hs := (Matrix.SpecialLinearGroup.toLin' g).map_smul c (action b v)
  change action g (c • action b v) = c • action g (action b v) at hs
  rw [hs]
  apply congrArg (fun w : V => c • w)
  change (action g * action b) v = (action b * action (b⁻¹ * g * b)) v
  rw [← map_mul, ← map_mul]
  exact congrArg (fun z : SL => action z v) (by group)
lemma exists_frame (p : V) (hp : p ≠ 0) (r : SL)
    (hr : action r p = p) (hne : r ≠ 1) :
    ∃ (b : SL) (c : F) (hc : c ≠ 0),
      rebase b c hc e1 = p ∧ b * upper 1 * b⁻¹ = r := by
  obtain ⟨s, hs⟩ := exists_first_column p hp
  have hf : action (s⁻¹ * r * s) e1 = e1 := by
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [hs, hr, ← hs]
    simp
  obtain ⟨a, ha⟩ := fixed_root _ hf
  have hn : a ≠ 0 := by
    intro hz
    have hzero : upper (0 : F) = 1 := by decide +kernel
    rw [hz, hzero] at ha
    apply hne
    calc
      r = s * (s⁻¹ * r * s) * s⁻¹ := by group
      _ = 1 := by rw [ha]; group
  obtain ⟨d, hd, hdr⟩ := diagonal_data a hn
  refine ⟨s * d, a, hn, ?_, ?_⟩
  · rw [rebase_apply, map_mul, LinearEquiv.mul_apply]
    change a • Matrix.SpecialLinearGroup.toLin' s (action d e1) = p
    rw [← map_smul, hd]
    exact hs
  · calc
      (s * d) * upper 1 * (s * d)⁻¹ = s * (d * upper 1 * d⁻¹) * s⁻¹ := by group
      _ = s * upper a * s⁻¹ := by rw [hdr]
      _ = r := by rw [← ha]; group

lemma point_mem_iff (v : V) : v ∈ PointCommutator.point ↔ v = 0 ∨ v = e1 := by
  change v ∈ upperFixed ⊓ fieldFixed ↔ _
  simp only [Submodule.mem_inf, mem_upperFixed, mem_fieldFixed]
  revert v
  decide +kernel
lemma frame_sylow (p : V) (b : SL) (c : F) (hc : c ≠ 0)
    (hb : rebase b c hc e1 = p) (P : Subgroup SL)
    (hP : ∀ g ∈ P, action g p = p) (hcard : Nat.card P = 4) :
    P.map (MulAut.conj b⁻¹).toMonoidHom = fixer e1 := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, hg, rfl⟩
    change action (b⁻¹ * g * b⁻¹⁻¹) e1 = e1
    rw [inv_inv]
    apply (rebase b c hc).injective
    rw [← rebase_equivariant, hb, hP g hg]
  · rw [Subgroup.card_map_of_injective (MulAut.conj b⁻¹).injective, fixer_card, hcard]

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Geometry.Model
