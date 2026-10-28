import Theory.AtlasPort.LinearGroups.Symplectic.Basic
import Theory.AtlasPort.LinearAlgebra.SymplecticBasis
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
set_option warningAsError false

noncomputable section
namespace Atlas.Symplectic
variable {F : Type*} [Field F]

/-- Split the first coordinate of each half, retaining the fixed index marking. -/
def headTail (n : ℕ) : Vector (n+1) F ≃ₗ[F] (F × F) × Vector n F where
  toFun x := ((x (.inl 0),x (.inr 0)),Sum.elim (fun i => x (.inl i.succ))
    (fun i => x (.inr i.succ)))
  invFun z := Sum.elim (Fin.cases z.1.1 (fun i => z.2 (.inl i)))
    (Fin.cases z.1.2 (fun i => z.2 (.inr i)))
  left_inv x := by
    funext i
    rcases i with i|i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      cases i <;> rfl
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext i
      cases i <;> rfl
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext i
      cases i <;> rfl

theorem form_headTail {n : ℕ} (x y : Vector (n+1) F) :
    form x y = (headTail n x).1.1*(headTail n y).1.2 -
      (headTail n x).1.2*(headTail n y).1.1 + form (headTail n x).2 (headTail n y).2 := by
  simp only [form_apply, Fin.sum_univ_succ]
  rfl


/-- Every finite-dimensional nondegenerate alternating form of dimension 2n
is isometric to the retained standard matrix form. -/
theorem exists_isometry {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (n : ℕ) (B : LinearMap.BilinForm F V)
    (hA : B.IsAlt) (hB : B.Nondegenerate) (hdim : Module.finrank F V = 2*n) :
    Nonempty (B.IsometryEquiv (form (n := n) (F := F))) := by
  induction n generalizing V with
  | zero =>
    letI : Subsingleton V := Module.finrank_zero_iff.mp (by simpa using hdim)
    refine ⟨{ toLinearEquiv := LinearEquiv.ofSubsingleton (R := F) V (Vector 0 F)
              map_app' := ?_ }⟩
    intro x y
    rw [Subsingleton.elim x 0, Subsingleton.elim y 0]
    simp
  | succ n ih =>
    letI : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F V)
    obtain ⟨e,he⟩ := exists_ne (0 : V)
    obtain ⟨f,hef⟩ := Atlas.AlternatingForm.exists_partner B hB he
    let W := Atlas.AlternatingForm.complement B e f
    let C := B.restrict W
    have hC : C.IsAlt := Atlas.AlternatingForm.complement_alternating B hA e f hef
    have hCN : C.Nondegenerate :=
      Atlas.AlternatingForm.complement_nondegenerate B hA e f hef hB
    have hW : Module.finrank F W = 2*n := by
      have h := Atlas.AlternatingForm.finrank_complement B hA e f hef
      change Module.finrank F W + 2 = Module.finrank F V at h
      omega
    obtain ⟨k⟩ := ih C hC hCN hW
    let s := Atlas.AlternatingForm.split B hA e f hef
    let t : V ≃ₗ[F] Vector (n+1) F :=
      (s.trans ((LinearEquiv.refl F (F × F)).prodCongr k.toLinearEquiv)).trans
        (headTail n).symm
    refine ⟨{ toLinearEquiv := t, map_app' := ?_ }⟩
    intro x y
    change form (t x) (t y) = B x y
    rw [form_headTail]
    have ht (z : V) : headTail n (t z) = ((s z).1,k (s z).2) := by
      simp [t]
    rw [ht, ht]
    have hk := k.map_app (s y).2 (s x).2
    change form (k (s x).2) (k (s y).2) = B (s x).2.val (s y).2.val at hk
    rw [hk]
    have hb := Atlas.AlternatingForm.split_form B hA e f hef (s x) (s y)
    simpa only [s, LinearEquiv.symm_apply_apply] using hb.symm


/-- A prescribed hyperbolic pair can be the first pair of standard coordinates. -/
theorem exists_isometry_pair {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (n : ℕ) (B : LinearMap.BilinForm F V)
    (hA : B.IsAlt) (hB : B.Nondegenerate) (hdim : Module.finrank F V = 2*(n+1))
    (u v : V) (huv : B u v = 1) :
    ∃ g : B.IsometryEquiv (form (n := n+1) (F := F)),
      g u = e 0 ∧ g v = f 0 := by
  let W := Atlas.AlternatingForm.complement B u v
  let C := B.restrict W
  have hC := Atlas.AlternatingForm.complement_alternating B hA u v huv
  have hCN := Atlas.AlternatingForm.complement_nondegenerate B hA u v huv hB
  have hW : Module.finrank F W = 2*n := by
    have h := Atlas.AlternatingForm.finrank_complement B hA u v huv
    change Module.finrank F W + 2 = Module.finrank F V at h
    omega
  obtain ⟨k⟩ := exists_isometry n C hC hCN hW
  let s := Atlas.AlternatingForm.split B hA u v huv
  let t : V ≃ₗ[F] Vector (n+1) F :=
    (s.trans ((LinearEquiv.refl F (F × F)).prodCongr k.toLinearEquiv)).trans
      (headTail n).symm
  have ht (z : V) : headTail n (t z) = ((s z).1,k (s z).2) := by simp [t]
  have htB : ∀ x y, form (t x) (t y) = B x y := by
    intro x y
    rw [form_headTail, ht, ht]
    have hk := k.map_app (s y).2 (s x).2
    change form (k (s x).2) (k (s y).2) = B (s x).2.val (s y).2.val at hk
    rw [hk]
    have hb := Atlas.AlternatingForm.split_form B hA u v huv (s x) (s y)
    simpa only [s, LinearEquiv.symm_apply_apply] using hb.symm
  refine ⟨{ toLinearEquiv := t, map_app' := htB }, ?_, ?_⟩
  · change t u = e 0
    apply (headTail n).injective
    rw [ht]
    have hs : s u = ((1,0),0) := by
      apply Prod.ext
      · simp [s, Atlas.AlternatingForm.split, huv, hA.self_eq_zero]
      · apply Subtype.ext
        change u-Atlas.AlternatingForm.planeProjection B u v u=0
        rw [Atlas.AlternatingForm.projection_e B hA u v huv, sub_self]
    rw [hs]
    simp [headTail, e, Pi.single_apply]
    rfl
  · change t v = f 0
    apply (headTail n).injective
    rw [ht]
    have hs : s v = ((0,1),0) := by
      apply Prod.ext
      · simp [s, Atlas.AlternatingForm.split, huv, hA.self_eq_zero,
          Atlas.AlternatingForm.reversed_pairing B hA u v huv]
      · apply Subtype.ext
        change v-Atlas.AlternatingForm.planeProjection B u v v=0
        rw [Atlas.AlternatingForm.projection_f B hA u v huv, sub_self]
    rw [hs]
    simp [headTail, f, Pi.single_apply]
    rfl

end Atlas.Symplectic


