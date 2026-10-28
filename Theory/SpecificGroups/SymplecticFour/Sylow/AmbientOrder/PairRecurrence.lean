module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearAlgebra/SymplecticBasis.lean and
Atlas/LinearGroups/Symplectic/{Basic,Isometry,Basis,PairStabilizer,PairCount,PairAction}.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG module-compatible private implementation, distinct namespace, lint cleanup,
removed unused projective-group and transvection APIs, and matrix-carrier export.
The original sources and existing legacy ports are unchanged.
-/

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.SetTheory.Cardinal.Finite
public import Theory.AtlasPort.LinearAlgebra.LinearFunctionalFiber

/-!
# Counting a symplectic group through normalized hyperbolic pairs

Over any finite field, count pairs (u,v) with B(u,v)=1: there are q^(2n)-1
choices of u and q^(2n-1) partners. Hyperbolic splitting gives transitivity
of the actual matrix group and identifies the full pointwise pair stabilizer
with the symplectic group of rank one less. Orbit-stabilizer then gives the
order recurrence. No characteristic restriction or assumed order is used.

The private adaptation is needed because the existing symplectic Atlas ports
are legacy non-modules. Its sole export concerns Mathlib's actual matrix carrier.
Source: ATLAS files identified above; used for the Sp₄ order in
Aschbacher--Smith, F.1.12(I)(2), printed pp.262–264.
-/

noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm
open LinearMap
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (hA : B.IsAlt)

/-- Nondegeneracy supplies a normalized partner without a characteristic restriction. -/
theorem exists_partner (hB : B.Nondegenerate) {e : V} (he : e ≠ 0) :
    ∃ f, B e f = 1 := by
  obtain ⟨v,hv⟩ : ∃ v, B e v ≠ 0 := by
    by_contra! h
    exact he (hB.1 e h)
  exact ⟨(B e v)⁻¹ • v, by simp [map_smul, hv]⟩

variable (e f : V) (hef : B e f = 1)

/-- The simultaneous orthogonal complement of the selected hyperbolic pair. -/
def complement : Submodule F V := (B.flip e).ker ⊓ (B.flip f).ker

@[simp] theorem mem_complement (x : V) :
    x ∈ complement B e f ↔ B x e = 0 ∧ B x f = 0 := Iff.rfl

/-- Projection onto the selected plane, in its normalized coordinates. -/
def planeProjection : V →ₗ[F] V := (B.flip f).smulRight e - (B.flip e).smulRight f

@[simp] theorem planeProjection_apply (x : V) :
    planeProjection B e f x = (B x f) • e - (B x e) • f := rfl

include hA hef
theorem reversed_pairing : B f e = -1 := by rw [← hA.neg_eq e f, hef]

@[simp] theorem projection_e : planeProjection B e f e = e := by
  simp [planeProjection_apply, hef, hA.self_eq_zero]

@[simp] theorem projection_f : planeProjection B e f f = f := by
  simp [planeProjection_apply, reversed_pairing B hA e f hef, hA.self_eq_zero]

theorem remainder_mem (x : V) : x - planeProjection B e f x ∈ complement B e f := by
  simp only [mem_complement, planeProjection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hA.self_eq_zero,
    reversed_pairing B hA e f hef, hef]
  constructor <;> ring

/-- The hyperbolic coordinates plus the actual complement give a direct decomposition. -/
def split : V ≃ₗ[F] (F × F) × complement B e f where
  toFun x := ((B x f, -B x e), ⟨x-planeProjection B e f x, remainder_mem B hA e f hef x⟩)
  invFun z := z.1.1 • e + z.1.2 • f + z.2.val
  left_inv x := by
    simp only [planeProjection_apply, neg_smul]
    abel
  right_inv z := by
    rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
    have hw' := (mem_complement B e f w).mp hw
    apply Prod.ext
    · apply Prod.ext <;>
        simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hef, hA.self_eq_zero, reversed_pairing B hA e f hef, hw'.1, hw'.2]
    · apply Subtype.ext
      simp only [planeProjection_apply, map_add, map_smul,
        hef, hA.self_eq_zero,
        reversed_pairing B hA e f hef, hw'.1, hw'.2]
      simp
  map_add' x y := by
    apply Prod.ext
    · simp [map_add, add_comm]
    · apply Subtype.ext
      change x+y-planeProjection B e f (x+y) =
        (x-planeProjection B e f x)+(y-planeProjection B e f y)
      rw [map_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · simp [map_smul, mul_neg]
    · apply Subtype.ext
      simp [map_smul, smul_sub]

omit hef in
/-- The alternating restriction on the actual complement. -/
theorem complement_alternating : (B.restrict (complement B e f)).IsAlt := by
  intro x
  exact hA.self_eq_zero x.val

/-- Nondegeneracy survives hyperbolic splitting. -/
theorem complement_nondegenerate (hB : B.Nondegenerate) :
    (B.restrict (complement B e f)).Nondegenerate := by
  have hs : (B.restrict (complement B e f)).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hB.1 x.val
    intro y
    obtain ⟨z,rfl⟩ := (split B hA e f hef).symm.surjective y
    rcases z with ⟨⟨r,s⟩,w⟩
    have hp := x.prop
    have hz : B x.val w.val = 0 := hx w
    change B x.val (r • e + s • f + w.val) = 0
    simp [map_add, map_smul, (mem_complement B e f x.val).mp hp, hz]
  refine ⟨hs, ?_⟩
  intro x hx
  apply hs x
  intro y
  change B x.val y.val = 0
  rw [← hA.neg_eq y.val x.val]
  change -((B.restrict (complement B e f)) y x) = 0
  rw [hx y, neg_zero]

theorem finrank_complement [FiniteDimensional F V] :
    Module.finrank F (complement B e f) + 2 = Module.finrank F V := by
  have h := (split B hA e f hef).finrank_eq
  simpa [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using h.symm


/-- The decomposition is orthogonal and has the normalized hyperbolic plane form. -/
theorem split_form (z z' : (F × F) × complement B e f) :
    B ((split B hA e f hef).symm z) ((split B hA e f hef).symm z') =
      z.1.1*z'.1.2-z.1.2*z'.1.1+B z.2.val z'.2.val := by
  rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
  rcases z' with ⟨⟨t,u⟩,⟨v,hv⟩⟩
  have hw := (mem_complement B e f w).mp hw
  have hv := (mem_complement B e f v).mp hv
  have hev : B e v = 0 := by rw [← hA.neg_eq v e, hv.1, neg_zero]
  have hfv : B f v = 0 := by rw [← hA.neg_eq v f, hv.2, neg_zero]
  change B (r • e+s • f+w) (t • e+u • f+v) = r*u-s*t+B w v
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hA.self_eq_zero, hef, reversed_pairing B hA e f hef,
    hw.1, hw.2, hev, hfv]
  ring

end Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm



namespace Theory.SpecificGroups.SymplecticFour.AmbientOrderProof
open Matrix

abbrev Index (n : ℕ) := Fin n ⊕ Fin n
abbrev Vector (n : ℕ) (F : Type*) := Index n → F
abbrev Sp (n : ℕ) (F : Type*) [CommRing F] := ↥(Matrix.symplecticGroup (Fin n) F)

variable {n : ℕ} {F : Type*} [CommRing F]

/-- The form with positive pairing from the first half to the second half. -/
def form : LinearMap.BilinForm F (Vector n F) := (-Matrix.J (Fin n) F).toBilin'

theorem form_apply (x y : Vector n F) :
    form x y = ∑ i : Fin n, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i)) := by
  simp [form, Matrix.toBilin'_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type, sub_eq_add_neg, Finset.sum_add_distrib]

@[simp] theorem form_self (x : Vector n F) : form x x = 0 := by
  simp [form_apply, mul_comm]

theorem form_alternating : (form (n := n) (F := F)).IsAlt := form_self

theorem form_swap (x y : Vector n F) : form x y = -form y x := by
  simp only [form_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def e (i : Fin n) : Vector n F := Pi.single (.inl i) 1
def f (i : Fin n) : Vector n F := Pi.single (.inr i) 1

@[simp] theorem form_e_right (x : Vector n F) (i : Fin n) : form x (e i) = -x (.inr i) := by
  simp [form_apply, e, Pi.single_apply]

@[simp] theorem form_f_right (x : Vector n F) (i : Fin n) : form x (f i) = x (.inl i) := by
  simp [form_apply, f, Pi.single_apply]

theorem form_left_separating (x : Vector n F) (hx : ∀ y, form x y = 0) : x = 0 := by
  funext i
  cases i with
  | inl i => simpa only [form_f_right, Pi.zero_apply] using hx (f i)
  | inr i => simpa only [form_e_right, neg_eq_zero, Pi.zero_apply] using hx (e i)

theorem form_nondegenerate : (form (n := n) (F := F)).Nondegenerate := by
  constructor
  · exact form_left_separating
  · intro y hy
    apply form_left_separating y
    intro x
    rw [form_swap, hy x, neg_zero]

/-- The column convention preserves the same carrier, also in characteristic two. -/
theorem mem_iff_preserves {A : Matrix (Index n) (Index n) F} :
    A ∈ Matrix.symplecticGroup (Fin n) F ↔ ∀ x y, form (A *ᵥ x) (A *ᵥ y) = form x y := by
  rw [SymplecticGroup.mem_iff']
  have he : ∀ A : Matrix (Index n) (Index n) F,
      (form (n := n) (F := F)).comp A.toLin' A.toLin' = (Aᵀ * (-J (Fin n) F) * A).toBilin' :=
    fun A => Matrix.toBilin'_comp _ _ _
  constructor
  · intro h x y
    have h' : Aᵀ * (-J (Fin n) F) * A = -J (Fin n) F := by simp [h]
    have hform := he A
    rw [h'] at hform
    exact congrArg (fun B : LinearMap.BilinForm F (Vector n F) => B x y) hform
  · intro h
    have hform : (form (n := n) (F := F)).comp A.toLin' A.toLin' = form := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact h x y
    rw [he A] at hform
    have hm := Matrix.toBilin'.injective hform
    simpa [Matrix.mul_neg, Matrix.neg_mul] using hm

theorem preserves (g : Sp n F) (x y : Vector n F) :
    form ((g.val) *ᵥ x) ((g.val) *ᵥ y) = form x y := mem_iff_preserves.mp g.prop x y

theorem smul_eq_mulVec (g : Sp n F) (x : Vector n F) :
    g • x = g.val *ᵥ x := rfl

instance faithful_linear_action : FaithfulSMul (Sp n F) (Vector n F) where
  eq_of_smul_eq_smul h := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have hv := congrFun (h (Pi.single j 1)) i
    simpa [smul_eq_mulVec, Matrix.mulVec_single] using hv

def toGL : Sp n F →* Matrix.GeneralLinearGroup (Index n) F where
  toFun g := Matrix.GeneralLinearGroup.mk'' g.val (SymplecticGroup.symplectic_det g.prop)
  map_one' := by apply Units.ext; rfl
  map_mul' _ _ := by apply Units.ext; rfl

theorem toGL_injective : Function.Injective (toGL (n := n) (F := F)) := by
  intro x y h
  exact Subtype.ext (congrArg Units.val h)

end Theory.SpecificGroups.SymplecticFour.AmbientOrderProof


namespace Theory.SpecificGroups.SymplecticFour.AmbientOrderProof
variable {n : ℕ} {F : Type*} [Field F]

/-- The faithful linear representation of the primary matrix group. -/
def toLinear : Sp n F →* (Vector n F ≃ₗ[F] Vector n F) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Vector n F)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp toGL)

@[simp] theorem toLinear_apply (g : Sp n F) (x : Vector n F) : toLinear g x = g • x := rfl

/-- Recover the primary matrix element from an actual form-preserving linear map. -/
def ofLinear (g : Vector n F ≃ₗ[F] Vector n F)
    (hg : ∀ x y, form (g x) (g y) = form x y) : Sp n F :=
  ⟨LinearMap.toMatrix' g.toLinearMap, mem_iff_preserves.mpr (by
    intro x y
    simpa only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] using hg x y)⟩

@[simp] theorem ofLinear_apply (g : Vector n F ≃ₗ[F] Vector n F)
    (hg : ∀ x y, form (g x) (g y) = form x y) (x : Vector n F) :
    ofLinear g hg • x = g x := LinearMap.toMatrix'_mulVec _ _

theorem ext_action {g h : Sp n F} (he : ∀ x : Vector n F, g • x = h • x) : g = h :=
  FaithfulSMul.eq_of_smul_eq_smul he

end Theory.SpecificGroups.SymplecticFour.AmbientOrderProof


namespace Theory.SpecificGroups.SymplecticFour.AmbientOrderProof
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
    let : Subsingleton V := Module.finrank_zero_iff.mp (by simpa using hdim)
    refine ⟨{ toLinearEquiv := LinearEquiv.ofSubsingleton (R := F) V (Vector 0 F)
              map_app' := ?_ }⟩
    intro x y
    rw [Subsingleton.elim x 0, Subsingleton.elim y 0]
    simp
  | succ n ih =>
    let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F V)
    obtain ⟨e,he⟩ := exists_ne (0 : V)
    obtain ⟨f,hef⟩ := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.exists_partner B hB he
    let W := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.complement B e f
    let C := B.restrict W
    have hC : C.IsAlt := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.complement_alternating B hA e f
    have hCN : C.Nondegenerate :=
      Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.complement_nondegenerate B hA e f hef hB
    have hW : Module.finrank F W = 2*n := by
      have h := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.finrank_complement B hA e f hef
      change Module.finrank F W + 2 = Module.finrank F V at h
      omega
    obtain ⟨k⟩ := ih C hC hCN hW
    let s := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.split B hA e f hef
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
    have hb := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.split_form B hA e f hef (s x) (s y)
    simpa only [s, LinearEquiv.symm_apply_apply] using hb.symm


/-- A prescribed hyperbolic pair can be the first pair of standard coordinates. -/
theorem exists_isometry_pair {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (n : ℕ) (B : LinearMap.BilinForm F V)
    (hA : B.IsAlt) (hB : B.Nondegenerate) (hdim : Module.finrank F V = 2*(n+1))
    (u v : V) (huv : B u v = 1) :
    ∃ g : B.IsometryEquiv (form (n := n+1) (F := F)),
      g u = e 0 ∧ g v = f 0 := by
  let W := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.complement B u v
  let C := B.restrict W
  have hC := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.complement_alternating B hA u v
  have hCN := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.complement_nondegenerate B hA u v huv hB
  have hW : Module.finrank F W = 2*n := by
    have h := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.finrank_complement B hA u v huv
    change Module.finrank F W + 2 = Module.finrank F V at h
    omega
  obtain ⟨k⟩ := exists_isometry n C hC hCN hW
  let s := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.split B hA u v huv
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
    have hb := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.split_form B hA u v huv (s x) (s y)
    simpa only [s, LinearEquiv.symm_apply_apply] using hb.symm
  refine ⟨{ toLinearEquiv := t, map_app' := htB }, ?_, ?_⟩
  · change t u = e 0
    apply (headTail n).injective
    rw [ht]
    have hs : s u = ((1,0),0) := by
      apply Prod.ext
      · simp [s, Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.split, huv, hA.self_eq_zero]
      · apply Subtype.ext
        change u-Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.planeProjection B u v u=0
        rw [Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.projection_e B hA u v huv, sub_self]
    rw [hs]
    simp [headTail, e]
    rfl
  · change t v = f 0
    apply (headTail n).injective
    rw [ht]
    have hs : s v = ((0,1),0) := by
      apply Prod.ext
      · simp [s, Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.split, hA.self_eq_zero,
          Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.reversed_pairing B hA u v huv]
      · apply Subtype.ext
        change v-Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.planeProjection B u v v=0
        rw [Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.projection_f B hA u v huv, sub_self]
    rw [hs]
    simp [headTail, f]
    rfl

end Theory.SpecificGroups.SymplecticFour.AmbientOrderProof




namespace Theory.SpecificGroups.SymplecticFour.AmbientOrderProof
variable {n : ℕ} {F : Type*} [Field F]

/-- Pointwise stabilizer of the first hyperbolic pair, not of just one vector. -/
def pairStabilizer (n : ℕ) (F : Type*) [Field F] : Subgroup (Sp (n+1) F) :=
  MulAction.stabilizer (Sp (n+1) F) (e (n := n+1) (F := F) 0) ⊓ MulAction.stabilizer (Sp (n+1) F) (f (n := n+1) (F := F) 0)

theorem mem_pairStabilizer (g : Sp (n+1) F) : g ∈ pairStabilizer n F ↔
    g • e (n := n+1) (F := F) 0 = e (n := n+1) (F := F) 0 ∧ g • f (n := n+1) (F := F) 0 = f (n := n+1) (F := F) 0 := Iff.rfl

theorem pairStabilizer_head (g : pairStabilizer n F) (x : Vector (n+1) F) :
    (headTail n (g.val • x)).1 = (headTail n x).1 := by
  have he := preserves g.val x (e (n := n+1) (F := F) 0)
  have hf := preserves g.val x (f (n := n+1) (F := F) 0)
  change form (g.val • x) (g.val • e (n := n+1) (F := F) 0) = form x (e (n := n+1) (F := F) 0) at he
  change form (g.val • x) (g.val • f (n := n+1) (F := F) 0) = form x (f (n := n+1) (F := F) 0) at hf
  rw [(mem_pairStabilizer g.val).mp g.prop |>.1] at he
  rw [(mem_pairStabilizer g.val).mp g.prop |>.2] at hf
  simp only [form_e_right, neg_inj] at he
  simp only [form_f_right] at hf
  exact Prod.ext hf he

/-- Restriction to the actual orthogonal complement, in its retained coordinates. -/
def tailMap (g : pairStabilizer n F) : Vector n F →ₗ[F] Vector n F :=
  (LinearMap.snd F (F×F) (Vector n F)).comp ((headTail n).toLinearMap.comp
    ((toLinear g.val).toLinearMap.comp ((headTail n).symm.toLinearMap.comp
      (LinearMap.inr F (F×F) (Vector n F)))))

theorem tailMap_apply (g : pairStabilizer n F) (x : Vector n F) :
    tailMap g x = (headTail n (g.val • (headTail n).symm (0,x))).2 := rfl

theorem pairStabilizer_tail (g : pairStabilizer n F) (x : Vector n F) :
    headTail n (g.val • (headTail n).symm (0,x)) = (0,tailMap g x) := by
  apply Prod.ext
  · rw [pairStabilizer_head, LinearEquiv.apply_symm_apply]
  · rfl

theorem tailMap_mul (g h : pairStabilizer n F) (x : Vector n F) :
    tailMap (g*h) x = tailMap g (tailMap h x) := by
  rw [tailMap_apply, tailMap_apply g]; simp only [Subgroup.coe_mul, mul_smul]
  rw [← pairStabilizer_tail h x, LinearEquiv.symm_apply_apply]

@[simp] theorem tailMap_one (x : Vector n F) : tailMap (1 : pairStabilizer n F) x = x := by
  simp [tailMap_apply]

def tailLinear (g : pairStabilizer n F) : Vector n F ≃ₗ[F] Vector n F :=
  { tailMap g with
    invFun := tailMap g⁻¹
    left_inv := fun x => by
      change tailMap g⁻¹ (tailMap g x) = x
      rw [← tailMap_mul, inv_mul_cancel, tailMap_one]
    right_inv := fun x => by
      change tailMap g (tailMap g⁻¹ x) = x
      rw [← tailMap_mul, mul_inv_cancel, tailMap_one] }

theorem tailLinear_preserves (g : pairStabilizer n F) (x y : Vector n F) :
    form (tailLinear g x) (tailLinear g y) = form x y := by
  have h := preserves g.val ((headTail n).symm (0,x)) ((headTail n).symm (0,y))
  change form (g.val • (headTail n).symm (0,x)) (g.val • (headTail n).symm (0,y)) = _ at h
  rw [form_headTail, form_headTail, pairStabilizer_tail, pairStabilizer_tail,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  simpa [tailLinear] using h

def restrictPair (g : pairStabilizer n F) : Sp n F :=
  ofLinear (tailLinear g) (tailLinear_preserves g)

@[simp] theorem restrictPair_apply (g : pairStabilizer n F) (x : Vector n F) :
    restrictPair g • x = tailMap g x := ofLinear_apply _ _ _

/-- Extend a full smaller symplectic isometry by the identity on the hyperbolic plane. -/
def extendLinear (g : Sp n F) : Vector (n+1) F ≃ₗ[F] Vector (n+1) F :=
  ((headTail n).trans ((LinearEquiv.refl F (F×F)).prodCongr (toLinear g))).trans
    (headTail n).symm

theorem extendLinear_headTail (g : Sp n F) (x : Vector (n+1) F) :
    headTail n (extendLinear g x) = ((headTail n x).1,g • (headTail n x).2) := by
  simp [extendLinear]

theorem extendLinear_preserves (g : Sp n F) (x y : Vector (n+1) F) :
    form (extendLinear g x) (extendLinear g y) = form x y := by
  rw [form_headTail, extendLinear_headTail, extendLinear_headTail, form_headTail x y]
  simp only [smul_eq_mulVec, preserves]

def extendPair (g : Sp n F) : pairStabilizer n F :=
  ⟨ofLinear (extendLinear g) (extendLinear_preserves g), by
    rw [mem_pairStabilizer]; constructor <;> rw [ofLinear_apply] <;> apply (headTail n).injective <;>
      rw [extendLinear_headTail] <;> simp [headTail,e,f] <;>
        change toLinear g 0 = 0 <;> exact map_zero _⟩

@[simp] theorem restrict_extend (g : Sp n F) : restrictPair (extendPair g) = g := by
  apply ext_action
  intro x
  rw [restrictPair_apply, tailMap_apply]
  change (headTail n (ofLinear (extendLinear g) (extendLinear_preserves g) • _)).2 = _
  rw [ofLinear_apply, extendLinear_headTail, LinearEquiv.apply_symm_apply]

@[simp] theorem headTail_e : headTail n (e (n := n+1) (F := F) 0) = ((1,0),0) := by
  simp [headTail,e]
  rfl

@[simp] theorem headTail_f : headTail n (f (n := n+1) (F := F) 0) = ((0,1),0) := by
  simp [headTail,f]
  rfl

theorem headTail_decomposition (x : Vector (n+1) F) :
    x = (headTail n x).1.1 • e 0 + (headTail n x).1.2 • f 0 +
      (headTail n).symm (0,(headTail n x).2) := by
  apply (headTail n).injective
  simp only [map_add, map_smul, headTail_e, headTail_f, LinearEquiv.apply_symm_apply]
  ext <;> simp

theorem pairStabilizer_block (g : pairStabilizer n F) (x : Vector (n+1) F) :
    headTail n (g.val • x) = ((headTail n x).1,tailMap g (headTail n x).2) := by
  have h := congrArg (fun z => headTail n (toLinear g.val z)) (headTail_decomposition x)
  simp only [map_add, map_smul, toLinear_apply,
    (mem_pairStabilizer g.val).mp g.prop |>.1,
    (mem_pairStabilizer g.val).mp g.prop |>.2,
    headTail_e, headTail_f, pairStabilizer_tail] at h
  simpa using h

@[simp] theorem extend_restrict (g : pairStabilizer n F) : extendPair (restrictPair g) = g := by
  apply Subtype.ext
  apply ext_action
  intro x
  apply (headTail n).injective
  change headTail n (ofLinear (extendLinear (restrictPair g)) (extendLinear_preserves (restrictPair g)) • x) = _
  rw [ofLinear_apply, extendLinear_headTail, restrictPair_apply, pairStabilizer_block]

/-- The full pointwise stabilizer is the full smaller symplectic group. -/
def pairStabilizerEquiv : pairStabilizer n F ≃* Sp n F where
  toFun := restrictPair
  invFun := extendPair
  left_inv := extend_restrict
  right_inv := restrict_extend
  map_mul' g h := by
    apply ext_action
    intro x
    rw [restrictPair_apply, mul_smul, restrictPair_apply, restrictPair_apply, tailMap_mul]

end Theory.SpecificGroups.SymplecticFour.AmbientOrderProof



namespace Theory.SpecificGroups.SymplecticFour.AmbientOrderProof
variable {n : ℕ} {F : Type*} [Field F]

abbrev HyperbolicPairs (n : ℕ) (F : Type*) [Field F] :=
  {p : Vector n F × Vector n F // form p.1 p.2 = 1}

/-- Count first vectors and normalized partners, before any group-order calculation. -/
def pairFiberEquiv : HyperbolicPairs n F ≃
    Σ e : {v : Vector n F // v ≠ 0}, {f : Vector n F // form e.val f = 1} where
  toFun p := ⟨⟨p.val.1,by intro h; simpa [h] using p.prop⟩,⟨p.val.2,p.prop⟩⟩
  invFun p := ⟨(p.1.val,p.2.val),p.2.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem vector_finrank : Module.finrank F (Vector n F) = 2*n := by
  simp [Vector,Index,Fintype.card_sum, two_mul]

theorem partner_card [Finite F] {e : Vector n F} (he : e ≠ 0) :
    Nat.card {f : Vector n F // form e f = 1} = Nat.card F ^ (2*n-1) := by
  obtain ⟨v,hv⟩ := Theory.SpecificGroups.SymplecticFour.AmbientOrderProof.AlternatingForm.exists_partner form form_nondegenerate he
  simpa only [vector_finrank] using Atlas.LinearFunctional.card_fiber (form e) v hv 1

theorem nonzero_vector_card [Finite F] :
    Nat.card {v : Vector n F // v ≠ 0} = Nat.card F ^ (2*n)-1 := by
  classical
  let := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hc : Fintype.card (Vector n F) = Nat.card F ^ (2*n) := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F), vector_finrank]
  rw [hc, Fintype.card_unique]

theorem hyperbolicPairs_card [Finite F] :
    Nat.card (HyperbolicPairs n F) = (Nat.card F ^ (2*n)-1) * Nat.card F ^ (2*n-1) := by
  classical
  let := Fintype.ofFinite F
  rw [Nat.card_congr pairFiberEquiv, Nat.card_sigma]
  have hs : (∑ e : {v : Vector n F // v ≠ 0}, Nat.card {f : Vector n F // form e.val f = 1}) =
      ∑ _e : {v : Vector n F // v ≠ 0}, Nat.card F ^ (2*n-1) := by
    apply Finset.sum_congr rfl
    intro e _
    exact partner_card e.prop
  rw [hs]
  rw [Finset.sum_const,Finset.card_univ, nsmul_eq_mul,← Nat.card_eq_fintype_card,
    nonzero_vector_card]
  simp
end Theory.SpecificGroups.SymplecticFour.AmbientOrderProof


namespace Theory.SpecificGroups.SymplecticFour.AmbientOrderProof
variable {n : ℕ} {F : Type*} [Field F]

instance pairAction : MulAction (Sp n F) (HyperbolicPairs n F) where
  smul g p := ⟨(g • p.val.1,g • p.val.2), by
    rw [smul_eq_mulVec, smul_eq_mulVec, preserves]; exact p.prop⟩
  one_smul p := by
    apply Subtype.ext
    change ((1 : Sp n F) • p.val.1, (1 : Sp n F) • p.val.2) = p.val
    simp
  mul_smul g h p := by
    apply Subtype.ext
    change ((g*h) • p.val.1,(g*h) • p.val.2) = (g • (h • p.val.1),g • (h • p.val.2))
    simp only [mul_smul]

def standardPair (n : ℕ) (F : Type*) [Field F] : HyperbolicPairs (n+1) F :=
  ⟨(e 0,f 0),by simp [e]⟩

/-- Full pair transitivity follows from the independent alternating-basis theorem. -/
theorem exists_pair_transporter (p : HyperbolicPairs (n+1) F) :
    ∃ g : Sp (n+1) F, g • standardPair n F = p := by
  obtain ⟨k,hk₁,hk₂⟩ := exists_isometry_pair n form form_alternating form_nondegenerate
    vector_finrank p.val.1 p.val.2 p.prop
  refine ⟨ofLinear k.symm.toLinearEquiv k.symm.map_app', ?_⟩
  apply Subtype.ext
  change (ofLinear _ _ • e 0, ofLinear _ _ • f 0) = p.val
  simp only [ofLinear_apply]
  apply Prod.ext
  · rw [← hk₁]; exact k.symm_apply_apply _
  · rw [← hk₂]; exact k.symm_apply_apply _

theorem standardPair_stabilizer :
    MulAction.stabilizer (Sp (n+1) F) (standardPair n F) = pairStabilizer n F := by
  ext g
  rw [mem_pairStabilizer]
  change (g • standardPair n F = standardPair n F) ↔ _
  rw [Subtype.ext_iff]
  exact Prod.ext_iff

/-- The actual ordered-pair orbit is the whole normalized-pair geometry. -/
def standardPairOrbitEquiv : MulAction.orbit (Sp (n+1) F) (standardPair n F) ≃
    HyperbolicPairs (n+1) F :=
  Equiv.ofBijective (fun p => p.val) ⟨Subtype.val_injective, fun p =>
    ⟨⟨p,by obtain ⟨g,hg⟩ := exists_pair_transporter p; exact ⟨g,hg⟩⟩,rfl⟩⟩

/-- Independent order recurrence using the full pointwise hyperbolic-pair stabilizer. -/
public theorem card_sp_succ [Finite F] : Nat.card (Matrix.symplecticGroup (Fin (n+1)) F) =
    (Nat.card F ^ (2*(n+1))-1) * Nat.card F ^ (2*n+1) * Nat.card (Matrix.symplecticGroup (Fin n) F) := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Sp (n+1) F)
    (standardPair n F)), Nat.card_prod,
    Nat.card_congr standardPairOrbitEquiv, standardPair_stabilizer,
    Nat.card_congr pairStabilizerEquiv.toEquiv, hyperbolicPairs_card]
  congr 2

end Theory.SpecificGroups.SymplecticFour.AmbientOrderProof
