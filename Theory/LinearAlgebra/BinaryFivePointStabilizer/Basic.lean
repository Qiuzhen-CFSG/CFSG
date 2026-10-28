module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.QuotientNormalImage

/-!
# The quotient action of a binary point stabilizer

The stabilizer of a vector acts on the quotient by its span. Its kernel consists
of automorphisms whose displacements lie in the fixed line. Each such element
squares to the identity, so the kernel is elementary abelian. In dimension five
the quotient has dimension four.

This is the intrinsic linear action underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, Lemma 14.2.21, printed p.989
(PDF p.1006). No structural identification of the stabilizer is assumed.
-/

@[expose] public section

namespace Theory.LinearAlgebra.BinaryFivePointStabilizer

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The actual subgroup of linear automorphisms fixing the marked vector. -/
def stabilizer (z : E) : Subgroup (E ≃ₗ[ZMod 2] E) where
  carrier := {g | g z = z}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    change g z = z at hg
    change h z = z at hh
    change g (h z) = z
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change g.symm z = z
    apply g.injective
    exact g.apply_symm_apply z |>.trans hg.symm

@[simp] theorem mem_stabilizer (z : E) (g : E ≃ₗ[ZMod 2] E) :
    g ∈ stabilizer z ↔ g z = z := Iff.rfl

/-- The fixed line. -/
abbrev line (z : E) : Submodule (ZMod 2) E := Submodule.span (ZMod 2) {z}

/-- The natural quotient space for the point-stabilizer action. -/
abbrev QuotientSpace (z : E) := E ⧸ line z

theorem fixes_line (z : E) (g : stabilizer z) (x : E) (hx : x ∈ line z) :
    (g : E ≃ₗ[ZMod 2] E) x = x := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, g.property]

theorem map_line (z : E) (g : stabilizer z) :
    (line z).map (g : E ≃ₗ[ZMod 2] E).toLinearMap = line z := by
  rw [Submodule.map_span]
  simp only [Set.image_singleton]
  change Submodule.span (ZMod 2) {(g : E ≃ₗ[ZMod 2] E) z} = line z
  rw [g.property]

/-- The homomorphism induced by the action on the quotient by the fixed line. -/
def quotientAction (z : E) : stabilizer z →*
    (QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z) where
  toFun g := Submodule.Quotient.equiv (line z) (line z) g.val (map_line z g)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

@[simp] theorem quotientAction_mk (z : E) (g : stabilizer z) (x : E) :
    quotientAction z g ((line z).mkQ x) = (line z).mkQ (g.val x) := rfl

/-- The displacement kernel of the quotient action. -/
abbrev kernel (z : E) : Subgroup (stabilizer z) := (quotientAction z).ker

theorem mem_kernel_iff (z : E) (g : stabilizer z) :
    g ∈ kernel z ↔ ∀ x : E, g.val x - x ∈ line z := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x
    apply (Submodule.Quotient.eq (line z)).mp
    exact LinearEquiv.congr_fun h ((line z).mkQ x)
  · intro h
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact (Submodule.Quotient.eq (line z)).mpr (h x)

private theorem add_self_eq_zero (x : E) : x + x = 0 := by
  calc
    x + x = ((1 : ZMod 2) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 from rfl, zero_smul]

/-- Every displacement-kernel element is an involution or the identity. -/
theorem kernel_sq (z : E) (g : kernel z) : g ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  ext x
  have hd := (mem_kernel_iff z g.val).mp g.property x
  have hf := fixes_line z g.val _ hd
  simp only [map_sub] at hf
  change g.val.val (g.val.val x) = x
  have hneg (y : E) : -y = y := neg_eq_of_add_eq_zero_left (add_self_eq_zero y)
  simp only [sub_eq_add_neg, hneg] at hf
  exact add_right_cancel (hf.trans (add_comm _ _))

/-- The quotient-action kernel is elementary abelian in every dimension. -/
instance kernel_elementaryAbelian (z : E) : IsElementaryAbelian 2 (kernel z) where
  is_comm := by
    constructor
    intro a b
    have hi (g : kernel z) : g⁻¹ = g := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [pow_two] using kernel_sq z g
    calc
      a * b = (a * b)⁻¹ := (hi _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
      _ = b * a := by rw [hi, hi]
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (kernel_sq z)

/-- The kernel remains normal in each overgroup and maps back to the same kernel. -/
theorem kernel_normal_subgroupOf (z : E) (H : Subgroup (stabilizer z))
    (hH : kernel z ≤ H) :
    ((kernel z).subgroupOf H).Normal ∧
      ((kernel z).subgroupOf H).map H.subtype = kernel z :=
  Subgroup.normal_subgroupOf_and_map_eq (kernel z) H hH

/-- A five-dimensional binary space modulo a nonzero vector has dimension four. -/
theorem finrank_quotient [FiniteDimensional (ZMod 2) E] (z : E) (hz : z ≠ 0)
    (hE : Module.finrank (ZMod 2) E = 5) :
    Module.finrank (ZMod 2) (QuotientSpace z) = 4 := by
  have h := (line z).finrank_quotient_add_finrank
  rw [finrank_span_singleton hz, hE] at h
  change Module.finrank (ZMod 2) (QuotientSpace z) + 1 = 5 at h
  omega

end Theory.LinearAlgebra.BinaryFivePointStabilizer
