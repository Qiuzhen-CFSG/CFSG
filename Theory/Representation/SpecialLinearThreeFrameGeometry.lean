module
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.QuadraticDuality
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Algebra.CharP.Two

/-!
# Concrete roots and dual fixed spaces for SL₃

A root consists of determinant-one matrices with displacement in its center
and fixing its axis pointwise. The point radical is the root whose center
and axis coincide. Stabilizers are actual setwise stabilizers in the natural
matrix action; a frame is an ordered direct decomposition into three F-lines.

The shear x ↦ x + f(x)v realizes every vector in a root's center as a
displacement when its axis is proper. Consequently its moved space is exactly
the center. Taking annihilators computes the common fixed space of two point
radicals in the genuine F-linear contragredient module. These arguments work
over every field. The exponent-two calculation applies in characteristic two,
including F₂. Frame generation and the plane-stabilizer residual are separate
results, not conclusions encoded in the frame data.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.1.1–4 and
G.2.5, printed pp.327–328,335–336, PDF pp.338–339,346–347.
-/

@[expose] public section
noncomputable section
namespace Matrix.SpecialLinearGroup.FrameGeometry
open Matrix Subgroup
open scoped MatrixGroups Pointwise
variable {F : Type*} [Field F]
/-- The literal natural matrix representation. -/
abbrev natural : Representation F SL(3, F) (Fin 3 → F) :=
  Representation.specialLinearNatural 3

/-- Displacement in A and pointwise fixation of B; incident dimensions are supplied by callers. -/
def root (A B : Submodule F (Fin 3 → F)) : Subgroup SL(3, F) where
  carrier := {g | (∀ v, natural g v - v ∈ A) ∧ (∀ v ∈ B, natural g v = v)}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hgA, hgB⟩ ⟨hhA, hhB⟩
    constructor
    · intro v
      have he : natural (g * h) v - v =
          (natural g (natural h v) - natural h v) + (natural h v - v) := by
        simp only [map_mul, Module.End.mul_apply]
        abel
      rw [he]
      exact A.add_mem (hgA (natural h v)) (hhA v)
    · intro v hv
      simp only [map_mul, Module.End.mul_apply, hhB v hv, hgB v hv]
  inv_mem' := by
    rintro g ⟨hgA, hgB⟩
    constructor
    · intro v
      have h := A.neg_mem (hgA (natural g⁻¹ v))
      simpa only [natural.self_inv_apply, neg_sub] using h
    · intro v hv
      exact (natural.inv_apply_eq_iff).mpr (hgB v hv).symm

/-- The concrete unipotent point radical when A is a line. -/
def pointRadical (A : Submodule F (Fin 3 → F)) : Subgroup SL(3, F) := root A A

/-- The actual setwise stabilizer of a subspace in SL₃(F). -/
def stabilizer (A : Submodule F (Fin 3 → F)) : Subgroup SL(3, F) :=
  MulAction.stabilizer SL(3, F) (A : Set (Fin 3 → F))

/-- Setwise stabilization is equivalent to equality of the image submodule. -/
theorem mem_stabilizer_iff (A : Submodule F (Fin 3 → F)) (g : SL(3, F)) :
    g ∈ stabilizer A ↔ A.map (natural g) = A := by
  change g • (A : Set (Fin 3 → F)) = (A : Set (Fin 3 → F)) ↔ _
  have he : (↑(A.map (natural g)) : Set (Fin 3 → F)) = g • (A : Set (Fin 3 → F)) := rfl
  rw [← he, SetLike.coe_set_eq]

theorem root_mono {A B C D : Submodule F (Fin 3 → F)} (hAC : A ≤ C) (hDB : D ≤ B) :
    root A B ≤ root C D := by
  rintro g ⟨hgA, hgB⟩
  exact ⟨fun v => hAC (hgA v), fun v hv => hgB v (hDB hv)⟩

theorem root_le_stabilizer_of_le_axis {A B C : Submodule F (Fin 3 → F)} (hCB : C ≤ B) :
    root A B ≤ stabilizer C := by
  intro g hg
  rw [stabilizer, MulAction.mem_stabilizer_set]
  intro v
  change natural g v ∈ C ↔ v ∈ C
  constructor
  · intro hv
    have he := ((root A B).inv_mem hg).2 _ (hCB hv)
    rw [natural.inv_self_apply] at he
    exact he ▸ hv
  · intro hv
    rw [hg.2 v (hCB hv)]
    exact hv

theorem root_le_stabilizer_of_center_le {A B C : Submodule F (Fin 3 → F)} (hAC : A ≤ C) :
    root A B ≤ stabilizer C := by
  intro g hg
  rw [stabilizer, MulAction.mem_stabilizer_set]
  intro v
  change natural g v ∈ C ↔ v ∈ C
  have hp : ∀ a ∈ root A B, ∀ w ∈ C, natural a w ∈ C := by
    intro a ha w hw
    have he := C.add_mem (hAC (ha.1 w)) hw
    simpa only [sub_add_cancel] using he
  exact ⟨fun hv => by simpa using hp g⁻¹ ((root A B).inv_mem hg) _ hv,
    hp g hg v⟩

/-- An ordered direct frame of three F-lines, without any group-theoretic conclusions. -/
structure Frame (F : Type*) [Field F] where
  point : Fin 3 → Submodule F (Fin 3 → F)
  dimension : ∀ i, Module.finrank F (point i) = 1
  disjoint : Disjoint (point 0) (point 1)
  third_disjoint : Disjoint (point 0 ⊔ point 1) (point 2)
  span : (point 0 ⊔ point 1) ⊔ point 2 = ⊤

theorem Frame.point_ne_top (b : Frame F) (i : Fin 3) : b.point i ≠ ⊤ := by
  intro he
  have hd := b.dimension i
  rw [he] at hd
  simp at hd

/-- The second index is the other fixed point, not the omitted coordinate. -/
def Frame.axisRoot (b : Frame F) (i j : Fin 3) : Subgroup SL(3, F) :=
  root (b.point i) (b.point i ⊔ b.point j)

theorem Frame.axisRoot_le_pointRadical (b : Frame F) (i j : Fin 3) :
    b.axisRoot i j ≤ pointRadical (b.point i) := root_mono le_rfl le_sup_left

theorem Frame.axisRoot_le_second_stabilizer (b : Frame F) (i j : Fin 3) :
    b.axisRoot i j ≤ stabilizer (b.point j) := root_le_stabilizer_of_le_axis le_sup_right

/-- The F-span of all natural displacements of H. -/
def movedSpace (H : Subgroup SL(3, F)) : Submodule F (Fin 3 → F) :=
  Representation.Coinvariants.ker (natural.comp H.subtype)

/-- Common fixed vectors in the genuine F-linear contragredient module. -/
def dualFixed (H : Subgroup SL(3, F)) : Submodule F (Module.Dual F (Fin 3 → F)) :=
  Representation.invariants (natural.dual.comp H.subtype)

/-- A displacement bound is exactly containment in the corresponding zero-axis root. -/
theorem movedSpace_le_iff (H : Subgroup SL(3, F)) (A : Submodule F (Fin 3 → F)) :
    movedSpace H ≤ A ↔ H ≤ root A ⊥ := by
  rw [movedSpace, Representation.Coinvariants.ker, Submodule.span_le]
  constructor
  · intro hs g hg
    constructor
    · intro v
      apply hs
      exact ⟨(⟨g, hg⟩, v), rfl⟩
    · intro v hv
      have hv0 : v = 0 := hv
      rw [hv0, map_zero]
  · rintro hs _ ⟨⟨g, v⟩, rfl⟩
    exact (hs g.property).1 v

theorem movedSpace_mono {H K : Subgroup SL(3, F)} (hHK : H ≤ K) :
    movedSpace H ≤ movedSpace K := by
  rw [movedSpace_le_iff]
  exact hHK.trans ((movedSpace_le_iff K _).mp le_rfl)

/-- Joining actor subgroups adds their moved subspaces. -/
theorem movedSpace_sup (H K : Subgroup SL(3, F)) :
    movedSpace (H ⊔ K) = movedSpace H ⊔ movedSpace K := by
  apply le_antisymm
  · rw [movedSpace_le_iff]
    exact sup_le ((movedSpace_le_iff H _).mp le_sup_left)
      ((movedSpace_le_iff K _).mp le_sup_right)
  · exact sup_le (movedSpace_mono le_sup_left) (movedSpace_mono le_sup_right)

/-- Dual fixed space and natural moved space are mutual annihilator constructions. -/
theorem dualFixed_eq_annihilator (H : Subgroup SL(3, F)) :
    dualFixed H = (movedSpace H).dualAnnihilator :=
  (Representation.dualAnnihilator_coinvariantsKer (natural.comp H.subtype)).symm

/-- The determinant-one shear x ↦ x + f(x)v. -/
def shear (f : Module.Dual F (Fin 3 → F)) (v : Fin 3 → F) (hfv : f v = 0) : SL(3, F) :=
  ⟨LinearMap.toMatrix' (LinearMap.transvection f v), by
    rw [LinearMap.det_toMatrix', LinearMap.transvection.det, hfv, add_zero]⟩

theorem shear_apply (f : Module.Dual F (Fin 3 → F)) (v : Fin 3 → F)
    (hfv : f v = 0) (w : Fin 3 → F) :
    natural (shear f v hfv) w = w + f w • v :=
  LinearMap.toMatrix'_mulVec (LinearMap.transvection f v) w

theorem shear_mem_root {A B : Submodule F (Fin 3 → F)}
    (hAB : A ≤ B) (v : Fin 3 → F) (hv : v ∈ A)
    (f : Module.Dual F (Fin 3 → F)) (hf : f ∈ B.dualAnnihilator) :
    shear f v (((Submodule.mem_dualAnnihilator f).mp hf) v (hAB hv)) ∈ root A B := by
  constructor
  · intro w
    rw [shear_apply, add_sub_cancel_left]
    exact A.smul_mem _ hv
  · intro w hw
    rw [shear_apply, ((Submodule.mem_dualAnnihilator f).mp hf) w hw, zero_smul, add_zero]

/-- Every vector in the center is a displacement of an actual root element
as long as the axis is proper. -/
theorem exists_root_displacement (A B : Submodule F (Fin 3 → F)) (hAB : A ≤ B)
    (hB : B ≠ ⊤) (v : Fin 3 → F) (hv : v ∈ A) :
    ∃ g ∈ root A B, ∃ w, natural g w - w = v := by
  obtain ⟨f, hf, hBf⟩ := B.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hB)
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    simpa only [DFunLike.ne_iff, LinearMap.zero_apply] using hf
  have hfv : f v = 0 := hBf (hAB hv)
  refine ⟨shear f v hfv, shear_mem_root hAB v hv f ?_, (f w)⁻¹ • w, ?_⟩
  · exact (Submodule.mem_dualAnnihilator f).mpr (fun x hx => hBf hx)
  · rw [shear_apply, add_sub_cancel_left, map_smul, smul_eq_mul, inv_mul_cancel₀ hw, one_smul]

theorem exists_pointRadical_displacement (A : Submodule F (Fin 3 → F)) (hA : A ≠ ⊤)
    (v : Fin 3 → F) (hv : v ∈ A) :
    ∃ g ∈ pointRadical A, ∃ w, natural g w - w = v :=
  exists_root_displacement A A le_rfl hA v hv

/-- The moved space of a root with proper axis is its whole center. -/
theorem movedSpace_root (A B : Submodule F (Fin 3 → F)) (hAB : A ≤ B) (hB : B ≠ ⊤) :
    movedSpace (root A B) = A := by
  apply le_antisymm
  · exact (movedSpace_le_iff _ _).mpr (root_mono le_rfl bot_le)
  · intro v hv
    obtain ⟨g, hg, w, rfl⟩ := exists_root_displacement A B hAB hB v hv
    exact Representation.Coinvariants.sub_mem_ker (ρ := natural.comp (root A B).subtype) ⟨g, hg⟩ w

theorem movedSpace_pointRadical (A : Submodule F (Fin 3 → F)) (hA : A ≠ ⊤) :
    movedSpace (pointRadical A) = A := movedSpace_root A A le_rfl hA

theorem dualFixed_pointRadical (A : Submodule F (Fin 3 → F)) (hA : A ≠ ⊤) :
    dualFixed (pointRadical A) = A.dualAnnihilator := by
  rw [dualFixed_eq_annihilator, movedSpace_pointRadical A hA]

/-- The fixed space of two point radicals is precisely their pair-plane annihilator. -/
theorem dualFixed_pair (A B : Submodule F (Fin 3 → F)) (hA : A ≠ ⊤) (hB : B ≠ ⊤) :
    dualFixed (pointRadical A ⊔ pointRadical B) = (A ⊔ B).dualAnnihilator := by
  rw [dualFixed_eq_annihilator, movedSpace_sup, movedSpace_pointRadical A hA,
    movedSpace_pointRadical B hB]
/-- The elementary abelian exponent calculation also holds over the binary field. -/
theorem pointRadical_sq [CharP F 2] (A : Submodule F (Fin 3 → F))
    (g : SL(3, F)) (hg : g ∈ pointRadical A) : g ^ 2 = 1 := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change natural (g ^ 2) v = natural (1 : SL(3, F)) v
  rw [map_one, Module.End.one_apply, pow_two, map_mul, Module.End.mul_apply]
  have hh := hg.2 _ (hg.1 v)
  rw [map_sub] at hh
  have he := congrArg (fun w => w + natural g v) hh
  simp only [sub_add_cancel] at he
  ext i
  have hi := congrFun he i
  change natural g (natural g v) i = (natural g v i - v i) + natural g v i at hi
  calc
    natural g (natural g v) i = (natural g v i - v i) + natural g v i := hi
    _ = (natural g v i + natural g v i) - v i := by abel
    _ = v i := by rw [CharTwo.add_self_eq_zero, zero_sub, CharTwo.neg_eq]

end Matrix.SpecialLinearGroup.FrameGeometry
