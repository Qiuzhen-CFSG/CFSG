module

public import Theory.Representation.BinaryPermutation.ThreeTensorDisplacement
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The simultaneous transposition/inversion extension of A₆ × C₃

The concrete group is the equal-sign subgroup of S₆ × S₃. Its even subgroup
is the embedded product A₆ × A₃, with A₃ explicitly identified with C₃.
Projection to the sign has this product as kernel and is onto the two-element
unit group of ℤ. The pair of transpositions (01),(01) is an involution and
conjugates the factors by a transposition and inversion, respectively.
Every element belongs to one of the resulting two cosets.

The representation is the restriction of the genuine external tensor action
on the binary natural six-point quotient and the three-point augmentation
core. These factors have dimensions four and two. Both permutation factors,
including the simultaneous odd coset, act on the tensor product.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(10), printed p.364 (PDF p.375), and the exclusion in 6.2.19,
printed p.691 (PDF p.708).
-/

@[expose] public section

open scoped TensorProduct
namespace Representation.RankTwo.Imprimitive.AlternatingSixTensor
abbrev S6 := Equiv.Perm (Fin 6)
abbrev S3 := Equiv.Perm (Fin 3)
abbrev A6 := alternatingGroup (Fin 6)
abbrev C3 := alternatingGroup (Fin 3)

def equalSign : Subgroup (S6 × S3) :=
  (Equiv.Perm.sign.comp (MonoidHom.fst S6 S3)).eqLocus
    (Equiv.Perm.sign.comp (MonoidHom.snd S6 S3))
abbrev GroupModel := equalSign

@[simp] theorem mem_equalSign (g : S6 × S3) :
    g ∈ equalSign ↔ g.1.sign = g.2.sign := Iff.rfl

def parity : GroupModel →* ℤˣ :=
  Equiv.Perm.sign.comp ((MonoidHom.fst S6 S3).comp equalSign.subtype)

def base : (A6 × C3) →* GroupModel where
  toFun g := ⟨(g.1.val, g.2.val), by
    change g.1.val.sign = g.2.val.sign
    rw [Equiv.Perm.mem_alternatingGroup.mp g.1.property,
      Equiv.Perm.mem_alternatingGroup.mp g.2.property]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem base_injective : Function.Injective base := by
  intro a b h
  have h' := congrArg (fun g : GroupModel => g.val) h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h'))
    (Subtype.ext (congrArg Prod.snd h'))

theorem base_range : base.range = parity.ker := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mp a.1.property
  · intro h
    have h6 : g.val.1.sign = 1 := h
    have h3 : g.val.2.sign = 1 := g.property.symm.trans h6
    exact ⟨(⟨g.val.1, Equiv.Perm.mem_alternatingGroup.mpr h6⟩,
      ⟨g.val.2, Equiv.Perm.mem_alternatingGroup.mpr h3⟩), rfl⟩

def outer : GroupModel := ⟨(Equiv.swap 0 1, Equiv.swap 0 1), by
  change (Equiv.swap (0 : Fin 6) 1).sign = (Equiv.swap (0 : Fin 3) 1).sign
  decide⟩

@[simp] theorem outer_sq : outer * outer = 1 := by
  apply Subtype.ext
  exact Prod.ext (Equiv.swap_mul_self _ _) (Equiv.swap_mul_self _ _)

@[simp] theorem parity_outer : parity outer = -1 := by decide

theorem outer_ne_one : outer ≠ 1 := by
  intro h
  have hh := congrArg parity h
  rw [parity_outer, map_one] at hh
  exact (by decide : (-1 : ℤˣ) ≠ 1) hh

theorem parity_surjective : Function.Surjective parity := by
  intro z
  rcases Int.units_eq_one_or z with rfl | rfl
  · exact ⟨1, map_one parity⟩
  · exact ⟨outer, parity_outer⟩

noncomputable def quotientEquiv : GroupModel ⧸ parity.ker ≃* ℤˣ :=
  QuotientGroup.quotientKerEquivOfSurjective parity parity_surjective

theorem card_cubic : Nat.card C3 = 3 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

noncomputable def cubicEquiv : C3 ≃* Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq card_cubic (by simp)

def transpositionConjugation : A6 ≃* A6 where
  toFun a := ⟨Equiv.swap 0 1 * a.val * Equiv.swap 0 1, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul,
      Equiv.Perm.mem_alternatingGroup.mp a.property]
    norm_num [Equiv.Perm.sign_swap]⟩
  invFun a := ⟨Equiv.swap 0 1 * a.val * Equiv.swap 0 1, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul,
      Equiv.Perm.mem_alternatingGroup.mp a.property]
    norm_num [Equiv.Perm.sign_swap]⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

private theorem invert_cubic (c : C3) :
    Equiv.swap 0 1 * c.val * Equiv.swap 0 1 = c.val⁻¹ := by
  revert c
  decide +kernel

theorem outer_conjugates_base (a : A6) (c : C3) :
    outer * base (a,c) * outer⁻¹ = base (transpositionConjugation a,c⁻¹) := by
  apply Subtype.ext
  apply Prod.ext
  · change Equiv.swap 0 1 * a.val * (Equiv.swap 0 1)⁻¹ = _
    simp [transpositionConjugation, base]
  · change Equiv.swap 0 1 * c.val * (Equiv.swap 0 1)⁻¹ = _
    simpa [base] using invert_cubic c

theorem two_cosets (g : GroupModel) :
    ∃ a : A6 × C3, g = base a ∨ g = outer * base a := by
  rcases Int.units_eq_one_or (parity g) with h | h
  · have hg : g ∈ base.range := by rw [base_range]; exact h
    obtain ⟨a, rfl⟩ := hg
    exact ⟨a, Or.inl rfl⟩
  · have hg : outer⁻¹ * g ∈ base.range := by
      rw [base_range]
      change parity (outer⁻¹ * g) = 1
      rw [map_mul, map_inv, parity_outer, h]
      decide
    obtain ⟨a, ha⟩ := hg
    exact ⟨a, Or.inr (by rw [ha, mul_inv_cancel_left])⟩

abbrev FourSpace := BinaryPermutation.natural (Fin 6)
abbrev TwoSpace := BinaryPermutation.core (Fin 3)
abbrev TensorSpace := FourSpace ⊗[ZMod 2] TwoSpace

noncomputable def representation : Representation (ZMod 2) GroupModel TensorSpace :=
  (BinaryPermutation.ThreeTensor.action (BinaryPermutation.naturalRepresentation (Fin 6))).comp
    equalSign.subtype

@[simp] theorem representation_tmul (g : GroupModel) (v : FourSpace) (w : TwoSpace) :
    representation g (v ⊗ₜ[ZMod 2] w) =
      BinaryPermutation.naturalRepresentation (Fin 6) g.val.1 v ⊗ₜ[ZMod 2]
        BinaryPermutation.coreRepresentation (Fin 3) g.val.2 w := rfl

theorem finrank_fourSpace : Module.finrank (ZMod 2) FourSpace = 4 := by
  simpa using BinaryPermutation.finrank_natural_even (Fin 6) (by decide)

theorem finrank_twoSpace : Module.finrank (ZMod 2) TwoSpace = 2 := by
  simpa using BinaryPermutation.finrank_core (Fin 3)

theorem finrank_tensorSpace : Module.finrank (ZMod 2) TensorSpace = 8 := by
  rw [Module.finrank_tensorProduct, finrank_fourSpace, finrank_twoSpace]

end Representation.RankTwo.Imprimitive.AlternatingSixTensor
