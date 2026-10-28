module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.SpecialLinearNatural
public import CFSG.Quasithin.ClassicalModels
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.FieldTheory.Finiteness

/-!
# Named block types in C.1.12, C.1.22 and C.1.30

The standard types below identify both the quotient by `O₂` and the actual
conjugation module with a concrete natural representation. The exceptional
types retain the dimension and faithfulness conditions used in the source;
their natural-module identifications are consequences of representation
theorems, rather than extra defining hypotheses.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Definitions C.1.12, C.1.22 and C.1.30, printed
pp.124, 129 and 135. Notation A.3.5 (printed p.43) identifies `A-hat_6` as
the quasisimple triple cover of `A_6`.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC

open ClassicalGroup Theory.GroupTheory

variable (L : Type*) [Group L]

/-- The model's multiplicative action is the specified linear representation,
after writing the additive natural module multiplicatively. -/
def IsLinearBlockModel {A V k : Type*} [Group A] [AddCommGroup V]
    [Semiring k] [Module k V] (pi : Representation k A V) : Prop :=
  ∃ rho : A →* MulAut (Multiplicative V),
    Nonempty (BlockModuleModel L rho) ∧
      ∀ (g : A) (v : Multiplicative V),
        Multiplicative.toAdd (rho g v) = pi g (Multiplicative.toAdd v)

/-- Type `L₂(2^n)`, with its defining two-dimensional module. The separate
projective model records the source's quotient name; the special-linear
model carries the natural action (these groups agree in characteristic two). -/
def IsL2EvenBlock (n : Nat) : Prop :=
  1 < n ∧ IsShort L ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ n ∧
      IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) ∧
      IsLinearBlockModel L (Representation.specialLinearNatural (k := F) 2)

/-- Type `A_n`: the noncentral chief factor of the binary permutation module,
namely the image of its even-weight core modulo the constant line. -/
def IsAlternatingBlock (n : Nat) : Prop :=
  3 ≤ n ∧ IsShort L ∧
    IsLinearBlockModel L ((BinaryPermutation.naturalRepresentation (Fin n)).comp
      (alternatingGroup (Fin n)).subtype)

/-- The set `chi` of C.1.12: even-field rank one or odd-degree alternating. -/
def IsChiBlock : Prop :=
  (∃ n, IsL2EvenBlock L n) ∨
    (∃ n, Odd n ∧ IsAlternatingBlock L n)

/-- The smaller class `chi_0` of C.1.12. The two `A₅` and `L₂(4)`
alternatives keep their different natural modules. -/
def IsChiZeroBlock : Prop :=
  (∃ n, IsL2EvenBlock L n) ∨ IsAlternatingBlock L 3 ∨ IsAlternatingBlock L 5

/-- The exceptional `A₇` definition is on `U/C_U(L)`, as in C.1.22. -/
def IsExceptionalA7Block : Prop :=
  IsShort L ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) ∧
    Nat.card (BlockModule L) = 2 ^ 4

/-- `A-hat_6` denotes the quasisimple triple cover with center of order three
(A.3.5), specified by its actual central quotient isomorphism. The rank-six
condition is on `U`, and faithfulness is `C_L(U) = O₂(L)`. -/
def IsExceptionalAhat6Block : Prop :=
  IsShort L ∧
    IsQuasisimple (L ⧸ pCore 2 L) ∧
    Nat.card (Subgroup.center (L ⧸ pCore 2 L)) = 3 ∧
    Nonempty (((L ⧸ pCore 2 L) ⧸
      Subgroup.center (L ⧸ pCore 2 L)) ≃*
        alternatingGroup (Fin 6)) ∧
    Nat.card (blockU L) = 2 ^ 6 ∧
    Subgroup.centralizer (blockU L : Set L) = pCore 2 L

/-- A natural `SL₃(2^n)` block; the full special-linear group is retained. -/
def IsSL3EvenBlock (n : Nat) : Prop :=
  1 ≤ n ∧ IsShort L ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ n ∧
      IsLinearBlockModel L (Representation.specialLinearNatural (k := F) 3)

/-- A natural `L_n(2)` block. Over the prime field of order two the special
and projective special groups agree. -/
def IsLinearTwoBlock (n : Nat) : Prop :=
  2 ≤ n ∧ IsShort L ∧
    IsPSL (L ⧸ pCore 2 L) n 2 ∧
    IsLinearBlockModel L
      (Representation.specialLinearNatural (k := ZMod 2) n)

/-- An `Sp₄(4)` block. The action is literally multiplication of column
vectors by a matrix preserving the standard alternating form. -/
def IsSp4FourBlock : Prop :=
  IsShort L ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = 4 ∧
    ∃ rho : Matrix.symplecticGroup (Fin 2) F →*
        MulAut (Multiplicative ((Fin 2 ⊕ Fin 2) → F)),
      Nonempty (BlockModuleModel L rho) ∧
        ∀ (g : Matrix.symplecticGroup (Fin 2) F)
          (v : Multiplicative ((Fin 2 ⊕ Fin 2) → F)),
          Multiplicative.toAdd (rho g v) =
            Matrix.mulVec g.val (Multiplicative.toAdd v)

variable {L}

/-- The linear-model interface exposes the actual core-quotient isomorphism. -/
theorem IsLinearBlockModel.quotient_iso {A V k : Type*} [Group A]
    [AddCommGroup V] [Semiring k] [Module k V]
    {pi : Representation k A V} (h : IsLinearBlockModel L pi) :
    Nonempty ((L ⧸ pCore 2 L) ≃* A) := by
  obtain ⟨rho, ⟨model⟩, _⟩ := h
  exact ⟨model.quotientIso⟩

/-- Cardinality is transported through the equivariant module model. -/
theorem IsLinearBlockModel.module_card {A V k : Type*} [Group A]
    [AddCommGroup V] [Semiring k] [Module k V]
    {pi : Representation k A V} (h : IsLinearBlockModel L pi) :
    Nat.card (BlockModule L) = Nat.card V := by
  obtain ⟨rho, ⟨model⟩, _⟩ := h
  exact Nat.card_congr model.moduleIso.toEquiv

/-- The binary dimension of a rank-one natural block is `2n`. -/
theorem IsL2EvenBlock.module_card {n : Nat} (h : IsL2EvenBlock L n) :
    Nat.card (BlockModule L) = 2 ^ (n * 2) := by
  obtain ⟨_, _, F, _, _, hF, _, hmodel⟩ := h
  rw [hmodel.module_card, Nat.card_fun, hF, Nat.card_fin, pow_mul]

/-- The binary dimension of an `SL₃(2^n)` natural block is `3n`. -/
theorem IsSL3EvenBlock.module_card {n : Nat} (h : IsSL3EvenBlock L n) :
    Nat.card (BlockModule L) = 2 ^ (n * 3) := by
  obtain ⟨_, _, F, _, _, hF, hmodel⟩ := h
  rw [hmodel.module_card, Nat.card_fun, hF, Nat.card_fin, pow_mul]

theorem IsLinearTwoBlock.module_card {n : Nat} (h : IsLinearTwoBlock L n) :
    Nat.card (BlockModule L) = 2 ^ n := by
  rw [h.2.2.2.module_card, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

/-- The natural symplectic module has four coordinates over the field of
order four, hence binary dimension eight. -/
theorem IsSp4FourBlock.module_card (h : IsSp4FourBlock L) :
    Nat.card (BlockModule L) = 2 ^ 8 := by
  obtain ⟨_, F, _, _, hF, rho, ⟨model⟩, _⟩ := h
  have hc := Nat.card_congr model.moduleIso.toEquiv
  change Nat.card (BlockModule L) = Nat.card ((Fin 2 ⊕ Fin 2) → F) at hc
  rw [Nat.card_fun, hF, Nat.card_eq_fintype_card (α := Fin 2 ⊕ Fin 2)] at hc
  simpa using hc

/-- The natural alternating module has dimension `n-1` in odd degree. -/
theorem IsAlternatingBlock.module_card_odd {n : Nat}
    (h : IsAlternatingBlock L n) (hn : Odd n) :
    Nat.card (BlockModule L) = 2 ^ (n - 1) := by
  have hge := h.1
  have : NeZero n := ⟨by omega⟩
  rw [h.2.2.module_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, BinaryPermutation.finrank_natural_odd (Fin n) (by simpa using hn)]
  simp

/-- In even degree both the constant line and the augmentation factor are removed. -/
theorem IsAlternatingBlock.module_card_even {n : Nat}
    (h : IsAlternatingBlock L n) (hn : Even n) :
    Nat.card (BlockModule L) = 2 ^ (n - 2) := by
  have hge := h.1
  have : NeZero n := ⟨by omega⟩
  rw [h.2.2.module_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, BinaryPermutation.finrank_natural_even (Fin n) (by simpa using hn)]
  simp

/-- Membership in `chi_0` implies membership in `chi`. -/
theorem IsChiZeroBlock.chi (h : IsChiZeroBlock L) : IsChiBlock L := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨3, by decide, h⟩
  · exact Or.inr ⟨5, by decide, h⟩

theorem IsChiBlock.short (h : IsChiBlock L) : IsShort L := by
  rcases h with ⟨n, hn⟩ | ⟨n, _, hn⟩
  · exact hn.2.1
  · exact hn.2.1

/-- The exceptional condition specifies the order of the actual module quotient. -/
theorem IsExceptionalA7Block.module_card (h : IsExceptionalA7Block L) :
    Nat.card (BlockModule L) = 16 := h.2.2

/-- The ordinary alternating block and exceptional `A₇` block are distinct types. -/
theorem IsAlternatingBlock.not_exceptionalA7 (h : IsAlternatingBlock L 7) :
    ¬ IsExceptionalA7Block L := by
  intro he
  have hc := h.module_card_odd (by decide)
  rw [he.module_card] at hc
  norm_num at hc

/-- The defining faithfulness condition is retained verbatim. -/
theorem IsExceptionalAhat6Block.centralizer (h : IsExceptionalAhat6Block L) :
    Subgroup.centralizer (blockU L : Set L) = pCore 2 L := h.2.2.2.2.2

variable {G : Type*} [Group G]

/-- An ambient block of a prescribed intrinsic type. This supplies the
subnormality condition in the last sentence of C.1.12. -/
def IsBlockOfType (K : Subgroup G) (type : Prop) : Prop := IsBlock K ∧ type

/-- A `chi`-block of the ambient group. -/
abbrev IsChiBlockIn (K : Subgroup G) : Prop := IsBlockOfType K (IsChiBlock K)

/-- A `chi_0`-block of the ambient group. -/
abbrev IsChiZeroBlockIn (K : Subgroup G) : Prop := IsBlockOfType K (IsChiZeroBlock K)

theorem IsChiZeroBlockIn.chi {K : Subgroup G} (h : IsChiZeroBlockIn K) :
    IsChiBlockIn K := ⟨h.1, h.2.chi⟩

end CFSG.Quasithin.ChapterC

end
