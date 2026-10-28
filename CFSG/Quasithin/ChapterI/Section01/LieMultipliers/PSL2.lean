module

public import GorensteinWalter.PSL2FourUniversalCover
public import GorensteinWalter.PSL2SchurMultiplier
public import Theory.GroupTheory.CoveringKernelEquiv

/-!
# PSL₂ inputs to the multiplier tables I.1.3–I.1.4

The actual SL₂ projection is universal over every field of odd order
greater than three, except order nine, and its kernel is C₂. For even
order at least eight, the identity cover is universal and its kernel is
trivial. At order four the explicit universal covering group is SL₂(5),
transported through the concrete A₅ comparisons. All three branches
supply finite quasisimple covers and full universality.

The defining-prime exclusions discharge the last kernel bounds in the
ordinary branches. Kernel comparison then gives the same group structure
for any chosen universal cover. The order-nine C₆ case remains separate
and belongs to the A₆ calculation, through the actual exceptional
isomorphism; no order-nine universality or triviality is asserted here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.1.3(1),(3), I.1.4(1), printed pp.407–408 (PDF pp.418–419).
-/

namespace CFSG.Quasithin.ChapterI.LieMultipliers.PSL2

open Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups

universe u w

public local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
public local instance : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩

/-- The prime-field branch, with the canonical covering and its actual kernel. -/
public theorem primeField_universalCover
    (F : Type u) [Field F] [Finite F]
    (hcard : 3 < Nat.card F) (hp : (Nat.card F).Prime) :
    letI : Fact (3 < Nat.card F) := ⟨hcard⟩
    Covering.IsUniversal.{u, u, w} (PSL2Cover.cover F) ∧
      Nonempty ((PSL2Cover.cover F).toMonoidHom.ker ≃* Multiplicative (ZMod 2)) := by
  let : Fact (3 < Nat.card F) := ⟨hcard⟩
  exact ⟨PSL2Cover.isUniversal_of_card_prime F hp,
    ⟨PSL2Cover.kernelEquivTwo F (hp.odd_of_ne_two (by omega))⟩⟩

/-- The ordinary odd-field branch of I.1.3(1) and I.1.4(1), with the
actual SL₂ covering and the full C₂ kernel isomorphism. -/
public theorem odd_universalCover
    (F : Type u) [Field F] [Finite F]
    (hcard : 3 < Nat.card F) (ho : Odd (Nat.card F)) (h9 : Nat.card F ≠ 9) :
    letI : Fact (3 < Nat.card F) := ⟨hcard⟩
    Covering.IsUniversal.{u, u, w} (PSL2Cover.cover F) ∧
      Nonempty ((PSL2Cover.cover F).toMonoidHom.ker ≃* Multiplicative (ZMod 2)) := by
  let : Fact (3 < Nat.card F) := ⟨hcard⟩
  exact ⟨PSL2Cover.isUniversal_of_odd F ho h9, ⟨PSL2Cover.kernelEquivTwo F ho⟩⟩

/-- The even-field branch omitted from the nontrivial multiplier tables:
for q ≥ 8 the actual identity cover is universal with trivial kernel. -/
public theorem even_universalCover
    (F : Type u) [Field F] [Finite F]
    (hcard : 8 ≤ Nat.card F) (he : Even (Nat.card F)) :
    letI : Fact (3 < Nat.card F) := ⟨by omega⟩
    Covering.IsUniversal.{u, u, w} (Covering.id : Covering PSL(2, F) PSL(2, F)) ∧
      Nonempty ((Covering.id : Covering PSL(2, F) PSL(2, F)).toMonoidHom.ker ≃* PUnit) := by
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  exact ⟨PSL2Cover.identity_isUniversal_of_even F he hcard, ⟨PSL2Cover.identityKernelEquivOne F⟩⟩

/-- The exceptional order-four branch, with explicit covering group SL₂(5). -/
public theorem four_universalCover
    (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 4) :
    letI : Fact (3 < Nat.card F) := ⟨by omega⟩
    Covering.IsUniversal.{u, 0, w} (PSL2Cover.fourCover F hF) ∧
      Nonempty ((PSL2Cover.fourCover F hF).toMonoidHom.ker ≃* Multiplicative (ZMod 2)) := by
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  exact ⟨PSL2Cover.fourCover_isUniversal F hF, ⟨PSL2Cover.fourKernelEquivTwo F hF⟩⟩

/-- The prime-field calculation for any chosen universal cover, retaining
the group structure of its kernel and the literal PSL₂ base. -/
public noncomputable def primeFieldMultiplierEquiv
    (F : Type u) [Field F] [Finite F] [Fact (3 < Nat.card F)]
    {E : Type u} [Group E] [Finite E] [IsQuasisimple E]
    (g : Covering E PSL(2, F)) (hg : Covering.IsUniversal.{u, u, u} g)
    (hp : (Nat.card F).Prime) : g.toMonoidHom.ker ≃* Multiplicative (ZMod 2) :=
  (hg.kerMulEquiv (PSL2Cover.isUniversal_of_card_prime F hp) (MulEquiv.refl _)).trans
    (PSL2Cover.kernelEquivTwo F
      (hp.odd_of_ne_two (by have := Fact.out (p := 3 < Nat.card F); omega)))

/-- The multiplier of any chosen universal cover of odd PSL₂(q), q > 3,
q ≠ 9, is C₂. The universal property is used only to compare the choice
with the explicit cover already proved universal above. -/
public noncomputable def oddMultiplierEquiv
    (F : Type u) [Field F] [Finite F] [Fact (3 < Nat.card F)]
    {E : Type u} [Group E] [Finite E] [IsQuasisimple E]
    (g : Covering E PSL(2, F)) (hg : Covering.IsUniversal.{u, u, u} g)
    (ho : Odd (Nat.card F)) (h9 : Nat.card F ≠ 9) :
    g.toMonoidHom.ker ≃* Multiplicative (ZMod 2) :=
  (hg.kerMulEquiv (PSL2Cover.isUniversal_of_odd F ho h9) (MulEquiv.refl _)).trans
    (PSL2Cover.kernelEquivTwo F ho)

/-- The multiplier of any chosen universal cover of even PSL₂(q), q ≥ 8,
is trivial, by comparison with the proved universal identity cover. -/
public noncomputable def evenMultiplierEquiv
    (F : Type u) [Field F] [Finite F] [Fact (3 < Nat.card F)]
    {E : Type u} [Group E] [Finite E] [IsQuasisimple E]
    (g : Covering E PSL(2, F)) (hg : Covering.IsUniversal.{u, u, u} g)
    (hcard : 8 ≤ Nat.card F) (he : Even (Nat.card F)) :
    g.toMonoidHom.ker ≃* PUnit :=
  (hg.kerMulEquiv (PSL2Cover.identity_isUniversal_of_even F he hcard)
    (MulEquiv.refl _)).trans (PSL2Cover.identityKernelEquivOne F)

end CFSG.Quasithin.ChapterI.LieMultipliers.PSL2
