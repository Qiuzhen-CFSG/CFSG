module

public import Theory.GroupTheory.QuaternionCentralizerCoreTransfer
public import Theory.GroupTheory.CentralProductElementaryTransfer
public import Theory.GroupTheory.PGroup.CentralProductProjection
public import Theory.GroupTheory.PGroup.RankOneInvolution
public import Theory.GroupTheory.SpecificGroups.QuaternionCentralSquareEmbedding
public import Theory.PGroupCore
public import BenderSuzuki.External.Huppert.IV.Basic

/-!
# Quaternion-core transfer in a binary centralizer product

The centralizer projection of an elementary subgroup is a two-group. Joining
it with the quaternion core gives a two-group with no elementary four, hence
a generalized quaternion group. Every square in the projection is central
in this larger group, because it belongs to the overlap of the commuting
factors.

The central-square embedding puts this projection into the quaternion core,
preserving the overlap with the other factor. The multiplication maps then
have the same kernel, so the elementary subgroup transfers without changing
its cardinality. In particular an elementary eight transfers into the product
with the core. The solvability, odd-core, and rank-two assumptions of the
campaign statement are not needed for this transfer step.

This is the quaternion-core case in the binary centralizer argument associated
with the remark following GLS, Number 2, Proposition 22.4
(`refs/KGroup/GLS2/ChapterF.tex`). The projection, quaternion geometry, and
gluing arguments are intrinsic lemmas in `Theory`.
-/

namespace Stellmacher

open Subgroup
open scoped IsMulCommutative

/-- The centralizer projection can be placed in a generalized quaternion
two-group containing the two-core, with all its squares central there. -/
public theorem exists_quaternion_centralizer_projection
    {H : Type*} [Group H] [Finite H] (Q B : Subgroup H)
    (hQ : IsPGroup 2 Q)
    (hgen : Q ⊔ centralizer (Q : Set H) = ⊤)
    (hfour : ∀ F : Subgroup (centralizer (Q : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4)
    (hcore : Nonempty (pCore 2 (centralizer (Q : Set H)) ≃* QuaternionGroup 2))
    [IsElementaryAbelian 2 B] :
    ∃ R T : Subgroup (centralizer (Q : Set H)),
      pCore 2 (centralizer (Q : Set H)) ≤ R ∧ T ≤ R ∧ IsPGroup 2 R ∧
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (R ≃* QuaternionGroup (2 ^ (n - 2)))) ∧
      B ≤ Q ⊔ T.map (centralizer (Q : Set H)).subtype ∧
      ∀ t : T, ∀ ht : (t : centralizer (Q : Set H)) ∈ R,
        (⟨t, ht⟩ : R) ^ 2 ∈ center R := by
  exact Subgroup.exists_quaternion_centralizer_projection Q B hQ hgen hfour hcore

/-- An elementary subgroup of a binary centralizer product has an elementary
copy of the same order in the product with the quaternion two-core. -/
public theorem exists_elementary_subgroup_quaternion_core_of_card_eq
    {H : Type*} [Group H] [Finite H] (Q B : Subgroup H)
    (hQ : IsPGroup 2 Q)
    (hgen : Q ⊔ centralizer (Q : Set H) = ⊤)
    (hfour : ∀ F : Subgroup (centralizer (Q : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4)
    (hcore : Nonempty (pCore 2 (centralizer (Q : Set H)) ≃* QuaternionGroup 2))
    [IsElementaryAbelian 2 B] :
    ∃ D : Subgroup H,
      D ≤ Q ⊔ (pCore 2 (centralizer (Q : Set H))).map
        (centralizer (Q : Set H)).subtype ∧
      IsElementaryAbelian 2 D ∧ Nat.card D = Nat.card B := by
  exact Subgroup.exists_elementary_subgroup_quaternion_core_of_card_eq Q B hQ hgen hfour hcore

/-- Quaternion-core transfer for an elementary subgroup of order at least eight. -/
public theorem exists_elementary_eight_quaternion_core
    {H : Type*} [Group H] [Finite H] (Q B : Subgroup H)
    (hQ : IsPGroup 2 Q)
    (hgen : Q ⊔ centralizer (Q : Set H) = ⊤)
    (hfour : ∀ F : Subgroup (centralizer (Q : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4)
    (hcore : Nonempty (pCore 2 (centralizer (Q : Set H)) ≃* QuaternionGroup 2))
    [IsElementaryAbelian 2 B] (hB : 8 ≤ Nat.card B) :
    ∃ D : Subgroup H,
      D ≤ Q ⊔ (pCore 2 (centralizer (Q : Set H))).map
        (centralizer (Q : Set H)).subtype ∧
      IsElementaryAbelian 2 D ∧ 8 ≤ Nat.card D := by
  exact Subgroup.exists_elementary_eight_quaternion_core Q B hQ hgen hfour hcore hB

/-- The quaternion-core case of binary centralizer transfer, with the full
hypotheses of the binary rank-two centralizer reduction. -/
public theorem binaryCentralizer_quaternion_core_transfer
    {H : Type*} [Group H] [Finite H] [Group.IsSolvable H]
    (Q E B : Subgroup H) (hQ : IsPGroup 2 Q)
    (hgen : Q ⊔ centralizer (Q : Set H) = ⊤)
    (_hodd : pPrimeCore 2 (centralizer (Q : Set H)) = ⊥)
    (_hEQ : E ≤ Q) (_hE : IsElementaryAbelian 2 E) (_hEcard : 4 ≤ Nat.card E)
    (_hQrank : ∀ F : Subgroup Q, IsElementaryAbelian 2 F → Nat.card F < 8)
    (hCrank : ∀ F : Subgroup (centralizer (Q : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4)
    (hcore : Nonempty (pCore 2 (centralizer (Q : Set H)) ≃* QuaternionGroup 2))
    (hB : IsElementaryAbelian 2 B) (hBcard : 8 ≤ Nat.card B) :
    ∃ D : Subgroup H,
      D ≤ Q ⊔ (pCore 2 (centralizer (Q : Set H))).map
        (centralizer (Q : Set H)).subtype ∧
      IsElementaryAbelian 2 D ∧ 8 ≤ Nat.card D := by
  let := hB
  exact exists_elementary_eight_quaternion_core Q B hQ hgen hCrank hcore hBcard

end Stellmacher
