module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Rank
import all Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Rank
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.QuasithinBasic

/-!
# A rank-three odd subgroup in a proper binary D₄ two-local

The root involution with direction e₂ and parameter e₃ commutes with the
three A₁ generators used by `BinaryEightObstruction.embedding`. Thus its actual
centralizer contains the existing faithful elementary subgroup of order 27.
An opposite root fails to commute with the involution, proving properness.
All calculations take place in the Siegel-generated Omega group and are then
transported through its literal scalar quotient, whose injectivity is proved
in `BinaryEightObstruction.Rank`.

This is the local-rank obstruction at the binary D₄ endpoint of
Aschbacher–Smith A.2.18, printed p.40 (`refs/quasithin.pdf`). Its three A₁
generators are the Levi diagram obtained by deleting the central D₄ node
(GLS3 §2.6). The conclusion only needs the explicitly constructed two-local;
no assertion about simple sections of every D₄(2) parabolic is used.
The private import of `BinaryEightObstruction.Rank` is intentional: this
is an extension of that construction and needs its internal root-word action,
while its new public results refer only to the existing public embedding.
The coordinate lemmas are reused from `BinaryEightObstruction.Rank`,
using the Siegel construction attributed there to ATLAS.
-/

public noncomputable section
namespace ClassicalOrthogonal.A02ParabolicSections.BinaryD4
open Matrix
open ClassicalOrthogonal.BinaryEightObstruction

local notation "K" => ZMod 2
local notation "E" => OmegaPlus 4 (ZMod 2)
local notation "Q" => formD 4 (ZMod 2)

private theorem generators_commute_root (i : Fin 3) :
    Commute (generators i) (rootEE 2 3) := by
  apply representation_injective
  fin_cases i
  · change representation ((rootEF 0 1 _ * rootEF 1 0 _) * rootEE 2 3) =
      representation (rootEE 2 3 * (rootEF 0 1 _ * rootEF 1 0 _))
    simp only [map_mul, representation_rootEF, representation_rootEE]
    decide
  · change representation ((rootEE 0 1 * rootFF 0 1) * rootEE 2 3) =
      representation (rootEE 2 3 * (rootEE 0 1 * rootFF 0 1))
    simp only [map_mul, representation_rootFF, representation_rootEE]
    decide
  · change representation ((rootEF 2 3 _ * rootEF 3 2 _) * rootEE 2 3) =
      representation (rootEE 2 3 * (rootEF 2 3 _ * rootEF 3 2 _))
    simp only [map_mul, representation_rootEF, representation_rootEE]
    decide

private theorem embedding_commute_root (a : Fin 3 → Multiplicative (ZMod 3)) :
    Commute (embedding a) (rootEE 2 3) := by
  rw [embedding_apply]
  exact ((generators_commute_root 0).pow_left _).mul_left
    (((generators_commute_root 1).pow_left _).mul_left ((generators_commute_root 2).pow_left _))

/-- The root involution in the exact projective elementary carrier. -/
def involution : POmegaPlus 4 K := projectiveElementaryMap Q (rootEE 2 3)

/-- The root has order two before and after the literal projective map. -/
theorem involution_order : orderOf involution = 2 := by
  apply orderOf_eq_prime
  · change (projectiveElementaryMap Q (rootEE 2 3)) ^ 2 = 1
    rw [← map_pow]
    have h : rootEE 2 3 ^ 2 = 1 := by
      apply representation_injective
      rw [map_pow, map_one, representation_rootEE, pow_two]
      decide
    rw [h, map_one]
  · intro h
    have he : rootEE 2 3 = 1 := projectiveMap_injective (h.trans (map_one _).symm)
    have hm := congrArg representation he
    rw [representation_rootEE, map_one] at hm
    revert hm
    decide

/-- The literal centralizer of the root involution. -/
def localSubgroup : Subgroup (POmegaPlus 4 K) :=
  Subgroup.centralizer ({involution} : Set (POmegaPlus 4 K))

/-- It is the normalizer of a nontrivial two-subgroup. -/
theorem localSubgroup_isTwoLocal : IsTwoLocal localSubgroup :=
  Theory.GroupTheory.isTwoLocal_involution_centralizer involution_order

/-- An opposite root witnesses that this two-local is proper. -/
theorem localSubgroup_ne_top : localSubgroup ≠ ⊤ := by
  intro h
  have hm : projectiveElementaryMap Q (rootFF 2 3) ∈ localSubgroup := by
    rw [h]
    trivial
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hm
  change projectiveElementaryMap Q (rootFF 2 3) * projectiveElementaryMap Q (rootEE 2 3) =
    projectiveElementaryMap Q (rootEE 2 3) * projectiveElementaryMap Q (rootFF 2 3) at hc
  rw [← map_mul, ← map_mul] at hc
  have hr := congrArg representation (projectiveMap_injective hc)
  simp only [map_mul, representation_rootEE, representation_rootFF] at hr
  revert hr
  decide

/-- The previously constructed elementary group of order 27 lies in this local. -/
def localEmbedding : (Fin 3 → Multiplicative (ZMod 3)) →* localSubgroup :=
  projectiveEmbedding.codRestrict localSubgroup (fun a =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((embedding_commute_root a).map (projectiveElementaryMap Q)))

/-- This is the existing marked projective embedding, with only its codomain restricted. -/
@[simp] theorem localEmbedding_val (a : Fin 3 → Multiplicative (ZMod 3)) :
    (localEmbedding a).val = projectiveEmbedding a := by rfl

theorem localEmbedding_injective : Function.Injective localEmbedding := by
  intro a b hab
  exact projectiveEmbedding_injective (congrArg Subtype.val hab)

/-- The proper two-local has 3-rank at least three. -/
theorem localSubgroup_rank : 3 ≤ primeRank 3 localSubgroup := by
  have hp : ∀ a : Fin 3 → Multiplicative (ZMod 3), a ^ 3 = 1 := by
    intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 (a i).toAdd)
  have hc : Nat.card (Fin 3 → Multiplicative (ZMod 3)) = 3 ^ 3 := by
    simp [Nat.card_eq_fintype_card]
  exact primeRank_ge_of_elementary_embedding hp hc localEmbedding localEmbedding_injective

/-- The actual binary split-eight model fails the two-local quasithin rank bound. -/
theorem not_quasithin : ¬ IsQuasithin (POmegaPlus 4 K) := by
  intro h
  have hb := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp h localSubgroup
    localSubgroup_isTwoLocal 3 (by decide) (by decide)
  have hr := localSubgroup_rank
  omega

end ClassicalOrthogonal.A02ParabolicSections.BinaryD4
