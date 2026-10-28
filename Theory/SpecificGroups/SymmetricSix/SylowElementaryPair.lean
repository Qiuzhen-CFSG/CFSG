module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.TwoElementaryIndexTwo
import Mathlib.Tactic
/-!
# Elementary subgroups of a Sylow two-subgroup of S₆ × C₂

An explicit faithful permutation embedding realizes D₈ × C₂ × C₂ as a
Sylow two-subgroup of S₆ × C₂. Its two elementary sixteen-groups have index
two. The general two-index-two-subgroup lemma shows that they contain all
elementary subgroups. Sylow conjugacy transports this pair to any Sylow
subgroup, through an actual multiplicative equivalence.

All finite coordinate identities below are checked by the Lean kernel.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
open Subgroup Equiv Equiv.Perm
namespace SymmetricSix.SylowElementaryPair
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
abbrev C2 := Multiplicative (ZMod 2)
abbrev Model := DihedralGroup 4 × C2 × C2
abbrev Binary := Multiplicative (Fin 4 → ZMod 2)
abbrev Product := Perm (Fin 6) × C2

def rotation : Perm (Fin 6) := swap 0 1 * (swap 0 2 * swap 1 3)
def reflection : Perm (Fin 6) := swap 0 1

def dihedralPerm : DihedralGroup 4 → Perm (Fin 6)
  | .r i => rotation ^ i.val
  | .sr i => reflection * rotation ^ i.val

def embedding : Model →* Product where
  toFun x := (dihedralPerm x.1 * (if x.2.1.toAdd = 0 then 1 else swap 4 5), x.2.2)
  map_one' := rfl
  map_mul' := by decide +kernel

theorem embedding_injective : Function.Injective embedding := by decide +kernel

def pairHom (b : Fin 2) : Binary →* Model where
  toFun v := ((if v.toAdd 0 = 0 then 1 else DihedralGroup.r 2) *
    (if v.toAdd 1 = 0 then 1 else DihedralGroup.sr b.val),
    Multiplicative.ofAdd (v.toAdd 2), Multiplicative.ofAdd (v.toAdd 3))
  map_one' := rfl
  map_mul' := by revert b; decide +kernel

theorem pairHom_injective (b : Fin 2) : Function.Injective (pairHom b) := by
  revert b; decide +kernel

def pair (b : Fin 2) : Subgroup Model := (pairHom b).range

instance binary_elementary : IsElementaryAbelian 2 Binary where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)
instance pair_elementary (b : Fin 2) : IsElementaryAbelian 2 (pair b) :=
  IsElementaryAbelian.of_surjective (pairHom b).rangeRestrict (pairHom b).rangeRestrict_surjective

theorem pair_card (b : Fin 2) : Nat.card (pair b) = 16 := by
  rw [pair, ← Nat.card_congr (MonoidHom.ofInjective (pairHom_injective b)).toEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem pair_ne : pair 0 ≠ pair 1 := by
  intro he
  have hm : (DihedralGroup.sr 0, 1, 1) ∈ pair 0 :=
    ⟨Multiplicative.ofAdd (Pi.single 1 1), by decide +kernel⟩
  rw [he] at hm
  have hn : ¬ ∃ v, pairHom 1 v = (DihedralGroup.sr 0, 1, 1) := by decide +kernel
  exact hn hm

theorem model_card : Nat.card Model = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem pair_index (b : Fin 2) : (pair b).index = 2 := by
  have hc := (pair b).card_mul_index
  rw [pair_card, model_card] at hc
  omega

theorem model_not_elementary : ¬ IsElementaryAbelian 2 Model := by
  intro h
  have he : ((DihedralGroup.r 1, 1, 1) : Model) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 Model) _
  have hn : ((DihedralGroup.r 1, 1, 1) : Model) ^ 2 ≠ 1 := by decide +kernel
  exact hn he

theorem elementary_cover (E : Subgroup Model) [IsElementaryAbelian 2 E] :
    E ≤ pair 0 ∨ E ≤ pair 1 :=
  elementary_le_one_of_two_index_two _ _ inferInstance inferInstance
    (pair_index 0) (pair_index 1) pair_ne model_not_elementary E inferInstance

def canonical : Subgroup Product := embedding.range

theorem canonical_card : Nat.card canonical = 32 := by
  rw [canonical, ← Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv, model_card]

theorem product_card : Nat.card Product = 1440 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

noncomputable def canonicalSylow : Sylow 2 Product :=
  (IsPGroup.of_card (p := 2) (n := 5) canonical_card).toSylow (by
    have h := canonical.card_mul_index
    rw [canonical_card, product_card] at h
    have hi : canonical.index = 45 := by omega
    rw [hi]
    decide)

noncomputable def sylowEquiv (P : Sylow 2 Product) : Model ≃* P :=
  (MonoidHom.ofInjective embedding_injective).trans (Sylow.equiv canonicalSylow P)

/-- The two elementary index-two subgroups in an arbitrary Sylow subgroup
of S₆ × C₂; every elementary subgroup is contained in one of them. -/
theorem pair_of_equiv {P : Type*} [Group P] [Finite P] (e : Model ≃* P) :
    ∃ A B : Subgroup P, A ≠ B ∧ IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A.index = 2 ∧ B.index = 2 ∧
      ∀ E : Subgroup P, IsElementaryAbelian 2 E → E ≤ A ∨ E ≤ B := by
  let A := (pair 0).map e.toMonoidHom
  let B := (pair 1).map e.toMonoidHom
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hAc : Nat.card A = 16 := (card_map_of_injective e.injective).trans (pair_card 0)
  have hBc : Nat.card B = 16 := (card_map_of_injective e.injective).trans (pair_card 1)
  have hP : Nat.card P = 32 := (Nat.card_congr e.toEquiv).symm.trans model_card
  have hAi : A.index = 2 := by have h := A.card_mul_index; rw [hAc, hP] at h; omega
  have hBi : B.index = 2 := by have h := B.card_mul_index; rw [hBc, hP] at h; omega
  have hne : A ≠ B := fun hh => pair_ne (e.mapSubgroup.injective hh)
  refine ⟨A, B, hne, hA, hB, hAc, hBc, hAi, hBi, ?_⟩
  intro E hE
  let := hE
  let F := E.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  have he : F.map e.toMonoidHom = E := e.mapSubgroup.apply_symm_apply E
  rcases elementary_cover F with ha | hb
  · exact Or.inl (he ▸ map_mono ha)
  · exact Or.inr (he ▸ map_mono hb)
/-- The pair in every actual Sylow subgroup of the permutation product. -/
theorem sylow_pair (P : Sylow 2 Product) :
    ∃ A B : Subgroup P, A ≠ B ∧ IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A.index = 2 ∧ B.index = 2 ∧
      ∀ E : Subgroup P, IsElementaryAbelian 2 E → E ≤ A ∨ E ≤ B :=
  pair_of_equiv (sylowEquiv P)

end SymmetricSix.SylowElementaryPair
