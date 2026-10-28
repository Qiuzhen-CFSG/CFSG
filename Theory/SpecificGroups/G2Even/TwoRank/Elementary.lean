module

public import Theory.AtlasPort.LinearGroups.G2.Unipotent
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Two

/-!
# An elementary subgroup of order q³ in even G₂

The first three positive root groups commute. Their ordered product embeds
three copies of the additive field in the actual split-octonion group.

Source: Aschbacher–Smith, rank table on printed p.356 and the rank inspection
in 16.3.9, printed p.1180. The root coordinates and multiplication law are
from the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

@[expose] public section

namespace Atlas.G2.EvenTwoRank
variable (F : Type*) [Field F]

/-- The three commuting positive root parameters. -/
def elementaryParameters (v : Fin 3 → F) : Fin 6 → F :=
  ![v 0, v 1, v 2, 0, 0, 0]

/-- The actual A-, B-, and C-root embedding. -/
def elementaryEmbedding : Multiplicative (Fin 3 → F) →* Model F where
  toFun v := unipotentProduct (elementaryParameters F v.toAdd)
  map_one' := by simp [elementaryParameters, unipotentProduct]
  map_mul' v w := by
    rw [unipotentProduct_mul]
    apply congrArg unipotentProduct
    funext i
    fin_cases i <;> simp [elementaryParameters, unipotentProductParameters, add_comm]

theorem elementaryEmbedding_injective : Function.Injective (elementaryEmbedding F) := by
  intro v w h
  have hp := unipotentProduct_injective h
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact congrFun hp 0
  · exact congrFun hp 1
  · exact congrFun hp 2

/-- The elementary root subgroup inside the octonion model. -/
def elementary : Subgroup (Model F) := (elementaryEmbedding F).range

noncomputable def elementaryEquiv : Multiplicative (Fin 3 → F) ≃* elementary F :=
  MonoidHom.ofInjective (elementaryEmbedding_injective F)

instance [CharP F 2] : IsElementaryAbelian 2 (elementary F) where
  toIsMulCommutative := inferInstanceAs (IsMulCommutative (elementaryEmbedding F).range)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
    obtain ⟨v, rfl⟩ := (elementaryEquiv F).surjective x
    rw [← map_pow]
    have hv : v ^ 2 = 1 := by
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      change v.toAdd + v.toAdd = 0
      funext i
      exact CharTwo.add_self_eq_zero _
    rw [hv, map_one]

theorem elementary_card [Finite F] : Nat.card (elementary F) = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (elementaryEquiv F).toEquiv]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]

theorem elementary_le_unipotent : elementary F ≤ unipotent := by
  rintro g ⟨v, rfl⟩
  exact unipotentProduct_mem _

/-- The full G₂ model has an elementary abelian subgroup of rank 3n. -/
theorem rank_ge [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    3 * n ≤ primeRank 2 (Model F) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  apply primeRank_ge_of_elementary_embedding (f := elementaryEmbedding F)
      (hf := elementaryEmbedding_injective F)
  · intro v
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    change v.toAdd + v.toAdd = 0
    funext i
    exact CharTwo.add_self_eq_zero _
  · rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
      hF, ← pow_mul, Nat.mul_comm n 3]

end Atlas.G2.EvenTwoRank
