module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Commute.Basic

/-!
# Splitting an abelian root normalizer

If a subgroup of an abelian root normalizer acts transitively on the
nonidentity root elements, every element of the normalizer can be adjusted
by that subgroup to centralize the whole root. Commutativity propagates
fixing one root element to fixing all of them.

The application is the full Cartan decomposition used in DGS, Groups and
Graphs (1985), (14.5)--(14.6), pp.213--214. No faithful root action or
trivial actor kernel is assumed.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory
variable {X : Type*} [Group X]

/-- An abelian normalizer splits over a subgroup transitive on the
nonidentity elements of its normalized group. -/
theorem abelian_normalizer_eq_sup_root_centralizer
    (K C R : Subgroup X) [IsMulCommutative K]
    (hCK : C ≤ K) (hn : K ≤ normalizer (R : Set X))
    (hne : R ≠ ⊥)
    (htrans : ∀ x∈R, ∀ y∈R, x≠1 → y≠1 → ∃ c∈C, c*x*c⁻¹=y) :
    K = C ⊔ (K ⊓ centralizer (R : Set X)) := by
  obtain ⟨x,hx,hx1⟩ := R.bot_or_exists_ne_one.resolve_left hne
  apply le_antisymm ?_ (sup_le hCK inf_le_left)
  intro k hk
  have hy : k*x*k⁻¹∈R := (mem_normalizer_iff.mp (hn hk) x).mp hx
  have hy1 : k*x*k⁻¹≠1 := by
    intro he
    have := (MulAut.conj k).injective (he.trans (map_one (MulAut.conj k)).symm)
    exact hx1 this
  obtain ⟨c,hc,he⟩ := htrans x hx _ hy hx1 hy1
  let d := c⁻¹*k
  have hdK : d∈K := K.mul_mem (K.inv_mem (hCK hc)) hk
  have hdx : d*x*d⁻¹=x := by
    calc
      d*x*d⁻¹ = c⁻¹*(k*x*k⁻¹)*c := by simp only [d,mul_inv_rev,inv_inv,mul_assoc]
      _ = x := by rw [←he]; simp [mul_assoc]
  have hdR : d∈centralizer (R : Set X) := by
    intro y hy
    by_cases hy1 : y=1
    · simp [hy1]
    obtain ⟨b,hb,rfl⟩ := htrans x hx y hy hx1 hy1
    have hdb : Commute d b := by
      exact congrArg Subtype.val (mul_comm' (⟨d,hdK⟩ : K) ⟨b,hCK hb⟩)
    have hdx' : Commute d x := mul_inv_eq_iff_eq_mul.mp hdx
    exact (hdb.mul_right hdx' |>.mul_right hdb.inv_right).symm.eq
  have hm : c*d ∈ C ⊔ (K ⊓ centralizer (R : Set X)) :=
    mul_mem (show c∈C ⊔ (K ⊓ centralizer (R : Set X)) from
      (show C ≤ C ⊔ (K ⊓ centralizer (R : Set X)) from le_sup_left) hc)
      ((show K ⊓ centralizer (R : Set X) ≤ C ⊔ (K ⊓ centralizer (R : Set X)) from le_sup_right) ⟨hdK,hdR⟩)
  simpa only [d,mul_inv_cancel_left] using hm

end Theory.GroupTheory
