module

public import Theory.GroupTheory.NormalClosureProductExchange
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-!
# Correcting a factor exchanger to an involution

Suppose the stabilizer of each of two commuting disjoint factors is their
product. An exchanger has square uv in that product. Uniqueness of the
factor coordinates shows that conjugation by the exchanger carries u to v.
Multiplying the exchanger by u⁻¹ therefore makes its square one. Every ambient
element either fixes the factors or is in this involution's product coset.

Source application: Aschbacher–Smith, G.6.4(3), printed p.346.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem map_conj_mul (A : Subgroup G) (x y : G) :
    A.map (MulAut.conj (x * y)).toMonoidHom =
      (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  change (x * y) * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹
  group

/-- An actual exchanged direct product with no larger factor stabilizer splits. -/
theorem exists_involutive_exchange_of_normalClosure_product
    (A B : Subgroup G) (a : G) (ha : a ∈ A)
    (hjoin : A ⊔ B = normalClosure ({a} : Set G))
    (hdis : Disjoint A B) (hcomm : ⁅A, B⁆ = ⊥) (hB : B ≠ ⊥)
    (hperm : ∀ g : G,
      (A.map (MulAut.conj g).toMonoidHom = A ∧
        B.map (MulAut.conj g).toMonoidHom = B) ∨
      (A.map (MulAut.conj g).toMonoidHom = B ∧
        B.map (MulAut.conj g).toMonoidHom = A))
    (hstab : ∀ g : G, A.map (MulAut.conj g).toMonoidHom = A →
      B.map (MulAut.conj g).toMonoidHom = B → g ∈ normalClosure ({a} : Set G)) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧
      normalClosure ({a} : Set G) ⊔ zpowers t = ⊤ ∧
      A.map (MulAut.conj t).toMonoidHom = B := by
  have hBA : B ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [hcomm]
    exact bot_le
  have hAB : A ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [commutator_comm, hcomm]
    exact bot_le
  have hinner (k : G) (hk : k ∈ A ⊔ B) :
      A.map (MulAut.conj k).toMonoidHom = A ∧
      B.map (MulAut.conj k).toMonoidHom = B :=
    ⟨mem_normalizer_iff_map_conj_eq.mp ((sup_le A.le_normalizer hBA) hk),
      mem_normalizer_iff_map_conj_eq.mp ((sup_le hAB B.le_normalizer) hk)⟩
  have hcommute (u : G) (hu : u ∈ A) (v : G) (hv : v ∈ B) : u * v = v * u :=
    (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hu) v hv).symm
  obtain ⟨g, hgA, hgB⟩ := exists_exchange_of_normalClosure_product A B a ha hjoin hdis hB hperm
  have hsq : g * g ∈ A ⊔ B := by
    rw [hjoin]
    apply hstab
    · rw [map_conj_mul, hgA, hgB]
    · rw [map_conj_mul, hgB, hgA]
  have hsq' : g * g ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hBA]
    exact hsq
  obtain ⟨u, hu, v, hv, huv⟩ := hsq'
  change u * v = g * g at huv
  have hgu : g * u * g⁻¹ ∈ B := by
    rw [← hgA]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom hu
  have hgv : g * v * g⁻¹ ∈ A := by
    rw [← hgB]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom hv
  have hconj : (g * v * g⁻¹) * (g * u * g⁻¹) = u * v := by
    calc
      _ = g * (v * u) * g⁻¹ := by group
      _ = g * (u * v) * g⁻¹ := by rw [hcommute u hu v hv]
      _ = u * v := by rw [huv]; group
  have he : ((⟨g * v * g⁻¹, hgv⟩, ⟨g * u * g⁻¹, hgu⟩) : A × B) =
      (⟨u, hu⟩, ⟨v, hv⟩) := by
    apply mul_injective_of_disjoint hdis
    exact hconj
  have hguv : g * u * g⁻¹ = v := congrArg (fun p : A × B => (p.2 : G)) he
  let t := u⁻¹ * g
  have ht : t * t = 1 := by
    calc
      _ = u⁻¹ * (g * u * g⁻¹)⁻¹ * (g * g) := by dsimp [t]; group
      _ = u⁻¹ * v⁻¹ * (u * v) := by rw [hguv, ← huv]
      _ = (v * u)⁻¹ * (u * v) := by rw [mul_inv_rev]
      _ = 1 := by rw [← hcommute u hu v hv, inv_mul_cancel]
  have hui := hinner u⁻¹ (mem_sup_left (A.inv_mem hu))
  have htA : A.map (MulAut.conj t).toMonoidHom = B := by
    rw [show t = u⁻¹ * g from rfl, map_conj_mul, hgA, hui.2]
  have htB : B.map (MulAut.conj t).toMonoidHom = A := by
    rw [show t = u⁻¹ * g from rfl, map_conj_mul, hgB, hui.1]
  have htne : t ≠ 1 := by
    intro heq
    have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    have hab : A = B := by
      simpa only [heq, hone, Subgroup.map_id] using htA
    apply hB
    simpa only [hab, inf_idem] using hdis.eq_bot
  refine ⟨t, htne, by simpa only [pow_two] using ht, ?_, htA⟩
  apply top_unique
  intro x _
  rcases hperm x with ⟨hxA, hxB⟩ | ⟨hxA, hxB⟩
  · exact mem_sup_left (hstab x hxA hxB)
  · have hx : x * t ∈ normalClosure ({a} : Set G) := by
      apply hstab
      · rw [map_conj_mul, htA, hxB]
      · rw [map_conj_mul, htB, hxA]
    have hxt : (x * t) * t ∈ normalClosure ({a} : Set G) ⊔ zpowers t :=
      (normalClosure ({a} : Set G) ⊔ zpowers t).mul_mem
        (mem_sup_left hx) (mem_sup_right (mem_zpowers t))
    simpa only [mul_assoc, ht, mul_one] using hxt

end Theory.GroupTheory
