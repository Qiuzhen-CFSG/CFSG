module

public import Theory.GroupTheory.PairedInvolutiveExtension.Centralizers
public import Mathlib.GroupTheory.Sylow

/-!
# Normalizers of paired base subgroups

An involution-stable self-normalizing subgroup D of a finite group K has
normalizer (D × D)⋊(C₂ × C₂) in the paired extension. The actor preserves
the base product, so the remaining normalizer conditions are the two
coordinate normalizer conditions. If D × D is Sylow in K × K, every
p-subgroup containing its embedded image normalizes that image: its
intersection with the normal base is already the indicated Sylow subgroup.

Source application: the paired Sylow recognition in Aschbacher--Smith,
proof of 2.4.34, printed p.548 of the 1 March 2004 manuscript.
-/

@[expose] public section
namespace Theory.GroupTheory.PairedInvolutiveExtension
open Subgroup
variable {K : Type*} [Group K] (α : MulAut K) (hα : Function.Involutive α)
/-- The embedded product of two copies of D, with trivial actor. -/
def baseSubgroup (D : Subgroup K) : Subgroup (Model α hα) :=
  (D.prod D).map SemidirectProduct.inl
@[simp] theorem mem_baseSubgroup (D : Subgroup K) (x : Model α hα) :
    x ∈ baseSubgroup α hα D ↔ x.right = 1 ∧ x.left.1 ∈ D ∧ x.left.2 ∈ D := by
  constructor
  · rintro ⟨⟨a,b⟩, hab, rfl⟩
    exact ⟨rfl, hab⟩
  · rintro ⟨hx,hab⟩
    exact ⟨x.left, hab, SemidirectProduct.ext rfl hx.symm⟩
@[simp] theorem base_mem_baseSubgroup (D : Subgroup K) (a b : K) :
    base α hα a b ∈ baseSubgroup α hα D ↔ a ∈ D ∧ b ∈ D := by
  rw [mem_baseSubgroup]
  change (1 = (1 : Bit × Bit) ∧ a ∈ D ∧ b ∈ D) ↔ _
  simp only [true_and]
private theorem action_mem_iff (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D)
    (p q : Bit) (a b : K) :
    (action α hα (p,q) (a,b)).1 ∈ D ∧ (action α hα (p,q) (a,b)).2 ∈ D ↔
      a ∈ D ∧ b ∈ D := by
  have hi (c : K) : α c ∈ D ↔ c ∈ D := ⟨fun hc => hα c ▸ hD _ hc, hD c⟩
  rcases bit_cases p with rfl | rfl <;> rcases bit_cases q with rfl | rfl <;>
    simp [hi, and_comm]
private theorem actor_mem_normalizer [Finite K] (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D)
    (p q : Bit) : mk α hα 1 1 p q ∈ normalizer (baseSubgroup α hα D : Set (Model α hα)) := by
  let : Finite (Model α hα) :=
    Finite.of_equiv ((K × K) × (Bit × Bit)) SemidirectProduct.equivProd.symm
  apply mem_normalizer_fintype
  rintro _ ⟨⟨a,b⟩,hab,rfl⟩
  change SemidirectProduct.inr (p,q) * SemidirectProduct.inl (a,b) *
    (SemidirectProduct.inr (p,q))⁻¹ ∈ baseSubgroup α hα D
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  exact mem_map_of_mem _ ((action_mem_iff α hα D hD p q a b).mpr hab)
private theorem base_mem_normalizer_iff [Finite K] (D : Subgroup K) (a b : K) :
    base α hα a b ∈ normalizer (baseSubgroup α hα D : Set (Model α hα)) ↔
      a ∈ normalizer (D : Set K) ∧ b ∈ normalizer (D : Set K) := by
  constructor
  · intro h
    rw [mem_normalizer_iff] at h
    constructor
    · rw [mem_normalizer_iff]
      intro c
      simpa only [base_conj,base_mem_baseSubgroup, D.one_mem, and_true, mul_one,
        mul_inv_cancel] using h (base α hα c 1)
    · rw [mem_normalizer_iff]
      intro d
      simpa only [base_conj,base_mem_baseSubgroup, D.one_mem, true_and, mul_one,
        mul_inv_cancel] using h (base α hα 1 d)
  · rintro ⟨ha,hb⟩
    let : Finite (Model α hα) :=
      Finite.of_equiv ((K × K) × (Bit × Bit)) SemidirectProduct.equivProd.symm
    apply mem_normalizer_fintype
    rintro _ ⟨⟨c,d⟩,hcd,rfl⟩
    change base α hα a b * base α hα c d * (base α hα a b)⁻¹ ∈ _
    rw [base_conj]
    apply (base_mem_baseSubgroup α hα D _ _).mpr
    exact ⟨(mem_normalizer_iff.mp ha c).mp hcd.1,(mem_normalizer_iff.mp hb d).mp hcd.2⟩

/-- Self-normalizing coordinate subgroups give the full paired normalizer. -/
theorem normalizer_baseSubgroup [Finite K] (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D)
    (hself : normalizer (D : Set K) = D) :
    normalizer (baseSubgroup α hα D : Set (Model α hα)) = subgroup α hα D hD := by
  ext x
  have hx : x = base α hα x.left.1 x.left.2 * mk α hα 1 1 x.right.1 x.right.2 := by
    exact (SemidirectProduct.inl_left_mul_inr_right x).symm
  rw [hx, (normalizer _).mul_mem_cancel_right (actor_mem_normalizer α hα D hD _ _),
    base_mem_normalizer_iff, hself,mem_subgroup]
  change _ ↔ (x.left.1 * 1 ∈ D ∧ x.left.2 * 1 ∈ D)
  simp only [mul_one]
/-- A p-subgroup containing the Sylow base product normalizes that product. -/
theorem le_normalizer_baseSubgroup_of_le [Finite K] {p : ℕ}
    (D : Subgroup K) (P : Sylow p (K × K)) (hP : (P : Subgroup (K × K)) = D.prod D)
    (S : Subgroup (Model α hα)) (hS : IsPGroup p S) (hle : baseSubgroup α hα D ≤ S) :
    S ≤ normalizer (baseSubgroup α hα D : Set (Model α hα)) := by
  let : Finite (Model α hα) :=
    Finite.of_equiv ((K × K) × (Bit × Bit)) SemidirectProduct.equivProd.symm
  have hc : S.comap SemidirectProduct.inl = D.prod D := by
    rw [← hP]
    apply P.is_maximal' (hS.comap_of_injective _ SemidirectProduct.inl_injective)
    intro y hy
    exact hle (mem_map_of_mem SemidirectProduct.inl (hP ▸ hy))
  intro x hx
  apply mem_normalizer_fintype
  intro y hy
  have hyS := hle hy
  have hzS : x * y * x⁻¹ ∈ S := S.mul_mem (S.mul_mem hx hyS) (S.inv_mem hx)
  have hyr : y.right = 1 := ((mem_baseSubgroup α hα D y).mp hy).1
  have hzr : (x * y * x⁻¹).right = 1 := by
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hyr, mul_one, mul_inv_cancel]
  have hz : SemidirectProduct.inl (x * y * x⁻¹).left = x * y * x⁻¹ :=
    SemidirectProduct.ext rfl hzr.symm
  apply (mem_baseSubgroup α hα D _).mpr
  refine ⟨hzr, ?_⟩
  change (x * y * x⁻¹).left ∈ D.prod D
  rw [← hc]
  change SemidirectProduct.inl (x * y * x⁻¹).left ∈ S
  rwa [hz]
end Theory.GroupTheory.PairedInvolutiveExtension
