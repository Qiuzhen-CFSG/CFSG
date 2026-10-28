module

public import Theory.GroupTheory.SemidihedralCenter
public import Theory.ElementaryAbelian.Basic

/-!
# Normal elementary subgroups of a semidihedral group of order sixteen

For generators a,b of orders eight and two with b a b⁻¹ = a³, the only
nontrivial normal elementary abelian two-subgroup is ⟨a⁴⟩. An element aⁱb
in a normal subgroup forces a⁻² into that subgroup by conjugation with a;
this contradicts exponent two. The remaining powers of a are 1 and a⁴.

This presentation calculation supplies the Sylow-local reduction for M11
in Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4. It uses the explicit
semidihedral normal forms and makes no assumption on other normal subgroups.
-/

open Subgroup
namespace Semidihedral
variable {G : Type*} [Group G]

/-- The unique nontrivial normal elementary subgroup of an explicit SD16 presentation. -/
public theorem normal_elementary_eq_of_order_sixteen (a b : G)
    (ha : orderOf a = 8) (hb : orderOf b = 2)
    (hc : b * a * b⁻¹ = a ^ 3)
    (hg : closure ({a, b} : Set G) = ⊤)
    (R : Subgroup G) (hR : R ≠ ⊥) [R.Normal] [IsElementaryAbelian 2 R] :
    R = zpowers (a ^ 4) := by
  have hs : ∀ x ∈ R, x ^ 2 = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian x hx
  have helem : ∀ x ∈ R, x = 1 ∨ x = a ^ 4 := by
    intro x hx
    obtain ⟨i, hi, hxi | hxi⟩ := normal_form a b 8 3 (by decide) ha
      (by rw [← hb]; exact pow_orderOf_eq_one b) hc hg x
    · have hpow := hs x hx
      rw [hxi, ← pow_mul] at hpow
      have hd := orderOf_dvd_of_pow_eq_one hpow
      rw [ha] at hd
      have hi' : i = 0 ∨ i = 4 := by omega
      rcases hi' with rfl | rfl
      · exact Or.inl (by simpa using hxi)
      · exact Or.inr hxi
    · have hxa : x * a * x⁻¹ = a ^ 3 := by
        rw [hxi]
        calc
          (a ^ i * b) * a * (a ^ i * b)⁻¹ =
              a ^ i * (b * a * b⁻¹) * (a ^ i)⁻¹ := by group
          _ = a ^ 3 := by rw [hc]; group
      have hymem : a * x * a⁻¹ * x⁻¹ ∈ R :=
        R.mul_mem (Subgroup.Normal.conj_mem inferInstance x hx a) (R.inv_mem hx)
      have hy : a * x * a⁻¹ * x⁻¹ = (a ^ 2)⁻¹ := by
        calc
          a * x * a⁻¹ * x⁻¹ = a * (x * a * x⁻¹)⁻¹ := by group
          _ = (a ^ 2)⁻¹ := by rw [hxa]; group
      have hpow := hs _ hymem
      rw [hy, inv_pow, inv_eq_one, ← pow_mul] at hpow
      have hd := orderOf_dvd_of_pow_eq_one hpow
      rw [ha] at hd
      norm_num at hd
  apply le_antisymm
  · intro x hx
    rcases helem x hx with rfl | rfl
    · exact (zpowers (a ^ 4)).one_mem
    · exact mem_zpowers _
  · obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
    apply zpowers_le.mpr
    rcases helem x x.property with h | h
    · exact False.elim (hx1 (Subtype.ext h))
    · exact h ▸ x.property
end Semidihedral
