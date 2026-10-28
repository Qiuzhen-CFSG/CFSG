module
public import Theory.GroupAction.CosetTransport
public import Mathlib.Tactic.Group

/-!
# Two-transitive coset actions and double cosets

A two-transitive left-coset action has exactly two double cosets. Thus any
two elements outside the marked subgroup differ by left and right factors
in that subgroup. The second theorem pulls this factorization through a
specified homomorphism whose kernel lies in the marked subgroup.

This supplies the orbit-span argument for the actual plane join in
Aschbacher--Smith 12.9.7, refs/quasithin.pdf, printed p.862.
-/

public section
namespace Subgroup
variable {G K : Type*} [Group G] [Group K]

/-- Every element outside the stabilizer lies in the same double coset. -/
theorem two_pretransitive_factorization (H : Subgroup G)
    (ht : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2)
    {a b : G} (ha : a ∉ H) (hb : b ∉ H) :
    ∃ x ∈ H, ∃ y ∈ H, x * a * y = b := by
  have hqa : (QuotientGroup.mk 1 : G ⧸ H) ≠ QuotientGroup.mk a := by
    intro he
    exact ha (by simpa using QuotientGroup.eq.mp he)
  have hqb : (QuotientGroup.mk 1 : G ⧸ H) ≠ QuotientGroup.mk b := by
    intro he
    exact hb (by simpa using QuotientGroup.eq.mp he)
  obtain ⟨x,hx,hxa⟩ := MulAction.is_two_pretransitive_iff.mp ht hqa hqb
  have hxH : x ∈ H := by
    have hh := QuotientGroup.eq.mp hx
    simpa using H.inv_mem hh
  have hyH : (x * a)⁻¹ * b ∈ H := QuotientGroup.eq.mp hxa
  exact ⟨x,hxH,(x*a)⁻¹*b,hyH,by group⟩

/-- Lift the double-coset factorization through its actual kernel. -/
theorem two_pretransitive_factorization_of_map (f : G →* K) (H : Subgroup G)
    (hk : f.ker ≤ H)
    (ht : MulAction.IsMultiplyPretransitive K (K ⧸ H.map f) 2)
    {a b : G} (ha : a ∉ H) (hb : b ∉ H) :
    ∃ x ∈ H, ∃ y ∈ H, x * a * y = b := by
  have hm (z : G) : f z ∈ H.map f ↔ z ∈ H := by
    change z ∈ (H.map f).comap f ↔ _
    rw [comap_map_eq_self hk]
  obtain ⟨x,hx,y,hy,he⟩ := two_pretransitive_factorization (H.map f) ht
    (fun he => ha ((hm a).mp he)) (fun he => hb ((hm b).mp he))
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  have hz : (x*a*y)⁻¹*b ∈ f.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,map_mul,map_mul,he,inv_mul_cancel]
  exact ⟨x,hx,y*((x*a*y)⁻¹*b),H.mul_mem hy (hk hz),by group⟩
end Subgroup
