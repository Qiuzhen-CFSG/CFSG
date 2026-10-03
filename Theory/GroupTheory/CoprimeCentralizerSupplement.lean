module

public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Prime subgroups in a centralizer supplement

If a centralizer supplements a normal subgroup of order coprime to `p`,
every `p`-subgroup containing the centralized subgroup centralizes it.
The supplement makes the quotient images commute, and the quotient map is
injective on the given `p`-subgroup.

This is the elementary implication from Lemma 3.1 to Lemma 3.2 in
Janko–Thompson, Math. Z. 113 (1970), printed p.389.
-/

namespace Subgroup

/-- Centralizer supplementation by a coprime normal subgroup forces
centralization inside every prime overgroup. -/
public theorem le_centralizer_of_isPGroup_of_coprime_supplement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (W O V : Subgroup G) [O.Normal]
    (hO : Nat.Coprime p (Nat.card O))
    (hsupp : centralizer (W : Set G) ⊔ O = ⊤)
    (hV : IsPGroup p V) (hWV : W ≤ V) : V ≤ centralizer (W : Set G) := by
  let q := QuotientGroup.mk' O
  have hinj := injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using hO) V hV
  intro v hv w hw
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp
    (show v ∈ centralizer (W : Set G) ⊔ O by rw [hsupp]; trivial)
  have hbq : q b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
  have hqv : q v = q a := by
    rw [← hab, map_mul, hbq, mul_one]
  have heq : q (w * v) = q (v * w) := by
    simp only [map_mul, hqv]
    exact congrArg q (ha w hw)
  exact congrArg Subtype.val (hinj (a₁ := (⟨w * v, V.mul_mem (hWV hw) hv⟩ : V))
    (a₂ := (⟨v * w, V.mul_mem hv (hWV hw)⟩ : V)) heq)

end Subgroup
