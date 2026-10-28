module

public import Theory.PGroupCore

/-!
# Trivial prime core in an extension

A normal subgroup and its quotient detect the ambient prime core. If both
have trivial p-core, then the whole group does too.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] (p : ℕ)

/-- Trivial p-core passes through an extension with trivial p-core kernel. -/
theorem pCore_eq_bot_of_normal_and_quotient (N : Subgroup G) [N.Normal]
    (hN : pCore p N = ⊥) (hQ : pCore p (G ⧸ N) = ⊥) :
    pCore p G = ⊥ := by
  let q := QuotientGroup.mk' N
  have hmap : (pCore p G).map q ≤ pCore p (G ⧸ N) :=
    le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective N),
      pCore_isPGroup.map q⟩
  have hle : pCore p G ≤ N := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    exact mem_bot.mp (hQ ▸ hmap (mem_map_of_mem q hx))
  have hcore : (pCore p G).subgroupOf N ≤ pCore p N :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  apply bot_unique
  intro x hx
  have he : (⟨x,hle hx⟩ : N) = 1 := mem_bot.mp (hN ▸ hcore hx)
  exact congrArg Subtype.val he

end Subgroup
