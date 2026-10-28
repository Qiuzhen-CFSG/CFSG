module

public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.CoveringKernelCard
public import Theory.PGroupCore

/-!
# Descent of covers through a p-group kernel

A universal covering maps onto every covering of the same finite quasisimple
base. A p-group kernel has p-group image in a target with trivial p-core,
and that image vanishes. The universal lift therefore descends through any
intermediate covering whose comparison kernel is a p-group. This retains
both the actual intermediate group and the commuting projection triangle.

This is the elementary descent step used with the canonical and exceptional
parts of the Schur multiplier in GLS3, Section 6.1, especially Theorem 6.1.4
and Corollary 6.1.5. It does not assert any model's multiplier calculation.
-/

public section

open Subgroup
namespace Theory.GroupTheory.Covering
universe u v w z
variable {S : Type u} {U : Type v} {L : Type w} {H : Type z}
  [Group S] [Finite S] [IsQuasisimple S]
  [Group U] [Finite U] [IsQuasisimple U]
  [Group L] [Finite L] [IsQuasisimple L]
  [Group H] [Finite H] [IsQuasisimple H]

/-- A universal p-group kernel forces every cover with trivial p-core to be
injective. The target kernel order divides the universal kernel order. -/
theorem IsUniversal.injective_of_pGroup_kernel {p : ℕ} [Fact p.Prime]
    {c : Covering U S} (hc : IsUniversal.{u,v,w} c)
    (hp : IsPGroup p c.toMonoidHom.ker) (g : Covering L S)
    (hcore : pCore p L = ⊥) : Function.Injective g.toMonoidHom := by
  let b := hc.lift g
  have hfac : g.toMonoidHom.comp b.toMonoidHom = c.toMonoidHom :=
    congrArg Covering.toMonoidHom (hc.lift_fac g)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hg : IsPGroup p g.toMonoidHom.ker := IsPGroup.of_card_dvd_pow
    (hn ▸ kernel_card_dvd_of_surjective_factor _ _ _ b.surjective hfac)
  apply g.toMonoidHom.ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  rw [← hcore]
  exact le_sSup ⟨inferInstance, hg⟩

/-- Descend the universal lift through a concrete intermediate cover whose
comparison kernel is a p-group. Its image in the target lies in the target
p-core, so vanishes; the descended map is still surjective and commutes
with the original projections. -/
theorem IsUniversal.exists_covering_of_pGroup_kernel {p : ℕ} [Fact p.Prime]
    {c : Covering U S} (hc : IsUniversal.{u,v,w} c)
    (a : Covering U H) (f : Covering H S) (hfac : f.comp a = c)
    (hp : IsPGroup p a.toMonoidHom.ker) (g : Covering L S)
    (hcore : pCore p L = ⊥) :
    ∃ k : Covering H L, g.comp k = f := by
  let b := hc.lift g
  have hb : g.toMonoidHom.comp b.toMonoidHom = c.toMonoidHom :=
    congrArg Covering.toMonoidHom (hc.lift_fac g)
  have hmap : a.toMonoidHom.ker.map b.toMonoidHom ≤ pCore p L :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ b.surjective, hp.map _⟩
  have hkill : a.toMonoidHom.ker ≤ b.toMonoidHom.ker := by
    rw [hcore] at hmap
    intro x hx
    exact Subgroup.mem_bot.mp (hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  let k : H →* L := a.toMonoidHom.liftOfSurjective a.surjective ⟨b.toMonoidHom, hkill⟩
  have hk : k.comp a.toMonoidHom = b.toMonoidHom :=
    MonoidHom.liftOfRightInverse_comp _ _ _ _
  have hks : Function.Surjective k := by
    intro y
    obtain ⟨x, rfl⟩ := b.surjective y
    exact ⟨a x, DFunLike.congr_fun hk x⟩
  have hh : g.toMonoidHom.comp k = f.toMonoidHom := by
    apply (MonoidHom.cancel_right a.surjective).mp
    rw [MonoidHom.comp_assoc, hk, hb]
    exact (congrArg Covering.toMonoidHom hfac).symm
  refine ⟨⟨k, hks⟩, ?_⟩
  ext x
  exact DFunLike.congr_fun hh x
end Theory.GroupTheory.Covering
