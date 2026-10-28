module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import CFSG.Quasithin.Chapter13.Section02.A5Local.FixedPoints
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.NoNaturalSubmodule

/-!
# Excluding symplectic local factors from an original A₅ context

The original chosen module is a nontrivial normal subgroup of the whole
component two-core and meets the component center trivially. In either
native symplectic local factor, every noncentral normal subgroup of the
radical is the whole radical, which contains a nontrivial local center.
Transporting the original module therefore excludes both local factors.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

private theorem not_core_normal_fixed
    (d : Context T L V V₁ V₂ V₃)
    {H : Type*} [Group H] (e : L ≃* H)
    (hkill : ∀ N : Subgroup H, N.Normal → N ≤ pCore 2 H →
      Disjoint N (center H) → N = ⊥) : False := by
  let U := V.subgroupOf L
  let N := U.map e.toMonoidHom
  let : U.Normal := normal_subgroupOf_of_le_normalizer d.chosen.normalizes
  have hN : N.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
  have hU : U ≤ pCore 2 L := by
    intro x hx
    exact (mem_map_iff_mem L.subtype_injective).mp (d.chosen.le_componentCore hx)
  have hcore : N ≤ pCore 2 H := by
    rw [←pCore_map_iso 2 e]
    exact map_mono hU
  have hd : Disjoint N (center H) := by
    rw [disjoint_iff_inf_le]
    rintro _ ⟨⟨v,hv,rfl⟩,hc⟩
    have hvc : v ∈ center L := by
      have hh := (centerCongr e.symm ⟨e v,hc⟩).property
      change e.symm (e v) ∈ center L at hh
      simpa only [MulEquiv.symm_apply_apply] using hh
    have hv1 : v.val = 1 := by
      apply mem_bot.mp
      apply d.flag.module.fixed_eq_bot.le
      refine ⟨hv,?_⟩
      intro l hl
      exact congrArg L.subtype (mem_center_iff.mp hvc ⟨l,hl⟩)
    have hv1' : v = 1 := Subtype.ext hv1
    simp only [mem_bot, hv1', map_one]
  have hzero : U = ⊥ := (U.map_eq_bot_iff_of_injective e.injective).mp
    (hkill N hN hcore hd)
  apply d.chosen.ne_bot
  have hh := congrArg (map L.subtype) hzero
  simpa only [U,map_subgroupOf_eq_of_le d.chosen.le_component,Subgroup.map_bot] using hh

/-- The original moved module excludes the native symplectic plane factor. -/
theorem original_context_not_symplectic_plane_local_equiv
    (d : Context T L V V₁ V₂ V₃)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n)
    (e : L ≃* planeLocal (F := F)) : False := by
  apply not_core_normal_fixed d e
  intro N hN hcore hd
  let : N.Normal := hN
  rw [planeLocal_core_eq hF hn] at hcore
  exact Plane.normal_radical_eq_bot_of_disjoint_center hF hn N hcore hd

/-- The original moved module excludes the native symplectic point factor. -/
theorem original_context_not_symplectic_point_local_equiv
    (d : Context T L V V₁ V₂ V₃)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n)
    (e : L ≃* pointLocal (F := F)) : False := by
  apply not_core_normal_fixed d e
  intro N hN hcore hd
  let : N.Normal := hN
  rw [pointLocal_core_eq hF hn] at hcore
  rcases PointRadicalAction.normal_radical_dichotomy hF hn N hcore with hc | he
  · exact bot_unique ((le_inf le_rfl hc).trans hd.le_bot)
  · have hcenter : center (pointLocal (F := F)) = ⊥ :=
      bot_unique ((le_inf (he ▸ PointRadicalAction.center_le_radical hF hn) le_rfl).trans hd.le_bot)
    have hne := (PointRadicalAction.chief_series hF hn).1.ne'
    rw [hcenter,Subgroup.map_bot] at hne
    exact (hne rfl).elim

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
