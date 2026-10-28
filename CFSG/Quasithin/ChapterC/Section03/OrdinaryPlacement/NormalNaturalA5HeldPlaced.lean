module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldCubicNormalizer
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldCoreNormalizer
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The Held cubic obstruction through the same local embedding

An injective embedding of either native max3/max4 transports the actual
perfect actor and elementary16 back to that same local group. The common
16-subgroup forces the native64 core to normalize the actor. Section
centralizers map through the embedding with the full actor two-core, so
the native cubic contradicts the original fixed-module condition.

This applies to a conjugate local overgroup without changing its embedded
actor or module. It is the final local transport for the Held inspection
in12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement
open Held.LocalPairs.PairCoverage

private theorem sectionCentralizer_image
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) (B : Subgroup X) :
    (ChapterA.Section04.twoSectionCentralizer B ⊤).map f ≤
      ChapterA.Section04.twoSectionCentralizer (B.map f) ⊤ := by
  have hk : IsPGroup 2 f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hf]
    exact IsPGroup.of_bot
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨mem_top _,B.le_normalizer_map f (mem_map_of_mem f hx.2.1),?_⟩
  rintro _ ⟨b,hb,rfl⟩
  rw [←map_commutatorElement,←map_pCoreIn_of_ker_isPGroup f hk B]
  exact mem_map_of_mem f (hx.2.2 b hb)

/-- An original actor and module placed through the same local embedding
cannot satisfy the section-centralizer fixedness condition. -/
theorem held_not_placed_with_fixed_sectionCentralizer
    (i : Bool) (f : localOvergroup i →* Held.He) (hf : Function.Injective f)
    (B E : Subgroup Held.He) [Group.IsPerfect B]
    (hB : B ≤ f.range) (hEB : E ≤ B)
    (hE : E ≤ (pCore 2 (localOvergroup i)).map f)
    (hEc : Nat.card E = 16) (hQc : Nat.card (pCore 2 (localOvergroup i)) = 64)
    (hfixed : ChapterA.Section04.twoSectionCentralizer B ⊤ ≤
      centralizer (E : Set Held.He)) : False := by
  let B₀ := B.comap f
  let E₀ := E.comap f
  have hBm : B₀.map f = B := map_comap_eq_self hB
  have hEm : E₀.map f = E := map_comap_eq_self (hEB.trans hB)
  let b : B₀ ≃* B := (B₀.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hBm)
  let e : E₀ ≃* E := (E₀.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hEm)
  let : Group.IsPerfect B₀ := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  have hE₀c : Nat.card E₀ = 16 := (Nat.card_congr e.toEquiv).trans hEc
  have hE₀ : E₀ ≤ pCore 2 (localOvergroup i) := by
    intro x hx
    exact (mem_map_iff_mem hf).mp (hE hx)
  have hEB₀ : E₀ ≤ B₀ := comap_mono hEB
  let : Group.IsNilpotent (pCore 2 (localOvergroup i)) := pCore_isPGroup.isNilpotent
  have hn : pCore 2 (localOvergroup i) ≤ normalizer (B₀ : Set (localOvergroup i)) :=
    held_core_normalizes_perfect_actor B₀ _ E₀
      (by rw [normalizer_eq_top]; exact le_top) hEB₀ hE₀ hQc hE₀c
  apply HeldCubic.not_fixed_by_sectionCentralizer i B₀ E₀ hn hE₀
  · intro hz
    rw [hz,Subgroup.card_bot] at hE₀c
    omega
  · intro x hx y hy
    apply hf
    have hx' := sectionCentralizer_image f hf B₀ (mem_map_of_mem f hx)
    rw [hBm] at hx'
    have hy' : f y ∈ E := hEm ▸ mem_map_of_mem f hy
    simpa only [map_mul] using hfixed hx' (f y) hy'

end CFSG.Quasithin.ChapterC.OrdinaryPlacement
