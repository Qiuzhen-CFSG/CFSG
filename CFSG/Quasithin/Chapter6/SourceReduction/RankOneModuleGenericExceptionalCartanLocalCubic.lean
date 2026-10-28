module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.CubicLinearExclusion

/-!
# Odd linear containing-row exclusions from the original cubic escape

The escaping cubic excludes the paired seed, making the whole residual
a local C-component and producing a proper normal containing component.
The actual quotient-action arguments then exclude every odd-prime PSL₂
quotient and PSL₂(25). Both Hall conditions and the original module
input are retained, and no A₅ quotient is assumed.

When the original field degree is two, its left Cartan has order three.
The original intersection escape forces that whole Cartan into Y, so
it supplies the cubic for the same exclusions. This specialized route
does not assert that the general source hypotheses imply degree two.

Source: Aschbacher–Smith 5.1.13, printed pp.636–638.
The remaining sieve and source assembly belong to the original local
Cartan classification family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- An original escaping cubic gives a proper normal container outside the odd linear rows. -/
theorem localCartan_cubic_escape_container_exclusions
    {T : Sylow 2 G} {L W H A B Y D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hDA : D ≤ A) (hDY : D ≤ Y) (hDc : Nat.card D = 3)
    (hD : ¬ D ≤ normalizer (residual H : Set G)) :
    residual H ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
        (X.subgroupOf Y).Normal ∧ residual H < X ∧
        (∀ p : ℕ, p.Prime → Odd p → ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 25 := by
  have hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G) :=
    fun hn => hD ((le_inf hDA hDY).trans hn)
  obtain ⟨_,_,hKL,X,hXY,hX,hXn,hKX⟩ := localCartan_cubic_escape_residual_component
    h hH hgen c hY hescape hDA hDc hD
  exact ⟨hKL,X,hXY,hX,hXn,hKX,
    fun _ hp ho => LocalSieve.cubic_escape_not_prime_container h hH hgen c hY hescape
      hXY hX hXn hKX.le hDA hDY hDc hD hp ho,
    LocalSieve.cubic_escape_not_twentyFive_container h hH hgen c hY hescape
      hXY hX hXn hKX.le hDA hDY hDc hD⟩

/-- At degree two the original intersection escape supplies the required cubic. -/
theorem localCartan_degree_two_escape_container_exclusions
    {T : Sylow 2 G} {L W H A B Y : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    A ≤ Y ∧ residual H ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
        (X.subgroupOf Y).Normal ∧ residual H < X ∧
        (∀ p : ℕ, p.Prime → Odd p → ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 25 := by
  have hAc : Nat.card A = 3 := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  let : Fact (Nat.card A).Prime := ⟨hAc ▸ (by decide : Nat.Prime 3)⟩
  have hAY : A ≤ Y := by
    rcases (Y.subgroupOf A).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply False.elim
      apply hescape
      intro x hx
      have hx' : (⟨x,hx.1⟩ : A) ∈ Y.subgroupOf A := hx.2
      rw [hb] at hx'
      have he : x = 1 := congrArg Subtype.val (mem_bot.mp hx')
      simpa only [he] using (normalizer (residual H : Set G)).one_mem
    · exact subgroupOf_eq_top.mp ht
  exact ⟨hAY, localCartan_cubic_escape_container_exclusions h hH hgen c hY
    le_rfl hAY hAc (fun hn => hescape (inf_le_left.trans hn))⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
