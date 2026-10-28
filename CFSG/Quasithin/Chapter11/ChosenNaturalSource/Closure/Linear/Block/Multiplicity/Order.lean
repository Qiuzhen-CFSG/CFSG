module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity.Flag

/-!
# The order comparison and multiplicity two

The vanished central supplement identifies the literal special factor
(U∩L)/C_{U∩L}(L) with U. Its preceding source order q⁵ therefore gives
|U|=q⁵. Counting the kernel of U→G₁/V₁ gives |U/V₁|=q⁴; an actual
natural-sum marking then forces its multiplicity to be exactly two.

The order of the special factor remains the explicit input supplied by
the independent special-structure argument. No chief-factor assertion
about G.2's different two-residual is used.
Source: Aschbacher--Smith, 11.5.7, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

def specialFactorEquiv (hUL : E.W ≤ L)
    (hz : E.W ⊓ centralizer (L : Set G) = ⊥) : SpecialFactor E ≃* E.W := by
  have hC : centralPart E = ⊥ := by
    apply bot_unique
    intro c hc
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hz.le ⟨c.property.1, hc⟩)
  exact ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot).trans
    (MulEquiv.subgroupCongr (inf_eq_left.mpr hUL))

theorem closure_card (f : E.ClosureFlag) (hK : E.K = E.L₁)
    (hseed : E.V₃ = V) {x y : G}
    (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y)
    (hsum : ∃ r : ℕ, Nonempty (ActionEquiv (action E f hK)
      (repeated (linearNatural E.input.field 2) r)))
    (hspecial : Nat.card (SpecialFactor E) = (2 ^ E.input.field.degree) ^ 5) :
    Nat.card E.W = (2 ^ E.input.field.degree) ^ 5 := by
  have hUL := (original_core_and_split E f hK hseed d hUT hf hc hsum).1
  rw [← Nat.card_congr (specialFactorEquiv E hUL
    (closure_fixed_eq_bot E f hK hseed d hsum)).toEquiv]
  exact hspecial

theorem quotient_card (f : E.ClosureFlag) (hK : E.K = E.L₁) {r : ℕ}
    (e : ActionEquiv (action E f hK) (repeated (linearNatural E.input.field 2) r)) :
    Nat.card (Space E f) = (2 ^ E.input.field.degree) ^ (2 * r) := by
  rw [Nat.card_congr e.linearEquiv.toEquiv]
  simp only [Nat.card_fun, Nat.card_fin, E.input.field.card_eq, ← pow_mul, Nat.mul_assoc]

theorem multiplicity_eq_two (f : E.ClosureFlag) (hK : E.K = E.L₁)
    (hseed : E.V₃ = V) {r : ℕ}
    (e : ActionEquiv (action E f hK) (repeated (linearNatural E.input.field 2) r))
    (hcard : Nat.card E.W = (2 ^ E.input.field.degree) ^ 5)
    (hpoint : Nat.card E.V₁ = 2 ^ E.input.field.degree) : r = 2 := by
  let A := E.localClosure E.G₁
  have hA : A ≤ E.G₁ := Geometry.ClosureFlag.closure_le _
    (sup_le E.L₁_le_G₁ f.sylow_normalizes_point)
  have hAW : A = E.W := by
    change conjugateSpanBy E.V₃ E.G₁ = conjugateSpanBy V E.G₁
    rw [hseed]
  have hpA : E.V₁ ≤ A := f.point_le_seed.trans (le_conjugateSpanBy _ _)
  let π := E.tildeProjection A hA
  have hker : Nat.card π.ker = 2 ^ E.input.field.degree := by
    rw [E.tildeProjection_kernel,
      Nat.card_congr (subgroupOfEquivOfLe hpA).toEquiv, hpoint]
  have hi : π.ker.index = Nat.card (Space E f) := by
    rw [index_ker, MonoidHom.range_eq_top_of_surjective _
      (E.tildeProjection_surjective A hA), Nat.card_congr (topEquiv : (⊤ : Subgroup (E.tilde A)) ≃* E.tilde A).toEquiv]
    rfl
  have hcount := π.ker.card_mul_index
  rw [hker, hi, quotient_card E f hK e, hAW, hcard] at hcount
  have he : 1 + 2 * r = 5 := by
    apply Nat.pow_right_injective (show 1 < 2 ^ E.input.field.degree from
      (by norm_num : 1 < 2 ^ 1).trans_le
        (Nat.pow_le_pow_right (by decide) E.input.field.degree_pos))
    simpa only [pow_add, pow_one] using hcount
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
