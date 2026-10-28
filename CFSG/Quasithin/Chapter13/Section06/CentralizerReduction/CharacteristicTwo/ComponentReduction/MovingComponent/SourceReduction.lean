module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.Inputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ResidualAlternatives

/-!
# Specializing the residual argument to the moving component

The two characteristic residual identities in the full initial-sieve output
force normality, leaving the rank-one alternative. Universal source 1.2.2(a)
is specialized to the actual component image in Gᵥ/O₂(Gᵥ). An index-two
normalizer identifies the full orbit with the orbit under the moving Tᵥ.
This constructs the residual equality used to put Lᵥ inside the component pair.

The literal a-image belongs to K* by the central four-group containment.
Its nontriviality follows from the characteristic-two involution centralizer,
and its centralization of Lᵥ* follows from the marked source configuration.
The binary PSL₂ involution-centralizer theorem then excludes that model.
No orbit-residual equality or involution action is assumed locally.

The universal earlier 1.2.2(a) statement remains an explicit input.
The full 13.6.6 assembly must discharge it.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
p.504, Lemma 1.2.2(a), and p.927, proof of 13.6.6.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
open A5Module InitialSieve
universe u

/-- The universal source statement 1.2.2(a), on the actual ambient two-core image. -/
def Earlier122A (κ : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  IsSimpleQTKE κ G → ∀ (H : Subgroup G), H ∈ Chapter1.H G →
    ∀ K : Subgroup H, K.IsCComponent → ∀ p : ℕ, p.Prime → Odd p →
      (Set.range fun g : H => K.map (MulAut.conj g).toMonoidHom).ncard = 2 →
      p ∣ Nat.card (K.map (QuotientGroup.mk' (pCore 2 H))) →
      primeToResidual p H = componentOrbit K ⊤

variable {H : Type*} [Group H]

theorem moving_orbit_eq_full (K U : Subgroup H)
    (hi : (normalizer (K : Set H)).index = 2)
    (hm : ¬ U ≤ normalizer (K : Set H)) :
    componentOrbit K U = componentOrbit K ⊤ := by
  obtain ⟨t, ht, htn⟩ := SetLike.not_le_iff_exists.mp hm
  rw [orbit_eq_pair K U hi ht htn, orbit_eq_pair K ⊤ hi (mem_top t) htn]

variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

omit [Finite G] in
theorem moving_rank_one (K : Subgroup (Gv (markedV s)))
    (a : ActionData s (T : Subgroup G) K) {m : ℕ}
    (hmove : ¬ localT (T : Subgroup G) (markedV s) ≤ X K)
    (hres : ResidualAlternatives s K a m) : primeRank 3 K ≤ 1 := by
  have hn := not_residual_identities K (localT (T : Subgroup G) (markedV s)) hmove
  cases hres with
  | residual _ he => exact (hn.1 he.symm).elim
  | rank_one h => exact h
  | extension _ _ he => exact (hn.2 he.symm).elim

theorem source_psl2_residual (d : Setup κ T s) (earlier : Earlier122A κ G)
    {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (i : ModelComparison.SourceInput s (T : Subgroup G) K m)
    (hpsl : ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 2 (2 ^ m)) :
    primeToResidual 3 (Gv (markedV s)) =
      componentOrbit K (localT (T : Subgroup G) (markedV s)) := by
  have hi := (ModelComparison.moving_index_and_model _ K i.moving i.localModels).1
  rw [moving_orbit_eq_full K _ hi i.moving]
  exact earlier d.ambient _ d.local115.mem_H K i.component.isCComponent
    3 Nat.prime_three (by decide)
    ((ncard_conjugates_eq_index_normalizer K).trans hi)
    (ModelComparison.psl2_three_divides_quotients i.oddCore i.component hpsl).2.2

/-- The actual a-image in K*, with its involution order and centralization of Lᵥ*. -/
theorem exists_marked_involution (d : Setup κ T s)
    {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (i : ModelComparison.SourceInput s (T : Subgroup G) K m) :
    ∃ a : NormalizerAction.componentImage K, orderOf a = 2 ∧
      (a : XStar K) = NormalizerAction.quotient K ⟨aLocal s, i.action.a_normalizes⟩ ∧
      ∀ x : X K, (x : Gv (markedV s)) ∈ residual s →
        Commute (NormalizerAction.quotient K x) (a : XStar K) := by
  let ax : X K := ⟨aLocal s, i.action.a_normalizes⟩
  have hmem : NormalizerAction.quotient K ax ∈
      EStar s K i.action.a_normalizes i.action.z_normalizes :=
    subset_closure (Set.mem_insert _ _)
  let a : NormalizerAction.componentImage K := ⟨NormalizerAction.quotient K ax,
    i.four_in_component hmem⟩
  have hne : a ≠ 1 := by
    intro he
    have hc := (NormalizerAction.quotient_eq_one_iff K ax).mp (congrArg Subtype.val he)
    exact i.component.not_centralizes_of_twoCore_centralizer _ d.centralizer_cores.1 hc
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    change NormalizerAction.quotient K ax ^ 2 = 1
    rw [← map_pow]
    have hax : ax ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change s.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.a) ^ 2 = 1
      rw [← map_pow, show (Multiplicative.ofAdd
        BinaryPermutation.FiveCentralizerGeometry.a) ^ 2 = 1 by decide +kernel, map_one]
    rw [hax, map_one]
  refine ⟨a, orderOf_eq_prime ha2 hne, rfl, ?_⟩
  intro x hx
  apply Commute.map
  apply Subtype.ext
  apply Subtype.ext
  exact (mem_centralizer_iff.mp d.a_centralizes (x : G) hx)

/-- Eliminate the actual binary PSL₂ alternative using universal 1.2.2(a). -/
theorem not_psl2_of_source (d : Setup κ T s) (earlier : Earlier122A κ G)
    {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (i : ModelComparison.SourceInput s (T : Subgroup G) K m)
    (hcard : Nat.card (residual s ⧸ pCore 2 (residual s)) = 3) :
    ¬ ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 2 (2 ^ m) := by
  intro hpsl
  have hres := source_psl2_residual d earlier i hpsl
  have hi := (ModelComparison.moving_index_and_model _ K i.moving i.localModels).1
  have hKD : ⁅K, residual s⁆ ≠ ⊥ := by
    rw [i.action.commutator_residual]
    exact i.component.isCComponent.ne_bot
  obtain ⟨a, ha, _, haC⟩ := exists_marked_involution d i
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact exclude_psl2_of_cubic_residual s (T : Subgroup G) K i.component hi i.moving
    i.action.residual_normalizes hcard hres hKD a ha haC e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
