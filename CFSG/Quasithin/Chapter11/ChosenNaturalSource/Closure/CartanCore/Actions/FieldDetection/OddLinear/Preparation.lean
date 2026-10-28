module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Components
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Parameters
public import Theory.GroupTheory.Hall.OddNormalProducts

/-!
# The actual odd Cartan input to the component sieve

The source Cartan normalizer is N_L(T intersect L), hence is normalized
by T. A Hall odd subgroup complements its Sylow two-subgroup, giving
XT=TX in the original ambient group. Combining this with the full split
Cartan marking supplies abelianity, coprimality, exclusion of three,
the component rank bound, normalization and a nonidentity quotient actor.

This prepares the hypotheses for the source sieve; it does not classify
any component. The full split marking and earlier numerical conclusions
remain explicit inputs from the original flag/Cartan and relative-component
producers. Source: Aschbacher--Smith A.3.15, pp.50--51, and 11.5.6(3), p.781.
-/

public section
open Subgroup
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Hall factorization in the literal Cartan normalizer proves XT=TX. -/
theorem cartan_sylow_permute (hc : LocalGeometry.IsCartan T L E.X) :
    (E.X : Set G) * (T : Set G) = (T : Set G) * (E.X : Set G) := by
  let N := LocalGeometry.cartanNormalizer T L
  have hn : (T : Subgroup G) ≤ normalizer (N : Set G) := by
    dsimp only [N]
    rw [LocalGeometry.cartanNormalizer_eq_intersection_normalizer]
    exact (le_inf D.sylow_normalizes_component
      (((le_inf (T : Subgroup G).le_normalizer D.sylow_normalizes_component).trans
        inf_normalizer_le_normalizer_inf).trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T N hn
  have hcomp := OddHall.sylow_complement_of_hall P hc.2
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, t, ht, rfl⟩
    have hconj : t⁻¹ * x * t ∈ N := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp (hn (T.inv_mem ht)) x).mp (hc.1 hx)
    obtain ⟨⟨p, y⟩, hp⟩ := hcomp.2 ⟨t⁻¹ * x * t, hconj⟩
    have hpT : (p.val : G) ∈ T := by
      exact hP.le p.property
    have he := congrArg Subtype.val hp
    refine ⟨t * p.val, T.mul_mem ht hpT, y.val, y.property, ?_⟩
    calc
      (t * (p.val : G)) * y.val = t * (p.val * y.val : N) := by simp only [Subgroup.coe_mul, mul_assoc]
      _ = t * (t⁻¹ * x * t) := congrArg (t * ·) he
      _ = x * t := by group
  · rintro _ ⟨t, ht, x, hx, rfl⟩
    have hconj : t * x * t⁻¹ ∈ N := (mem_normalizer_iff.mp (hn ht) x).mp (hc.1 hx)
    obtain ⟨⟨y, p⟩, hp⟩ := hcomp.symm.2 ⟨t * x * t⁻¹, hconj⟩
    have hpT : (p.val : G) ∈ T := by
      exact hP.le p.property
    have he := congrArg Subtype.val hp
    refine ⟨y.val, y.property, p.val * t, T.mul_mem hpT ht, ?_⟩
    calc
      (y.val : G) * (p.val * t) = (y.val * p.val : N) * t := by simp only [Subgroup.coe_mul, mul_assoc]
      _ = (t * x * t⁻¹) * t := congrArg (· * t) he
      _ = t * x := by group

/-- The actual source action satisfies the elementary inputs of the odd sieve. -/
theorem odd_component_action_preparation
    (hp : E.point ≠ ⊥) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (e : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (hr : primeRank 3 E.Y ≤ 1) (hn : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hm : ¬ ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2) :
    (E.X : Set G) * (T : Set G) = (T : Set G) * (E.X : Set G) ∧
      IsMulCommutative E.X ∧ Nat.Coprime (Nat.card E.X) (Nat.card I) ∧
      ¬ 3 ∣ Nat.card E.X ∧ primeRank 3 I ≤ 1 ∧
      E.X ≤ normalizer (I : Set G) ∧
      ∃ x : normalizer (I : Set G), (x : G) ∈ E.X ∧ coreQuotientAction I x ≠ 1 := by
  refine ⟨cartan_sylow_permute E hcart, ?_,
    E.cartan_coprime_component_of_split_marking e hc hI,
    E.three_not_dvd_cartan_of_split_marking e hn, ?_,
    E.cartan_normalizes_component hp hX hcart.odd hI,
    E.exists_component_quotient_mover hp hX hcart.odd hI hm⟩
  · exact ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  · exact (Theory.GroupTheory.primeRank_le_of_injective 3
      (inclusion hI.1) (inclusion_injective hI.1)).trans hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
