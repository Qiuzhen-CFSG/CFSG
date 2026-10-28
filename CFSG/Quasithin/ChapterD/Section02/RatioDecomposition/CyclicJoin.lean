module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.CyclicQuotient
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NormalClosureThree

/-!
# The cyclic normal-closure quotient endpoint

A non-quintic rank-one actor has the seeded three-core factor data from the
literal source action. The classified factors of that datum have cyclic
starred actors, so their odd local kernels map into the intrinsic Fitting
subgroup. The intrinsic Fitting quotient is therefore a two-group, and the
normal factor embeds into the preimage of the ambient two-core.

The theorem keeps the exact original rank-one and Sylow-fixed seed hypotheses;
it does not replace them with a blanket cyclicity assertion. Source:
Aschbacher--Smith D.2.16--17 and D.2.25--29, printed pp.187--192, with
15.1.2 printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
universe u
variable {G V : Type u} [Group G] [Finite G] [Group.IsSolvable G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem source_three_normalClosure_le_twoCore_preimage
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hq : cubicRatio ρ = 2) (hrank : ∀ B ∈ QhatStar ρ, rank B = 1)
    {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f)
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hZ : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hfive : ⁅pCore 5 G,A⁆ = ⊥) :
    normalClosure (A : Set G) ≤
      (pCore 2 (G ⧸ fittingSubgroup G)).comap (QuotientGroup.mk' (fittingSubgroup G)) := by
  let N := normalClosure (A : Set G)
  let P := (pCore 3 N).map N.subtype
  let : N.Normal := inferInstance
  have hcyc : ∀ B ∈ QhatStar ρ, IsCyclic B := by
    intro B hB
    have hb : Nat.card B = 2 := by
      rw [hB.1.2.1.card_eq_two_pow_rank,hrank B hB]
      norm_num
    exact isCyclic_of_prime_card hb
  obtain ⟨d,_,c,hc⟩ := ChapterD.source_three_normalClosure_seed_factors ρ hf hcore hq
    hrank hA hfive S Z hZ hspan
  exact d.cyclic_le_twoCore_preimage c hcore hq.le hc hH f honto hcyc

end CFSG.Quasithin.ChapterD.RatioDecomposition
