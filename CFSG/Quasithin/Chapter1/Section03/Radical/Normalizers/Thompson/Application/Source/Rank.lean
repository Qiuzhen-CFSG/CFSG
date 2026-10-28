module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Quasithin.Rank

/-!
# The rank bound for the solvable Thompson factors

The alternating cubic subgroup in each symmetric-three factor gives an
embedded elementary group of order 3^r in the literal centralizer quotient.
If its kernel is a two-group, coprime quotient lifting bounds r by the
three-rank of the original group. This is the rank calculation used in
15.4.12; no rank bound on arbitrary sections is assumed.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
variable {H : Type*} [Group H] [Finite H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (closure S)]

/-- The actual direct product contains one independent cubic per factor. -/
theorem Exceptional.count_le_quotient_threeRank (d : Exceptional S) :
    d.count ≤ primeRank 3 (CentralQuotient (closure S)) := by
  classical
  let A := alternatingGroup (Fin 3)
  have hA : Nat.card A = 3 := by
    change Nat.card (alternatingGroup (Fin 3)) = 3
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  let : IsCyclic A := isCyclic_of_prime_card hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let models (i : Fin d.count) : d.factor i ≃* Equiv.Perm (Fin 3) :=
    (d.factorModel i).trans (Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two.symm.trans e)
  let f : (Fin d.count → A) →* ((i : Fin d.count) → d.factor i) :=
    { toFun := fun a i => (models i).symm (a i)
      map_one' := by funext i; exact (models i).symm.map_one
      map_mul' := fun a b => by funext i; exact (models i).symm.map_mul (a i) (b i) }
  have hf : Function.Injective f := by
    intro a b hab
    funext i
    apply Subtype.ext
    exact (models i).symm.injective (congrFun hab i)
  let g := (((elementaryAbelianMaxJ (⊤ : Subgroup H)).map
    (starMap (closure S))).subtype.comp d.groupProduct.toMonoidHom).comp f
  have hg : Function.Injective g :=
    Subtype.val_injective.comp (d.groupProduct.injective.comp hf)
  apply primeRank_ge_of_elementary_embedding (f := g) (hf := hg)
  · intro a
    funext i
    change a i ^ 3 = 1
    have hp := pow_card_eq_one' (x := a i)
    rwa [hA] at hp
  · rw [Nat.card_pi]
    simp only [hA, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A two-group action kernel permits lifting this odd-prime rank to H. -/
theorem Exceptional.count_le_threeRank (d : Exceptional S)
    (hker : IsPGroup 2 (centralizer (closure S : Set H))) :
    d.count ≤ primeRank 3 H :=
  d.count_le_quotient_threeRank.trans
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ hker)

/-- A noncentral source application in three-rank at most two has one or two factors. -/
theorem Exceptional.count_eq_one_or_two (d : Exceptional S)
    (hker : IsPGroup 2 (centralizer (closure S : Set H)))
    (hrank : primeRank 3 H ≤ 2) : d.count = 1 ∨ d.count = 2 := by
  obtain ⟨i⟩ := d.nonempty_factors
  have hbound := (d.count_le_threeRank hker).trans hrank
  have := i.isLt
  omega

end CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
