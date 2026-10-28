module
public import Theory.GroupTheory.SwappedFourNormalizer
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.ElementaryAbelian.Injective

/-!
# Cubic-generated radicals in two self-centralizing four-groups

A nontrivial commutator-generated radical with equal coordinate projection
orders projects onto both four-groups: a projection of order two has trivial
automizer. Its centralizer is therefore contained in the product four-group.
A normalizing cubic plane acts faithfully on the radical. Groups of orders
four and eight have automorphism orders six and 168, so the radical must
have order sixteen and be the entire product.

Source application: Aschbacher--Smith 10.2.5, printed p.748, the radical
calculation in the small-congruence odd PSL₂ case. The zero radical remains
an explicit alternative; equal projection orders come from the exchanger.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SylowNormalizerAction
variable {Q : Type*} [Group Q] [Finite Q]

private theorem projection_full_of_commutator (V : Subgroup Q) [IsKleinFour V]
    (U P : Subgroup Q) (hUV : U ≤ V) (hne : U ≠ ⊥)
    (hn : P ≤ normalizer (U : Set Q)) (hc : ⁅U,P⁆ = U) : U = V := by
  have hd : Nat.card U ∣ 4 := IsKleinFour.card_four (G := V) ▸ card_dvd_of_le hUV
  have hm := Nat.mem_divisors.mpr ⟨hd,by decide⟩
  have hdiv : (4 : ℕ).divisors = {1,2,4} := by decide
  rw [hdiv] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm
  · exact (hne (card_eq_one.mp hm)).elim
  · have hh : P ≤ centralizer (U : Set Q) :=
      hn.trans (normalizer_le_centralizer_of_card_two U hm)
    have hz : ⁅U,P⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hh
    exact (hne (hc.symm.trans hz)).elim
  · exact eq_of_le_of_card_ge hUV (by rw [hm,IsKleinFour.card_four])

/-- An exchanged commutator-generated radical normalized by a cubic plane
in a product of self-centralizing four-groups is either trivial or full. -/
theorem four_product_radical_eq_or_bot
    (V W : Subgroup Q) [IsKleinFour V] [IsKleinFour W]
    (hv : centralizer (V : Set Q) = V) (hw : centralizer (W : Set Q) = W)
    (U P : Subgroup (Q × Q)) (hU : U ≤ V.prod W)
    (hp : IsPGroup 3 P) (hP : Nat.card P = 9)
    (hn : P ≤ normalizer (U : Set (Q × Q))) (hc : ⁅U,P⁆ = U)
    (he : Nat.card (U.map (MonoidHom.fst Q Q)) = Nat.card (U.map (MonoidHom.snd Q Q))) :
    U = ⊥ ∨ U = V.prod W := by
  classical
  by_cases hz : U = ⊥
  · exact Or.inl hz
  right
  let U₁ := U.map (MonoidHom.fst Q Q)
  let U₂ := U.map (MonoidHom.snd Q Q)
  have hu₁ : U₁ ≠ ⊥ := by
    intro hh
    have hh' : U₂ = ⊥ := card_eq_one.mp (by
      change Nat.card U₁ = Nat.card U₂ at he
      rw [hh,card_bot] at he
      exact he.symm)
    apply hz
    apply bot_unique
    intro x hx
    exact Prod.ext (mem_bot.mp (hh ▸ mem_map_of_mem (MonoidHom.fst Q Q) hx))
      (mem_bot.mp (hh' ▸ mem_map_of_mem (MonoidHom.snd Q Q) hx))
  have hu₂ : U₂ ≠ ⊥ := by
    intro hh
    apply hu₁
    apply card_eq_one.mp
    change Nat.card U₁ = Nat.card U₂ at he
    simpa only [hh,card_bot] using he
  have hf : U₁ = V := by
    apply projection_full_of_commutator V U₁ (P.map (MonoidHom.fst Q Q))
    · rintro x ⟨u,hu,rfl⟩; exact (hU hu).1
    · exact hu₁
    · exact (map_mono hn).trans (le_normalizer_map _)
    · rw [←map_commutator,hc]
  have hs : U₂ = W := by
    apply projection_full_of_commutator W U₂ (P.map (MonoidHom.snd Q Q))
    · rintro x ⟨u,hu,rfl⟩; exact (hU hu).2
    · exact hu₂
    · exact (map_mono hn).trans (le_normalizer_map _)
    · rw [←map_commutator,hc]
  have hcent : centralizer (U : Set (Q × Q)) ≤ V.prod W := by
    intro x hx
    constructor
    · rw [←hv,←hf]
      rintro y ⟨u,hu,rfl⟩
      exact congrArg Prod.fst (hx u hu)
    · rw [←hw,←hs]
      rintro y ⟨u,hu,rfl⟩
      exact congrArg Prod.snd (hx u hu)
  have htwo : IsPGroup 2 (V.prod W) := by
    apply IsPGroup.of_card (n := 4)
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,
      IsKleinFour.card_four (G := V),IsKleinFour.card_four (G := W)]
    norm_num
  let f : P →* MulAut U := U.normalizerMonoidHom.comp (inclusion hn)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hh : (⟨x,hn x.property⟩ : normalizer (U : Set (Q × Q))) ∈
        U.normalizerMonoidHom.ker := hx
    rw [normalizerMonoidHom_ker] at hh
    exact Subtype.ext ((hp.disjoint_of_coprime htwo (by decide)).le_bot
      ⟨x.property,hcent hh⟩)
  have hd : 9 ∣ Nat.card (MulAut U) := hP ▸ card_dvd_of_injective f hi
  have hcard : Nat.card U ∣ 16 := by
    have hh := card_dvd_of_le hU
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,
      IsKleinFour.card_four (G := V),IsKleinFour.card_four (G := W)] at hh
    exact hh
  have hlo : 4 ≤ Nat.card U := by
    rw [←IsKleinFour.card_four (G := V),←hf]
    exact Nat.card_le_card_of_surjective ((MonoidHom.fst Q Q).subgroupMap U)
      ((MonoidHom.fst Q Q).subgroupMap_surjective U)
  have hm := Nat.mem_divisors.mpr ⟨hcard,by decide⟩
  have hdiv : (16 : ℕ).divisors = {1,2,4,8,16} := by decide
  rw [hdiv] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  have hcases : Nat.card U = 4 ∨ Nat.card U = 8 ∨ Nat.card U = 16 := by omega
  let : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let : IsElementaryAbelian 2 W :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let : IsElementaryAbelian 2 (V × W) :=
    { exponent_dvd_p := by
        rw [Monoid.exponent_prod,IsKleinFour.exponent_two (G := V),
          IsKleinFour.exponent_two (G := W)]
        decide }
  let : IsElementaryAbelian 2 (V.prod W) :=
    IsElementaryAbelian.of_injective (prodEquiv V W).toMonoidHom (prodEquiv V W).injective
  let : IsElementaryAbelian 2 U :=
    IsElementaryAbelian.of_injective (inclusion hU) (inclusion_injective hU)
  rcases hcases with hh | hh | hh
  · let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let : IsKleinFour U := ⟨hh,IsElementaryAbelian.exponent_eq_prime (p := 2)⟩
    rw [IsKleinFour.card_mulAut] at hd
    norm_num at hd
  · rw [card_mulAut_of_elementary_eight U hh] at hd
    norm_num at hd
  · apply eq_of_le_of_card_ge hU
    rw [hh,Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,
      IsKleinFour.card_four (G := V),IsKleinFour.card_four (G := W)]
end Theory.GroupTheory.SylowNormalizerAction
