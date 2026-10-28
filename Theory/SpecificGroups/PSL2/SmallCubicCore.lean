module
public import Theory.GroupTheory.FourCubicKernel
public import Theory.GroupTheory.NormalThreeJoinCore
public import Theory.SpecificGroups.PSL2.SmallSylowCentralizer

/-!
# The exact two-core order of a normalized cubic join

In a small-congruence odd PSL2 square, a full Sylow two-subgroup is the
product of two self-centralizing four-groups. If it normalizes a cubic
plane with cyclic coordinate projections, the two-core of their join is
the Sylow centralizer of that plane and has order four. The calculation
transports through the supplied square isomorphism.

Source application: Aschbacher--Smith 10.2.5, printed p.748, in
BinaryThreeAction/OddSmallCoreSize, preserving the original radical map.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace Theory.PSL2
open scoped MatrixGroups
variable {F : Type} [Field F] [Finite F]

/-- The two-core of the normalized cubic join in the literal PSL₂ square has order four. -/
theorem small_pair_cubic_core_card
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F))
    (S : Sylow 2 (PSL(2,F) × PSL(2,F)))
    (P : Subgroup (PSL(2,F) × PSL(2,F))) [IsElementaryAbelian 3 P]
    [IsCyclic (P.map (MonoidHom.fst PSL(2,F) PSL(2,F)))]
    [IsCyclic (P.map (MonoidHom.snd PSL(2,F) PSL(2,F)))]
    (hP : Nat.card P = 9)
    (hn : (S : Subgroup (PSL(2,F) × PSL(2,F))) ≤ normalizer (P : Set _)) :
    Nat.card ((P ⊔ (S : Subgroup (PSL(2,F) × PSL(2,F)))).pCoreIn 2) = 4 := by
  let A := S.mapSurjective (f := MonoidHom.fst _ _) (fun x => ⟨(x,1),rfl⟩)
  let B := S.mapSurjective (f := MonoidHom.snd _ _) (fun x => ⟨(1,x),rfl⟩)
  let := Theory.PSL2.small_sylow_kleinFour hF h8 A
  let := Theory.PSL2.small_sylow_kleinFour hF h8 B
  have hprod : (S : Subgroup (PSL(2,F) × PSL(2,F))) =
      (A : Subgroup PSL(2,F)).prod (B : Subgroup PSL(2,F)) := by
    symm
    apply S.is_maximal'
    · apply IsPGroup.of_card (n := 4)
      rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,
        IsKleinFour.card_four,IsKleinFour.card_four]
      norm_num
    · intro x hx
      exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩
  rw [core_join_three_eq_sylow_centralizer P S (IsElementaryAbelian.isPGroup 3 P) hn,hprod]
  exact four_product_cubic_kernel_card _ _
    (GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF A inferInstance)
    (GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF B inferInstance)
    P hP (hprod ▸ hn)

end Theory.PSL2

namespace Theory.PSL2
open scoped MatrixGroups
variable {F : Type} [Field F] [Finite F]
variable {B : Type*} [Group B] [Finite B]

/-- The same order calculation through the supplied square isomorphism. -/
theorem small_pair_cubic_core_card_of_equiv
    (e : B ≃* PSL(2,F) × PSL(2,F))
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F))
    (S : Sylow 2 B) (P : Subgroup B) [IsElementaryAbelian 3 P]
    [IsCyclic ((P.map e.toMonoidHom).map (MonoidHom.fst PSL(2,F) PSL(2,F)))]
    [IsCyclic ((P.map e.toMonoidHom).map (MonoidHom.snd PSL(2,F) PSL(2,F)))]
    (hP : Nat.card P = 9) (hn : (S : Subgroup B) ≤ normalizer (P : Set B)) :
    Nat.card ((P ⊔ (S : Subgroup B)).pCoreIn 2) = 4 := by
  let : IsElementaryAbelian 3 (P.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hh := small_pair_cubic_core_card hF h8
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (P.map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective]; exact hP)
    ((map_mono hn).trans (le_normalizer_map e.toMonoidHom))
  change Nat.card ((P.map e.toMonoidHom ⊔
    (S : Subgroup B).map e.toMonoidHom).pCoreIn 2) = 4 at hh
  rwa [←Subgroup.map_sup,←map_pCoreIn_of_injective 2 _ e.toMonoidHom e.injective,
    card_map_of_injective e.injective] at hh

end Theory.PSL2
