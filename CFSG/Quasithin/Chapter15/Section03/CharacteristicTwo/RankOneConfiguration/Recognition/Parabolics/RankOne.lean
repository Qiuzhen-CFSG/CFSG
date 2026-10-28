module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Local
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.FiniteParabolicTransfer

/-!
# Rank-one consequences of the preliminary alternatives

The first alternative of 15.3.11(5) has a three-group quotient of exponent
three and order nine or twenty-seven. Odd prime rank one makes its Sylow
three-subgroup cyclic, which rules out that alternative. This proves all
four conclusions of 15.3.26(1) from the displayed earlier disjunction.

The prime-to-three residual identity puts every three-subgroup of `M ∩ I`
in `Y₊`. Its image in `(Y₊S)/O₂(Y₊S) ≃ S₃` is injective, so its order is
at most three. These are the rank and order bounds used in 15.3.27–28.
No rank-two elimination or component normality is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(5), p.1123, and 15.3.26(1), p.1130 (PDF pp.1140 and 1147).
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics

variable {G : Type*} [Group G]

/-- The four conclusions of 15.3.26(1), with the actual quotient,
prime-to-three residual, and relative centralizer. This is an output interface;
`lemma_15_3_26_1_of_15_3_11_5` constructs it from the earlier alternative. -/
structure RankOneFacts (d : LocalData G) (I : Subgroup G) : Prop where
  choice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M ∧
    d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G))
  shadow : Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸
    pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃* Equiv.Perm (Fin 3))
  residual : d.Yplus = (primeToResidual 3 (d.MI I)).map (d.MI I).subtype
  centralizer : d.R = d.S ⊓ centralizer (d.V₂ : Set G)

private theorem three_quotient_card_le_three [Finite G]
    (N : Subgroup G) [N.Normal]
    (hr : primeRank 3 G ≤ 1)
    (hq : IsPGroup 3 (G ⧸ N)) (he : Monoid.exponent (G ⧸ N) ∣ 3) :
    Nat.card (G ⧸ N) ≤ 3 := by
  let P : Sylow 3 G := Sylow.nonempty.some
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have hQ : (Q : Subgroup (G ⧸ N)) = ⊤ :=
    top_unique ((hq.to_subgroup ⊤).le_sylow_of_normal Q)
  let : IsCyclic Q := isCyclic_of_surjective
    ((QuotientGroup.mk' N).subgroupMap (P : Subgroup G))
    ((QuotientGroup.mk' N).subgroupMap_surjective (P : Subgroup G))
  have hc : IsCyclic (G ⧸ N) := by
    have ht : IsCyclic (⊤ : Subgroup (G ⧸ N)) := hQ ▸ inferInstanceAs (IsCyclic Q)
    exact (topEquiv : (⊤ : Subgroup (G ⧸ N)) ≃* (G ⧸ N)).isCyclic.mp ht
  let := hc
  rw [IsCyclic.exponent_eq_card] at he
  exact Nat.le_of_dvd (by decide) he

/-- Select 15.3.11(5ii) using rank one. Only the displayed numerical
consequences of (5i) are needed: its quotient is a three-group of exponent
three and order greater than three. The preliminary assembly must supply
this disjunction from the genuine earlier conclusions. -/
theorem lemma_15_3_26_1_of_15_3_11_5 [Finite G]
    (d : LocalData G) (I : Subgroup G) (hr : primeRank 3 d.Yplus = 1)
    (h11_5 :
      (IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) ∧
        Monoid.exponent (d.Yplus ⧸ pCore 2 d.Yplus) ∣ 3 ∧
        3 < Nat.card (d.Yplus ⧸ pCore 2 d.Yplus)) ∨ RankOneFacts d I) :
    RankOneFacts d I := by
  rcases h11_5 with ⟨hp, he, hc⟩ | h
  · exact (not_lt_of_ge (three_quotient_card_le_three _ hr.le hp he) hc).elim
  · exact h

private theorem injective_of_three_source_two_kernel
    {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hA : IsPGroup 3 A) (hk : IsPGroup 2 f.ker) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) f.ker (⊤ : Subgroup A)
    hk (hA.to_subgroup ⊤)
  simpa only [disjoint_top] using hd

private theorem three_card_le_three_of_le_six {A : Type*} [Group A] [Finite A]
    (hp : IsPGroup 3 A) (hc : Nat.card A ≤ 6) : Nat.card A ≤ 3 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  by_cases h : n ≤ 1
  · rw [hn]
    exact (Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) h).trans (by decide)
  · have hlarge : 9 ≤ 3 ^ n := by
      exact Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (by omega : 2 ≤ n)
    omega

/-- Every three-subgroup of the intersection has order at most three.
The proof uses the residual identity and the actual `S₃` quotient. -/
theorem three_subgroup_card_le_three [Finite G]
    (d : LocalData G) {I X : Subgroup G} (h : RankOneFacts d I)
    (hXM : X ≤ d.MI I) (hp : IsPGroup 3 X) : Nat.card X ≤ 3 := by
  have hXY : X ≤ d.Yplus := by
    rw [h.residual]
    have hsub : X.subgroupOf (d.MI I) ≤ primeToResidual 3 (d.MI I) :=
      le_primeToResidual_of_isPGroup (hp.of_equiv (subgroupOfEquivOfLe hXM).symm)
    have hm := map_mono (f := (d.MI I).subtype) hsub
    rwa [map_subgroupOf_eq_of_le hXM] at hm
  let j := inclusion (hXY.trans (le_sup_left : d.Yplus ≤ d.Yplus ⊔ d.S))
  let f := (QuotientGroup.mk' (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))).comp j
  have hk : IsPGroup 2 f.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective j (inclusion_injective _)
  have hf := injective_of_three_source_two_kernel f hp hk
  obtain ⟨e⟩ := h.shadow
  apply three_card_le_three_of_le_six hp
  have hc := Nat.card_le_card_of_injective (e.toMonoidHom.comp f)
    (e.injective.comp hf)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, show Nat.factorial 3 = 6 from rfl] using hc

/-- The Sylow-three bound needed for the normal-centre obstruction. -/
theorem intersection_sylow_three_card_le_three [Finite G]
    (d : LocalData G) {I : Subgroup G} (h : RankOneFacts d I)
    (P : Sylow 3 (d.MI I)) : Nat.card P ≤ 3 := by
  have hb := three_subgroup_card_le_three d h (map_subtype_le (P : Subgroup (d.MI I)))
    (P.isPGroup'.map (d.MI I).subtype)
  rwa [card_map_of_injective (d.MI I).subtype_injective] at hb

/-- The rank bound used for the Borel and partition-stabilizer exclusions. -/
theorem intersection_three_rank_le_one [Finite G]
    (d : LocalData G) {I : Subgroup G} (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1) : primeRank 3 (d.MI I) ≤ 1 := by
  let P : Sylow 3 (d.MI I) := Sylow.nonempty.some
  have hPY : (P : Subgroup (d.MI I)).map (d.MI I).subtype ≤ d.Yplus := by
    rw [h.residual]
    exact map_mono (le_primeToResidual_of_isPGroup P.isPGroup')
  have hrP : primeRank 3 P ≤ 1 := by
    apply le_trans ?_ hr.le
    let f : P →* d.Yplus :=
      ((d.MI I).subtype.comp (P : Subgroup (d.MI I)).subtype).codRestrict d.Yplus
        (fun x => hPY (mem_map_of_mem _ x.property))
    exact Theory.GroupTheory.primeRank_le_of_injective 3 f
      (by
        intro x y he
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : d.Yplus => (z : G)) he)
  exact P.primeRank_le_one_of_isCyclic
    ((P.isPGroup').isCyclic_of_odd_of_elementary_card_le (by decide)
      (fun E hE => @IsElementaryAbelian.card_le_prime_of_primeRank_le_one
        P _ _ 3 _ hrP E hE))

/-- The intersection has exactly the same three-rank as `Y₊` in this branch. -/
theorem intersection_three_rank_eq_one [Finite G]
    (d : LocalData G) {I : Subgroup G} (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1) : primeRank 3 (d.MI I) = 1 := by
  apply le_antisymm (intersection_three_rank_le_one d h hr)
  rw [← hr]
  have hYM : d.Yplus ≤ d.MI I := h.residual ▸ map_subtype_le _
  exact Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hYM)
    (inclusion_injective hYM)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
