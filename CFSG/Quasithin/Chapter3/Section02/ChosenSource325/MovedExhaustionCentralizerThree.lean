module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizerPrime
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer

/-!
# Order-three support in the chosen-seed centralizer argument

A nontrivial three-subgroup X = [X,C_A(K)] contains a hyperplane support
moved by the same centralizer. D.2.13 makes the ambient support cyclic of
order three; its nontrivial subgroup Y is therefore that whole support.
This retains its binary moved plane as well as its order and A-invariance.

The original rank-two cover bounds K's three-rank by one in this branch:
an involution in C_A(K) moves the ambient three-core, so A.1.31 bounds its
full centralizer. If A itself centralized K, the selected moved plane would
be K-invariant. Perfectness and fixed-freeness then give a contradiction.
Thus this branch supplies the proper-centralizer input to D.3.19.

`SeedAlternativesMovedExhaustionCentralizerThree` applies this to the literal
normalizer image and its original Sylow orbit. The component branch, section
FF exclusions, full exhaustion and Source325 assembly remain with qt-baumann-fsu.
In particular neither nontriviality of C_A(K) nor exhaustion follows merely
from the cubic bound. The SL3 central cover is retained throughout.
Source: Aschbacher--Smith D.2.13(5), D.3.9(2), D.3.14 and D.3.18--19,
printed pp.184--185 and200--204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterD
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Select an order-three support still moved by the specified component
centralizer, retaining its hyperplane and binary moved plane. -/
theorem exists_order_three_hyperplane_support_moved_by_centralizer
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (K : Subgroup H) [Group.IsPerfect K]
    (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    {A : Subgroup H} (hA : A ∈ QhatStar ρ)
    (hBn : A ⊓ centralizer (K : Set H) ≠ ⊥)
    (X : Subgroup H) (hXcore : X ≤ pCore 3 H)
    (hAX : A ≤ normalizer (X : Set H)) (hXn : X ≠ ⊥)
    (hXB : ⁅X,A ⊓ centralizer (K : Set H)⁆ = X) :
    ∃ Y : Subgroup H, Y ≤ X ∧ A ≤ normalizer (Y : Set H) ∧
      Nat.card Y = 3 ∧ ⁅Y,A ⊓ centralizer (K : Set H)⁆ = Y ∧
      ∃ D : Subgroup H, D ≤ A ∧ rank D + 1 = rank A ∧
        Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ D) Y) = 2 := by
  classical
  let B := A ⊓ centralizer (K : Set H)
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hrne : rank A ≠ 1 := fun hr => hBn
    (rank_one_starred_component_centralizer_eq_bot ρ hf K hfull hA hr)
  have hrpos := hA.1.2.1.rank_pos
  have hr : 1 < rank A := by omega
  have hXA : ⁅X,A⁆ = X := by
    apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hAX)
    calc
      X = ⁅X,B⁆ := hXB.symm
      _ ≤ ⁅X,A⁆ := commutator_mono le_rfl inf_le_left
  have hgen := eq_iSup_hyperplane_centralizer_commutator (by decide : (3 : ℕ) ≠ 2)
    X A (pCore_isPGroup.to_le hXcore) hAX hXA.symm
  let F (D : Subgroup A) := ⁅X ⊓ centralizer (D.map A.subtype : Set H),A⁆
  have hex : ∃ D : Subgroup A, D.index = 2 ∧ ⁅F D,B⁆ ≠ ⊥ := by
    by_contra! hh
    have hc : X ≤ centralizer (B : Set H) := by
      rw [hgen]
      exact iSup₂_le fun D hi => commutator_eq_bot_iff_le_centralizer.mp (hh D hi)
    apply hXn
    rw [←hXB]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  obtain ⟨D,hidx,hm⟩ := hex
  let Y := F D
  let D₀ := D.map A.subtype
  let Z := ⁅pCore 3 H ⊓ centralizer (D₀ : Set H),A⁆
  have hAY : A ≤ normalizer (Y : Set H) := normalizer_commutator_ge_right _ _
  have hYX : Y ≤ X := (commutator_mono inf_le_left le_rfl).trans hXA.le
  have hYZ : Y ≤ Z := commutator_mono (inf_le_inf_right _ hXcore) le_rfl
  have hYn : Y ≠ ⊥ := by
    intro hz
    apply hm
    change ⁅Y,B⁆ = ⊥
    simp only [hz,commutator_bot_left]
  have hZn : Z ≠ ⊥ := fun hz => hYn (bot_unique (hYZ.trans hz.le))
  have hDtwo := (IsElementaryAbelian.isPGroup 2 A).to_subgroup D
  obtain ⟨n,hcardD⟩ := hDtwo.exists_card_eq
  have hc := D.card_mul_index
  rw [hidx,hcardD,hA.1.2.1.card_eq_two_pow_rank] at hc
  have hn : n + 1 = rank A := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2 ^ (n + 1) = 2 ^ rank A
    rw [pow_succ]
    exact hc
  have hDrank : rank D₀ + 1 = rank A := by
    change Nat.log 2 (Nat.card (D.map A.subtype)) + 1 = rank A
    rw [card_map_of_injective A.subtype_injective,hcardD,
      Nat.log_pow (by decide : 1 < 2)]
    exact hn
  have hsupp := source_lemma_D_2_13_noncyclic_support ρ hf hA hr D₀
    (map_subtype_le D) hDrank hZn
  have hZcard : Nat.card Z = 3 := hsupp.1
  have hYcard : Nat.card Y = 3 := by
    have hd := card_dvd_of_le hYZ
    rw [hZcard] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with he | he
    · exact (hYn (Subgroup.card_eq_one.mp he)).elim
    · exact he
  have hYB : ⁅Y,B⁆ ≤ Y :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hAY)
  have hYBcard : Nat.card (⁅Y,B⁆ : Subgroup H) = 3 := by
    have hd := card_dvd_of_le hYB
    rw [hYcard] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with he | he
    · exact (hm (Subgroup.card_eq_one.mp he)).elim
    · exact he
  have he : Y = Z := eq_of_le_of_card_ge hYZ (by rw [hYcard,hZcard])
  refine ⟨Y,hYX,hAY,hYcard,eq_of_le_of_card_ge hYB (by rw [hYcard,hYBcard]),
    D₀,map_subtype_le D,hDrank,?_⟩
  rw [he]
  exact hsupp.2.2.1


/-- The three-core branch forces three-rank at most one on the original
component, using rank on an actual cover rather than quotient monotonicity. -/
theorem component_three_rank_le_one_of_moved_three_core
    {P : Type*} [Group P] [Finite P]
    (f : P →* H) (hf : Function.Surjective f) (hr : primeRank 3 P ≤ 2)
    (K A X : Subgroup H) [IsElementaryAbelian 2 A]
    (hXcore : X ≤ pCore 3 H) (hXn : X ≠ ⊥)
    (hXB : ⁅X,A ⊓ centralizer (K : Set H)⁆ = X) : primeRank 3 K ≤ 1 := by
  let B := A ⊓ centralizer (K : Set H)
  have hn : ¬ B ≤ centralizer (pCore 3 H : Set H) := by
    intro hh
    apply hXn
    rw [←hXB]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact le_centralizer_iff.mp (hh.trans (centralizer_le hXcore))
  obtain ⟨t,ht,hm⟩ := Set.not_subset.mp hn
  have htne : t ≠ 1 := fun he => hm (he ▸ (centralizer (pCore 3 H : Set H)).one_mem)
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht.1) htne
  have hK : K ≤ centralizer ({t} : Set H) := by
    intro k hk x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact (ht.2 k hk).symm
  exact (primeRank_mono 3 hK).trans
    (primeRank_involutionCentralizer_le_one_of_surjective_rank_le_two
      (by decide : Odd 3) f hf hr (pCore 3 H) pCore_isPGroup t ht2 hm)


/-- A starred actor centralizing a fixed-free perfect component cannot move
its centralizer's three-core. The selected hyperplane support is a binary
plane invariant under K, hence fixed by K, contradicting fixed-freeness. -/
theorem starred_not_centralizing_of_moved_three_core
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (K : Subgroup H) [Group.IsPerfect K]
    (hfull : subspaceCommutator ρ ⊤ K = ⊤) (hfixed : fixedSpace ρ K = ⊥)
    {A : Subgroup H} (hA : A ∈ QhatStar ρ)
    (X : Subgroup H) (hXC : X ≤ centralizer (K : Set H))
    (hXcore : X ≤ pCore 3 H) (hAX : A ≤ normalizer (X : Set H))
    (hXn : X ≠ ⊥) (hXA : ⁅X,A⁆ = X) : ¬ A ≤ centralizer (K : Set H) := by
  intro hAc
  have hAB : A ⊓ centralizer (K : Set H) = A := inf_eq_left.mpr hAc
  have hBn : A ⊓ centralizer (K : Set H) ≠ ⊥ := by
    rw [hAB]
    exact hA.1.2.1.1
  obtain ⟨Y,hYX,_,_,_,D,hDA,_,hdim⟩ :=
    exists_order_three_hyperplane_support_moved_by_centralizer ρ hf K hfull hA hBn
      X hXcore hAX hXn (by simpa only [hAB] using hXA)
  let J := subspaceCommutator ρ (fixedSpace ρ D) Y
  have hKD : K ≤ subspaceStabilizer ρ (fixedSpace ρ D) :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ K D
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp (hDA.trans hAc)))
  have hKJ : K ≤ subspaceStabilizer ρ J :=
    subspaceCommutator_invariant_normalizer ρ hKD
      ((le_centralizer_iff.mp (hYX.trans hXC)).trans (Subgroup.centralizer_le_normalizer _))
  have hJfix : J ≤ fixedSpace ρ K := by
    intro v hv k
    exact congrArg Subtype.val (LinearMap.congr_fun
      (representation_eq_one_of_isPerfect_of_finrank_le_two
        (invariantSubspace ρ K J hKJ).toRepresentation (show Module.finrank (ZMod 2) J ≤ 2 from hdim.le) k) ⟨v,hv⟩)
  have hz : J = ⊥ := bot_unique (hJfix.trans hfixed.le)
  change Module.finrank (ZMod 2) J = 2 at hdim
  rw [hz] at hdim
  simp at hdim

/-- Refine the three-core choice to an actual subgroup of order three.
The nonabelian alternative is still the literal orbit of a component. -/
theorem exists_starred_order_three_or_component_in_centralizer
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hcore : pCore 2 H = ⊥) (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    {A : Subgroup H} (hA : A ∈ QhatStar ρ)
    (hBn : A ⊓ centralizer (K : Set H) ≠ ⊥) :
    let C := centralizer (K : Set H)
    ∃ X : Subgroup H, X ≤ C ∧ A ≤ normalizer (X : Set H) ∧ X ≠ ⊥ ∧
      ⁅X,A ⊓ C⁆ = X ∧
      ((X ≤ (pCore 3 C).map C.subtype ∧ Nat.card X = 3) ∨
        ∃ J : Subgroup H, IsComponent H J ∧ J ≤ C ∧ X = componentOrbit J A) := by
  let C := centralizer (K : Set H)
  obtain ⟨X,hXC,hn,hXn,hXB,hcase⟩ :=
    exists_starred_moved_subgroup_in_component_centralizer ρ hf K hcore hfull hA hBn
  rcases hcase with ⟨hXP,_⟩ | hcomp
  · have hP : (pCore 3 C).map C.subtype ≤ pCore 3 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map C.subtype⟩
    obtain ⟨Y,hYX,hAY,hYcard,hYB,_⟩ :=
      exists_order_three_hyperplane_support_moved_by_centralizer ρ hf K hfull hA hBn
        X (hXP.trans hP) hn hXn hXB
    refine ⟨Y,hYX.trans hXC,hAY,?_,hYB,Or.inl ⟨hYX.trans hXP,hYcard⟩⟩
    intro he
    rw [he,card_bot] at hYcard
    omega
  · exact ⟨X,hXC,hn,hXn,hXB,Or.inr hcomp⟩

/-- The order-three branch forces three-rank at most one on the original K
and noncentral action by A. Both conclusions preserve the actual cover and K. -/
theorem exists_starred_proper_three_or_component_in_centralizer
    {P : Type*} [Group P] [Finite P]
    (f : P →* H) (hfs : Function.Surjective f) (hr : primeRank 3 P ≤ 2)
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hcore : pCore 2 H = ⊥) (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    (hfixed : fixedSpace ρ K = ⊥)
    {A : Subgroup H} (hA : A ∈ QhatStar ρ)
    (hBn : A ⊓ centralizer (K : Set H) ≠ ⊥) :
    let C := centralizer (K : Set H)
    ∃ X : Subgroup H, X ≤ C ∧ A ≤ normalizer (X : Set H) ∧ X ≠ ⊥ ∧
      ⁅X,A ⊓ C⁆ = X ∧
      ((X ≤ (pCore 3 C).map C.subtype ∧ Nat.card X = 3 ∧ primeRank 3 K ≤ 1 ∧ ¬ A ≤ C) ∨
        ∃ J : Subgroup H, IsComponent H J ∧ J ≤ C ∧ X = componentOrbit J A) := by
  let C := centralizer (K : Set H)
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨X,hXC,hn,hXn,hXB,hcase⟩ :=
    exists_starred_order_three_or_component_in_centralizer ρ hf K hcore hfull hA hBn
  refine ⟨X,hXC,hn,hXn,hXB,?_⟩
  rcases hcase with ⟨hXP,hXcard⟩ | hcomp
  · have hP : (pCore 3 C).map C.subtype ≤ pCore 3 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map C.subtype⟩
    have hXA : ⁅X,A⁆ = X := le_antisymm
      (le_normalizer_iff_commutator_le_left.mp hn)
      (hXB.symm.le.trans (commutator_mono le_rfl inf_le_left))
    exact Or.inl ⟨hXP,hXcard,component_three_rank_le_one_of_moved_three_core
      f hfs hr K A X (hXP.trans hP) hXn hXB,
      starred_not_centralizing_of_moved_three_core ρ hf K hfull hfixed hA
        X hXC (hXP.trans hP) hn hXn hXA⟩
  · exact Or.inr hcomp

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
