module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Minimal
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Constituents
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Solvable.Elementary
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Solvable.ConstituentBound
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Solvable.Dihedral
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Solvable.CyclicFive

/-!
# Exclusion of solvable minimal normal actors in 15.3.58

For an arbitrary solvable minimal normal subgroup of the actual faithful
irreducible actor, the small-prime exclusions leave elementary exponent p > 3.
The checked degree bound supplies the hypothesis of 15.3.57(2), and the
rank-two displacement makes [K, v] nontrivial. The source extraspecial product
and its elementary subgroup construct a marked D₈. Its action shows that
[K, v] cannot be cyclic. The rank-two small-support theorem identifies the
same literal commutator with C₅, contradicting solvability.

Earlier source inputs remain explicit: the faithful irreducible action, s > 0,
degree and displacement rank, the three-free centralizer, and the marked
extraspecial product of 15.3.56(6), containing the elementary subgroup of order
2^(s+1) from 15.3.56(4). The source-theorem assembly supplies these inputs;
neither inversion nor a cyclic-five or dihedral witness is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1149.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The intermediate solvable-case reduction: prime exponent greater than three
and a nontrivial, noncyclic commutator. The cyclic-five theorem contradicts this
conclusion in `minimalNormal_not_solvable`. -/
theorem solvable_minimalNormal_reduction
    (ρ : Representation (ZMod 2) G W) (hρ : ρ.IsIrreducible)
    (hf : Function.Injective ρ) (K : Subgroup G) (hK : IsMinimalNormal K)
    [Group.IsSolvable K]
    (v : G) (hv : IsInvolution v) (s : ℕ) (hs : 0 < s)
    (hC : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({v} : Set G)))
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) = 2)
    (hdim : Module.finrank (ZMod 2) W = 2 * (s + 2))
    (P : Subgroup G) [IsExtraspecial 2 P] (X : Subgroup P)
    [IsElementaryAbelian 2 X] (hX : Nat.card X = 2 ^ (s + 1))
    (hZ : (Subgroup.center P).map P.subtype = Subgroup.zpowers v) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsElementaryAbelian p K ∧
      (⨆ a : K, LinearMap.range (ρ a - LinearMap.id)) = ⊤ ∧
      (∀ A : Subrepresentation (ρ.comp K.subtype), A.toRepresentation.IsIrreducible →
        3 ≤ Module.finrank (ZMod 2) A.toSubmodule) ∧
      ⁅K, Subgroup.zpowers v⁆ ≠ ⊥ ∧
      ¬ IsCyclic (⁅K, Subgroup.zpowers v⁆ : Subgroup G) := by
  let := hK.1
  obtain ⟨p, hp, hlarge, hE⟩ :=
    minimalNormal_solvable_prime_gt_three ρ hρ hf K hK v hv s hs hC hrank hdim
  let := hE
  let : Fact p.Prime := ⟨hp⟩
  have hP := IsElementaryAbelian.isPGroup p K
  have hsmall := normal_pGroup_constituent_finrank_ge_three ρ hρ hf K hK.2.1 hlarge hP
  have hnoncomm := Representation.commutator_zpowers_ne_bot_of_small_displacement ρ K v
      (fun A hA => by rw [hrank]; exact hsmall A hA) (by rw [hrank]; decide)
  have hXlarge : 2 < Nat.card X := by
    rw [hX]
    calc
      2 = 2 ^ 1 := by decide
      _ < 2 ^ (s + 1) := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  obtain ⟨f, _, hmark⟩ := exists_marked_dihedral_of_extraspecial P X hXlarge v hv.1 hZ
  have hodd : Odd (Nat.card K) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two (by omega)).pow
  exact ⟨p, hp, hlarge, hE,
    Representation.NormalConstituentDisplacement.normal_commutator_span_eq_top ρ hρ hf K hK.2.1,
    hsmall, hnoncomm, odd_normal_commutator_not_cyclic_of_marked_dihedral K hodd v hv f hmark hnoncomm⟩

/-- The solvable minimal normal case is impossible under the earlier source
dimension, centralizer and marked extraspecial-product facts of 15.3.58. -/
theorem minimalNormal_not_solvable
    (ρ : Representation (ZMod 2) G W) (hρ : ρ.IsIrreducible)
    (hf : Function.Injective ρ) (K : Subgroup G) (hK : IsMinimalNormal K)
    (v : G) (hv : IsInvolution v) (s : ℕ) (hs : 0 < s)
    (hC : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({v} : Set G)))
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) = 2)
    (hdim : Module.finrank (ZMod 2) W = 2 * (s + 2))
    (P : Subgroup G) [IsExtraspecial 2 P] (X : Subgroup P)
    [IsElementaryAbelian 2 X] (hX : Nat.card X = 2 ^ (s + 1))
    (hZ : (Subgroup.center P).map P.subtype = Subgroup.zpowers v) :
    ¬ Group.IsSolvable K := by
  intro hsolv
  let := hsolv
  obtain ⟨p, hp, hlarge, hE, -, -, hne, hnotcyclic⟩ :=
    solvable_minimalNormal_reduction ρ hρ hf K hK v hv s hs hC hrank hdim P X hX hZ
  let := hK.1
  let : Fact p.Prime := ⟨hp⟩
  let := hE
  obtain ⟨_, ⟨e⟩⟩ := elementary_normal_commutator_cyclic_five_of_rank_two
    ρ hf K hlarge v hv hrank hne
  exact hnotcyclic (e.isCyclic.mpr inferInstance)
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- The complete reduction above on the literal faithful H/O₂(H) action on U/Z. The extraspecial product and its marked center are explicit earlier 15.3.56 inputs. -/
theorem actor_solvable_minimalNormal_reduction
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hρ : (actorRepresentation Z ZS hkernel).IsIrreducible)
    (K : Subgroup (ActorQuotient Z)) (hK : IsMinimalNormal K) [Group.IsSolvable K]
    (v : ActorQuotient Z) (hv : IsInvolution v) (s : ℕ) (hs : 0 < s)
    (hC : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({v} : Set (ActorQuotient Z))))
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)) = 2)
    (hdim : Module.finrank (ZMod 2) (Space Z ZS) = 2 * (s + 2))
    (P : Subgroup (ActorQuotient Z)) [IsExtraspecial 2 P] (X : Subgroup P)
    [IsElementaryAbelian 2 X] (hX : Nat.card X = 2 ^ (s + 1))
    (hZ : (Subgroup.center P).map P.subtype = Subgroup.zpowers v) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsElementaryAbelian p K ∧
      (⨆ a : K, LinearMap.range (actorRepresentation Z ZS hkernel a - LinearMap.id)) = ⊤ ∧
      (∀ A : Subrepresentation ((actorRepresentation Z ZS hkernel).comp K.subtype),
        A.toRepresentation.IsIrreducible → 3 ≤ Module.finrank (ZMod 2) A.toSubmodule) ∧
      ⁅K, Subgroup.zpowers v⁆ ≠ ⊥ ∧
      ¬ IsCyclic (⁅K, Subgroup.zpowers v⁆ : Subgroup (ActorQuotient Z)) :=
  solvable_minimalNormal_reduction (actorRepresentation Z ZS hkernel) hρ
    (actorRepresentation_injective Z ZS hkernel) K hK v hv s hs hC hrank hdim P X hX hZ

/-- Every minimal nontrivial normal subgroup of the literal actor `H/O₂(H)`
is nonsolvable, conditional on the earlier 15.3.51–56 configuration facts.
The cyclic-five identification and the marked dihedral subgroup are proved
from these inputs, rather than supplied as additional hypotheses. -/
theorem actor_minimalNormal_not_solvable
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hρ : (actorRepresentation Z ZS hkernel).IsIrreducible)
    (K : Subgroup (ActorQuotient Z)) (hK : IsMinimalNormal K)
    (v : ActorQuotient Z) (hv : IsInvolution v) (s : ℕ) (hs : 0 < s)
    (hC : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({v} : Set (ActorQuotient Z))))
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)) = 2)
    (hdim : Module.finrank (ZMod 2) (Space Z ZS) = 2 * (s + 2))
    (P : Subgroup (ActorQuotient Z)) [IsExtraspecial 2 P] (X : Subgroup P)
    [IsElementaryAbelian 2 X] (hX : Nat.card X = 2 ^ (s + 1))
    (hZ : (Subgroup.center P).map P.subtype = Subgroup.zpowers v) :
    ¬ Group.IsSolvable K :=
  minimalNormal_not_solvable (actorRepresentation Z ZS hkernel) hρ
    (actorRepresentation_injective Z ZS hkernel) K hK v hv s hs hC hrank hdim P X hX hZ
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
