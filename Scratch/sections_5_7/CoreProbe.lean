module
public import Stellmacher.FinalTheorem
public import Theory.Quasithin
public import Theory.Comparator.Defs
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.Gorenstein.Chapter8_2
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Sylow
open scoped Pointwise

namespace Stellmacher
namespace SectionsFiveToSeven

variable {G : Type*} [Group G]

@[expose] public def twoCoreIn (P : Subgroup G) : Subgroup G :=
  (pCore 2 P).map P.subtype

@[expose] public def twoResidualIn (P : Subgroup G) : Subgroup G :=
  (Op_p'p 2 P).map P.subtype

@[expose] public def omegaOneCenter (P : Subgroup G) : Subgroup G :=
  ((omega₁ (G := Subgroup.center P) (p := 2)).map (Subgroup.center P).subtype).map P.subtype

@[expose] public def baumannIn (P : Subgroup G) : Subgroup G :=
  P ⊓ Subgroup.centralizer
    (((omega₁ (G := thompsonCenter (G := G) P) (p := 2)).map
      (thompsonCenter (G := G) P).subtype : Subgroup G) : Set G)

@[expose] public def NormalIn (A P : Subgroup G) : Prop :=
  A ≤ P ∧ (A.subgroupOf P).Normal

@[expose] public def SubnormalIn (A P : Subgroup G) : Prop :=
  A ≤ P ∧ (A.subgroupOf P).IsSubnormal

@[expose] public def IsSylowTwoIn (S P : Subgroup G) : Prop :=
  S ≤ P ∧ ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype = S

@[expose] public def HasUniqueMaximalOver (S P : Subgroup G) : Prop :=
  S ≤ P ∧ ∃ M : Subgroup P,
    IsCoatom M ∧ S.subgroupOf P ≤ M ∧
      ∀ M' : Subgroup P, IsCoatom M' → S.subgroupOf P ≤ M' → M' = M

@[expose] public def IsLMember (U S P : Subgroup G) : Prop :=
  P ≤ U ∧ IsSylowTwoIn S P ∧ twoCoreIn P ≠ ⊥ ∧ S ≠ twoCoreIn P

@[expose] public def IsPMember (U S P : Subgroup G) : Prop :=
  IsLMember U S P ∧ HasUniqueMaximalOver S P

@[expose] public def IsMaximalLMember (U S L : Subgroup G) : Prop :=
  IsLMember U S L ∧ ∀ L' : Subgroup G, IsLMember U S L' → L ≤ L' → L' = L

@[expose] public def IsPStarMember (U S P : Subgroup G) : Prop :=
  IsPMember U S P ∧
    ∃ L : Subgroup G,
      IsMaximalLMember U S L ∧ SubnormalIn (twoResidualIn P) L

@[expose] public def PFamily (U S : Subgroup G) : Set (Subgroup G) :=
  {P | IsPMember U S P}

@[expose] public def PStarFamily (U S : Subgroup G) : Set (Subgroup G) :=
  {P | IsPStarMember U S P}

@[expose] public def IsMaximalTwoLocalContaining (S M : Subgroup G) : Prop :=
  Theory.Quasithin.IsMaximalTwoLocal M ∧ S ≤ M

@[expose] public def UniqueMaximalTwoLocalContaining (S M : Subgroup G) : Prop :=
  IsMaximalTwoLocalContaining S M ∧
    ∀ M' : Subgroup G, IsMaximalTwoLocalContaining S M' → M' = M

@[expose] public def conjugateClosure (X A : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ a : A, ∃ y : X, x = (a : G) * (y : G) * (a : G)⁻¹}

@[expose] public def actionFixedIn (V A : Subgroup G) : Subgroup G :=
  V ⊓ Subgroup.centralizer (A : Set G)

@[expose] public def actionCriticalSubgroup (V S : Subgroup G) : Subgroup G :=
  sSup {A : Subgroup G | A ≤ S ∧ IsElementaryAbelian 2 A ∧
    Nat.card V ≤ Nat.card (actionFixedIn V A) * Nat.card A}

@[expose] public def actionFixedCentralizer (V A : Subgroup G) : Subgroup G :=
  actionFixedIn V A

public structure HypothesisOne (H : Type*) [Group H] [Finite H]
    (S0 : Sylow 2 H) : Prop where
  even_order : Even (Nat.card H)
  local_solvable_characteristicTwo :
    ∀ U : Subgroup H,
      Theory.Quasithin.IsTwoLocal U → (S0 : Subgroup H) ≤ U →
        Group.IsSolvable U ∧ Stellmacher.IsCharacteristicTwoType U
  twoCore_eq_bot : pCore 2 H = ⊥
  no_strongly_embedded : ¬ ∃ M : Subgroup H, Theory.Comparator.IsStronglyEmbedded M

public inductive FiveOneAlternative
    (H : Type*) [Group H] [Finite H] (S0 : Sylow 2 H)
    (S P1 P2 : Subgroup H) : Prop
  | a
      (_ : S = (S0 : Subgroup H))
      (_ : ¬ NormalIn (omegaOneCenter S) P1)
      (_ : ¬ NormalIn (omegaOneCenter S) P2)
  | b
      (_ : S = (S0 : Subgroup H))
      (_ : P2 ∈ PStarFamily (Subgroup.centralizer (omegaOneCenter S : Set H)) S)
  | c
      (M : Subgroup H)
      (_ : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
      (_ : S ≠ (S0 : Subgroup H))
      (_ : ¬ NormalIn (omegaOneCenter S) P1)
      (_ : ¬ NormalIn (omegaOneCenter S) P2)
      (_ : ¬ NormalIn (thompsonSubgroup (G := H) S) P1)
      (_ : ¬ NormalIn (thompsonSubgroup (G := H) S) P2)
      (_ : ¬ P1 ≤ M)
      (_ : ¬ P2 ≤ M)
      (_ : IsSylowTwoIn S (Subgroup.normalizer (twoCoreIn P1 : Set H)))
      (_ : IsSylowTwoIn S (Subgroup.normalizer (twoCoreIn P2 : Set H)))
      (_ : ∀ T : Subgroup H, thompsonSubgroup (G := H) S ≤ T →
        T ≤ (S0 : Subgroup H) →
        ∀ P1' P2' : Subgroup H,
          P1' ∈ PFamily (⊤ : Subgroup H) T → P2' ∈ PFamily (⊤ : Subgroup H) T →
          twoCoreIn (P1' ⊔ P2') ≠ ⊥ →
          (P1' ⊔ P2') ≤ M ∨
            ∀ S1 : Subgroup H, T ≤ S1 → IsSylowTwoIn S1 (P1' ⊔ P2') →
              thompsonSubgroup (G := H) S = thompsonSubgroup (G := H) S1)

public structure FiveOneConditions
    (H : Type*) [Group H] [Finite H] (S0 : Sylow 2 H)
    (S P1 P2 : Subgroup H) : Prop where
  S_nontrivial : S ≠ ⊥
  S_le_S0 : S ≤ (S0 : Subgroup H)
  P1_mem : P1 ∈ PFamily (⊤ : Subgroup H) S
  P2_mem : P2 ∈ PFamily (⊤ : Subgroup H) S
  join_twoCore_eq_bot : twoCoreIn (P1 ⊔ P2) = ⊥
  alternative : FiveOneAlternative H S0 S P1 P2

public structure HypothesisTwo (H : Type*) [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H) : Prop where
  hyp1 : HypothesisOne H S0
  fiveOne : FiveOneConditions H S0 S P1 P2
  local_B :
    ∀ U : Subgroup H,
      Theory.Quasithin.IsTwoLocal U → baumannIn S ≤ U →
        Group.IsSolvable U ∧ Stellmacher.IsCharacteristicTwoType U

end SectionsFiveToSeven
end Stellmacher

