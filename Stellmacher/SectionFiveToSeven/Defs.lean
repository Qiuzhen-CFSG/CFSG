module
public import Stellmacher.FinalTheorem
public import Stellmacher.SectionsOneToFourDefs
public import Theory.Quasithin
public import Theory.Comparator.Defs
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.Gorenstein.Chapter8_2
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Sylow
open scoped Pointwise

universe u v

namespace Stellmacher
namespace SectionsFiveToSeven

variable {G : Type*} [Group G]

@[expose] public def twoCoreIn (P : Subgroup G) : Subgroup G :=
  (pCore 2 P).map P.subtype

@[expose] public noncomputable def twoResidualIn (P : Subgroup G) : Subgroup G :=
  twoResidualAmbient P

@[expose] public def omegaOneCenter (P : Subgroup G) : Subgroup G :=
  ((omega₁ (G := Subgroup.center P) (p := 2)).map (Subgroup.center P).subtype).map P.subtype

@[expose] public def baumannIn (P : Subgroup G) : Subgroup G :=
  P ⊓ Subgroup.centralizer
    (omegaOneCenter (elementaryAbelianMaxJ (G := G) P) : Set G)

@[expose] public def NormalIn (A P : Subgroup G) : Prop :=
  A ≤ P ∧ (A.subgroupOf P).Normal

@[expose] public def SubnormalIn (A P : Subgroup G) : Prop :=
  A ≤ P ∧ (A.subgroupOf P).IsSubnormal

@[expose] public def IsSylowTwoIn (S P : Subgroup G) : Prop :=
  S ≤ P ∧ ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype = S

/- A Sylow subgroup of an intersection, viewed in the ambient group. -/
@[expose] public def sylowTwoAmbient
    (I : Subgroup G) (T : Sylow 2 I) : Subgroup G :=
  (T : Subgroup I).map I.subtype

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

@[expose] public def conjugateBy (A : Subgroup G) (x : G) : Subgroup G :=
  A.map (MulAut.conj x).toMonoidHom

@[expose] public def conjugateOrbit (X A : Subgroup G) : Set G :=
  {x : G | ∃ a : A, ∃ y : X, x = (a : G) * (y : G) * (a : G)⁻¹}

@[expose] public noncomputable def frattiniAmbient (A : Subgroup G) : Subgroup G :=
  (frattini A).map A.subtype

@[expose] public def actionFixedIn (V A : Subgroup G) : Subgroup G :=
  V ⊓ Subgroup.centralizer (A : Set G)

@[expose] public def actionCriticalSubgroup (V S : Subgroup G) : Subgroup G :=
  sSup {A : Subgroup G | A ≤ S ∧ IsElementaryAbelian 2 A ∧
    Nat.card V ≤ Nat.card (actionFixedIn V A) * Nat.card A}

@[expose] public def actionFixedCentralizer (V A : Subgroup G) : Subgroup G :=
  actionFixedIn V A

/- Section 6's generated-subgroup notation. -/
@[expose] public def sectionSixL (B P : Subgroup G) : Subgroup G :=
  conjugateClosure B P

@[expose] public def sectionSixZ (B P : Subgroup G) : Subgroup G :=
  conjugateClosure (omegaOneCenter B) P

@[expose] public def sectionSixV (S P : Subgroup G) : Subgroup G :=
  conjugateClosure (omegaOneCenter S) P

/- The subgroup `⟨S, C_{P₂}(w)⟩` occurring pointwise in (6.4). -/
@[expose] public def sectionSixCentralizerJoin
    (P2 S : Subgroup G) (w : G) : Subgroup G :=
  (P2 ⊓ Subgroup.centralizer (Subgroup.zpowers w : Set G)) ⊔ S

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
      (_ : ¬ NormalIn (elementaryAbelianMaxJ (G := H) S) P1)
      (_ : ¬ NormalIn (elementaryAbelianMaxJ (G := H) S) P2)
      (_ : ¬ P1 ≤ M)
      (_ : ¬ P2 ≤ M)
      (_ : IsSylowTwoIn S (Subgroup.normalizer (twoCoreIn P1 : Set H)))
      (_ : IsSylowTwoIn S (Subgroup.normalizer (twoCoreIn P2 : Set H)))
      (_ : ∀ T : Subgroup H, elementaryAbelianMaxJ (G := H) S ≤ T →
        T ≤ (S0 : Subgroup H) →
        ∀ P1' P2' : Subgroup H,
          P1' ∈ PFamily (⊤ : Subgroup H) T →
          P2' ∈ PFamily (⊤ : Subgroup H) T →
          twoCoreIn (P1' ⊔ P2') ≠ ⊥ →
          (P1' ⊔ P2') ≤ M ∨
            ∀ S1 : Subgroup H, T ≤ S1 → IsSylowTwoIn S1 (P1' ⊔ P2') →
              elementaryAbelianMaxJ (G := H) S =
                elementaryAbelianMaxJ (G := H) S1)

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

/-- Standing assumptions for Section 7.  The graph results use only this
interface to the local subgroups, together with a `CosetGraphContext`. -/
public structure SectionSevenHypotheses
    (G : Type u) [Group G] [Finite G]
    (S P1 P2 : Subgroup G) : Prop where
  S_nontrivial : S ≠ ⊥
  P1_mem : P1 ∈ PFamily (⊤ : Subgroup G) S
  P2_mem : P2 ∈ PFamily (⊤ : Subgroup G) S
  generated : P1 ⊔ P2 = ⊤
  P1_solvable : Group.IsSolvable P1
  P2_solvable : Group.IsSolvable P2
  P1_characteristicTwo : Stellmacher.IsCharacteristicTwoType P1
  P2_characteristicTwo : Stellmacher.IsCharacteristicTwoType P2
  twoCore_eq_bot : pCore 2 G = ⊥

/-- A quotient-level formulation of the product notation
`\bar L ≅ D_{2p^n} × \bar A₀` used in (7.8).  The homomorphism `quotientMap`
is the quotient map on `L` (its kernel is `L ∩ Q`), and `barA0` is required to
be the image of `A₀`; thus `barL` and `barA0` are precisely the barred groups
in the source without relying on a global quotient-group instance. -/
public structure QuotientDihedralProduct
    {G : Type u} [Group G] (L Q A0 : Subgroup G) : Type (u + 1) where
  A0_le_L : A0 ≤ L
  p : ℕ
  n : ℕ
  p_prime : Nat.Prime p
  p_odd : Odd p
  barL : Type u
  [barL_group : Group barL]
  [barL_finite : Finite barL]
  barA0 : Subgroup barL
  quotientMap : (↥L) →* barL
  quotient_surjective : Function.Surjective quotientMap
  quotient_kernel : quotientMap.ker = (L ⊓ Q).subgroupOf L
  barA0_image :
    barA0 = Subgroup.map
      (quotientMap.comp (Subgroup.inclusion A0_le_L)) (⊤ : Subgroup A0)
  model : Nonempty (barL ≃* (DihedralGroup (p ^ n) × ↥barA0))

/-!
The coset graph in Section 7 is built from right cosets of `P₁` and `P₂`.
Mathlib's quotient type for right cosets does not carry a right action of the
whole ambient group without an auxiliary opposite-group action.  The record
below therefore packages the canonical graph together with its right-action
interface.  The fields `coset₁`, `coset₂`, `coset₁_eq_iff`, `coset₂_eq_iff`,
and `adj_cosets` are the defining right-coset conditions; all later notation
(`Gd`, `D(d)`, `Qd`, `Ed`, `Zd`, and `Vd`) is exposed explicitly as fields.
This is a statement-level interface only, so it does not assert any of the
Section 7 conclusions in advance.
-/

public structure CosetGraphContext
    (G : Type u) [Group G] [Finite G]
    (S P1 P2 : Subgroup G) : Type (max u v + 1) where
  Vertex : Type v
  [finiteVertex : Finite Vertex]
  adjacent : Vertex → Vertex → Prop
  adjacent_symm : ∀ {d l}, adjacent d l → adjacent l d
  act : G → Vertex → Vertex
  act_one : ∀ d, act 1 d = d
  act_mul : ∀ g h d, act (g * h) d = act h (act g d)
  coset₁ : G → Vertex
  coset₂ : G → Vertex
  coset₁_surjective : ∀ d, ∃ g, d = coset₁ g ∨ d = coset₂ g
  coset₁_eq_iff : ∀ g h,
    coset₁ g = coset₁ h ↔ MulOpposite.op g • (P1 : Set G) =
      MulOpposite.op h • (P1 : Set G)
  coset₂_eq_iff : ∀ g h,
    coset₂ g = coset₂ h ↔ MulOpposite.op g • (P2 : Set G) =
      MulOpposite.op h • (P2 : Set G)
  act_coset₁ : ∀ g h, act g (coset₁ h) = coset₁ (h * g)
  act_coset₂ : ∀ g h, act g (coset₂ h) = coset₂ (h * g)
  adj_cosets : ∀ g h,
    adjacent (coset₁ g) (coset₂ h) ↔
      (MulOpposite.op g • (P1 : Set G)) ∩
          (MulOpposite.op h • (P2 : Set G)) ≠ ∅
  no_adj_coset₁_coset₁ : ∀ g h, ¬ adjacent (coset₁ g) (coset₁ h)
  no_adj_coset₂_coset₂ : ∀ g h, ¬ adjacent (coset₂ g) (coset₂ h)
  vertexStabilizer : Vertex → Subgroup G
  stabilizer_def : ∀ d, vertexStabilizer d =
    {g | act g d = d}
  distance : Vertex → Vertex → ℕ
  distance_refl : ∀ d, distance d d = 0
  distance_symm : ∀ d l, distance d l = distance l d
  distance_zero_iff : ∀ d l, distance d l = 0 ↔ d = l
  distance_path : ∀ d l,
    ∃ f : Fin (distance d l + 1) → Vertex,
      f 0 = d ∧
        f ⟨distance d l, Nat.lt_succ_self (distance d l)⟩ = l ∧
        ∀ i : Fin (distance d l), adjacent (f i.castSucc) (f i.succ)
  distance_le_of_path : ∀ (n : ℕ) (f : Fin (n + 1) → Vertex),
    (∀ i : Fin n, adjacent (f i.castSucc) (f i.succ)) →
      distance (f 0) (f ⟨n, Nat.lt_succ_self n⟩) ≤ n
  neighbors : Vertex → Set Vertex
  neighbors_def : ∀ d, neighbors d = {l | distance l d = 1}
  twoCoreAt : Vertex → Subgroup G
  twoCoreAt_def : ∀ d, twoCoreAt d = twoCoreIn (vertexStabilizer d)
  twoResidualAt : Vertex → Subgroup G
  twoResidualAt_def : ∀ d, twoResidualAt d = twoResidualIn (vertexStabilizer d)
  zAt : Vertex → Subgroup G
  zAt_def : ∀ d, zAt d =
    sSup {Z : Subgroup G |
      ∃ T : Sylow 2 (vertexStabilizer d),
        Z = omegaOneCenter ((T : Subgroup (vertexStabilizer d)).map
          (vertexStabilizer d).subtype)}
  vAt : Vertex → Subgroup G
  vAt_def : ∀ d, vAt d = sSup {Z : Subgroup G | ∃ l ∈ neighbors d, Z = zAt l}
  actionKernel : Subgroup G
  actionKernel_def : ∀ g, g ∈ actionKernel ↔ ∀ d, act g d = d

namespace CosetGraphContext

instance {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2) :
    Finite Γ.Vertex := Γ.finiteVertex

@[expose] public def stabilizer
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.vertexStabilizer d

@[expose] public def neighborhood
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Set Γ.Vertex := Γ.neighbors d

@[expose] public def q
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.twoCoreAt d

@[expose] public def e
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.twoResidualAt d

@[expose] public def z
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.zAt d

@[expose] public def v
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.vAt d

@[expose] public def IsAdjacent
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (d l : Γ.Vertex) : Prop := Γ.adjacent d l

@[expose] public def IsActionTransitiveOn
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (K : Subgroup G) (X : Set Γ.Vertex) : Prop :=
  ∀ ⦃d l : Γ.Vertex⦄, d ∈ X → l ∈ X →
    ∃ g : K, Γ.act (g : G) d = l

@[expose] public def IsEdgeTransitive
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2) : Prop :=
  ∀ ⦃d l d' l' : Γ.Vertex⦄,
    Γ.adjacent d l → Γ.adjacent d' l' →
      ∃ g : G,
        (Γ.act g d = d' ∧ Γ.act g l = l') ∨
          (Γ.act g d = l' ∧ Γ.act g l = d')

@[expose] public def IsVertexTransitive
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2) : Prop :=
  ∀ d l : Γ.Vertex, ∃ g : G, Γ.act g d = l

@[expose] public def IsConnected
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2) : Prop :=
  ∀ d l : Γ.Vertex,
    ∃ n : ℕ, ∃ f : Fin (n + 1) → Γ.Vertex,
      f 0 = d ∧ f ⟨n, Nat.lt_succ_self n⟩ = l ∧
      ∀ i : Fin n, Γ.adjacent (f i.castSucc) (f i.succ)

@[expose] public def IsNormalIn
    {G : Type*} [Group G] (A K : Subgroup G) : Prop :=
  A ≤ K ∧ (A.subgroupOf K).Normal

@[expose] public def IsInvolution (g : G) : Prop := g ≠ 1 ∧ g ^ 2 = 1

@[expose] public def IsQuadraticOn
    {G : Type*} [Group G] (A V : Subgroup G) : Prop :=
  ⁅⁅V, A⁆, A⁆ = ⊥

@[expose] public def IsTwoGroup (K : Subgroup G) : Prop := IsPGroup 2 K

@[expose] public def IsCriticalPair
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (a a' : Γ.Vertex) : Prop :=
  Γ.distance a a' =
      sInf {n : ℕ | ∃ d d' : Γ.Vertex,
        Γ.distance d d' = n ∧ Γ.zAt d ≤ Γ.twoCoreAt d'} ∧
    Γ.zAt a ≤ Γ.twoCoreAt a'

@[expose] public noncomputable def CriticalDistance
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2) : ℕ :=
  sInf {n : ℕ | ∃ d d' : Γ.Vertex,
    Γ.distance d d' = n ∧ Γ.zAt d ≤ Γ.twoCoreAt d'}

end CosetGraphContext

public structure CriticalPath
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) where
  a : Γ.Vertex
  a' : Γ.Vertex
  length : ℕ
  length_pos : 0 < length
  critical : CosetGraphContext.IsCriticalPair Γ a a'
  firstStep : Γ.Vertex
  firstStep_adj : Γ.adjacent a firstStep
  endpoint_distance : Γ.distance a a' = length
  path : Fin (length + 1) → Γ.Vertex
  path_start : path 0 = a
  path_end : path ⟨length, Nat.lt_succ_self length⟩ = a'
  path_first : path ⟨1, by omega⟩ = firstStep
  path_adj : ∀ i : Fin length, Γ.adjacent (path i.castSucc) (path i.succ)
  S_le_edge_stabilizers : S ≤ Γ.stabilizer a ⊓ Γ.stabilizer firstStep
  edge_stabilizers_are_P :
    (Γ.stabilizer a = P1 ∧ Γ.stabilizer firstStep = P2) ∨
      (Γ.stabilizer a = P2 ∧ Γ.stabilizer firstStep = P1)

end SectionsFiveToSeven
end Stellmacher
