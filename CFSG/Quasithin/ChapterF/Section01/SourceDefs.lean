module

public import CFSG.Quasithin.ClassicalModels
public import BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.PGroupCore

/-!
# Source hypotheses for §F.1

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed
pp. 259–262, Hypothesis F.1.1 and the verification of Definition F.1.7 in
Proposition F.1.9. These declarations are separate from the legacy interfaces
in `ChapterF.Defs`. In particular none of the conclusions of F.1.3 is an
assumption of `Source.HypothesisF11`.

The quotient alternatives refer to concrete matrix groups (and the dihedral
group of order ten). Unitary parameters are fixed-field orders. Sylow data
are actual Sylow subgroups, and characteristic two uses the intrinsic F*.
Products are represented by subgroup joins; the source normalizing conditions
are what make these joins equal to the corresponding set products.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Source

open scoped Pointwise

universe u v

/-- The special, rather than projective special, unitary alternative. -/
def IsSU (H : Type u) [Group H] (n q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (J : BenderSuzuki.MatrixGroups.HermitianForm n F),
    Nat.card F = q ^ 2 ∧ (∀ x, J.conj x = x ^ q) ∧
      Nonempty (H ≃* J.specialSubgroup)

/-- The actual quotient alternatives in F.1.1(c), including the small parameters.
`SuzukiMatrixGroup m` is defined over the field of order `2^(2*m+1)`.
There is no arbitrary model carrier or unattached family tag. -/
inductive IsRankOneModel (H : Type u) [Group H] : Prop
  | linear (n : ℕ) (positive : 0 < n) (iso : ClassicalGroup.IsPSL H 2 (2 ^ n))
  | suzuki (m : ℕ)
      (iso : Nonempty (H ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | projective_unitary (n : ℕ) (positive : 0 < n)
      (iso : ClassicalGroup.IsPSU H 3 (2 ^ n))
  | special_unitary (n : ℕ) (positive : 0 < n) (iso : IsSU H 3 (2 ^ n))
  | dihedral (iso : Nonempty (H ≃* DihedralGroup 5))

variable {G : Type u} [Group G]

/-- The other member of a pair. -/
def other (i : Fin 2) : Fin 2 := 1 - i

/-- A subgroup's intrinsic 2-core, embedded in the ambient group. -/
def twoCore (H : Subgroup G) : Subgroup G := (pCore 2 H).map H.subtype

/-- The normalizer `N_L(S ∩ L)` defining the local Borel. -/
def borel (L S : Subgroup G) : Subgroup G :=
  L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)

/-- The group `B₁ B₂ S` of F.1.3. -/
def commonBorel (L : Fin 2 → Subgroup G) (S : Subgroup G) : Subgroup G :=
  borel (L 0) S ⊔ borel (L 1) S ⊔ S

/-- The source group `G₀ = ⟨L₁,L₂,S⟩`; no finiteness of G₀ is assumed. -/
def generated (L : Fin 2 → Subgroup G) (S : Subgroup G) : Subgroup G :=
  L 0 ⊔ L 1 ⊔ S

/-- The local factor `Lᵢ S Bⱼ` in F.1.1(f). -/
def parabolic (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Fin 2) : Subgroup G :=
  L i ⊔ S ⊔ borel (L (other i)) S

/-- Exactly the six conditions (a)–(f) of Hypothesis F.1.1.
The results about maximality, solvability, intersection and faithfulness must
be proved from this structure, rather than supplied by its callers. -/
structure HypothesisF11 (L : Fin 2 → Subgroup G) (S : Subgroup G) : Prop where
  finite_S : Finite S
  S_isP : IsPGroup 2 S
  S_normalizes : ∀ i, S ≤ Subgroup.normalizer (L i : Set G)
  sylow : ∀ i, ∃ T : Sylow 2 (L i), (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i
  quotient : ∀ i, IsRankOneModel ((L i) ⧸ pCore 2 (L i))
  cross : ∀ i, borel (L (other i)) S ≤ Subgroup.normalizer (L i : Set G)
  twoCore_free : pCore 2 (generated L S) = ⊥
  characteristic_two : ∀ i,
    Theory.GroupTheory.generalizedFitting (parabolic L S i) = pCore 2 (parabolic L S i)

/-- Intrinsic rank-one Sylow-normalizer facts to prove for the concrete models.
This is a theorem output contract, not an assumption in F.1.1. -/
structure RankOneSylowFacts {H : Type u} [Group H] (T : Sylow 2 H) : Prop where
  proper : Subgroup.normalizer (T : Set H) < ⊤
  unique_maximal : ∀ M : Subgroup H, (T : Subgroup H) ≤ M → M < ⊤ →
    M ≤ Subgroup.normalizer (T : Set H)
  twoCore_eq : twoCore (Subgroup.normalizer (T : Set H)) = (T : Subgroup H)
  solvable : Group.IsSolvable (Subgroup.normalizer (T : Set H))
  abelian_odd_complement : ∃ D : Subgroup H,
    D ≤ Subgroup.normalizer (T : Set H) ∧ Nat.Coprime 2 (Nat.card D) ∧
    IsMulCommutative D ∧ Disjoint (T : Subgroup H) D ∧
    (T : Subgroup H) ⊔ D = Subgroup.normalizer (T : Set H)

/-- The local conclusions needed from rank-one group theory, not hypotheses
of F.1.1. Maximality is restricted to *proper* overgroups in L. -/
structure RankOneBorelFacts (L S : Subgroup G) : Prop where
  proper : borel L S < L
  unique_maximal : ∀ M : Subgroup G, S ⊓ L ≤ M → M < L → M ≤ borel L S
  twoCore_eq : twoCore (borel L S) = S ⊓ L
  solvable : Group.IsSolvable (borel L S)
  abelian_odd_complement : ∃ D : Subgroup G,
    D ≤ borel L S ∧ Nat.Coprime 2 (Nat.card D) ∧ IsMulCommutative D ∧
    Disjoint (S ⊓ L) D ∧ (S ⊓ L) ⊔ D = borel L S

/-- The local data used to verify conditions (i)–(iii) of Green Book Hypothesis A, in the
prime-two form verified on printed p.261 of Aschbacher–Smith. `Pstar` is
normal in P, has the same 2-core, supplements B, and has a rank-one quotient
with Borel the Sylow normalizer. This is the data described by the F.1.9 proof;
a comparison with the original DGS85 p.94 statement remains necessary before
using it as the input to DGS recognition. -/
structure LocalRankOneData (P B : Subgroup G) where
  finite_P : Finite P
  Pstar : Subgroup G
  Pstar_le : Pstar ≤ P
  normal : (Pstar.subgroupOf P).Normal
  same_core : twoCore Pstar = twoCore P
  supplement : Pstar ⊔ B = P
  characteristic_two : Theory.GroupTheory.generalizedFitting P = pCore 2 P
  sylow : Sylow 2 Pstar
  borel_eq : Pstar ⊓ B = Pstar ⊓
    Subgroup.normalizer (((sylow : Subgroup Pstar).map Pstar.subtype : Subgroup G) : Set G)
  quotient : IsRankOneModel (Pstar ⧸ pCore 2 Pstar)

/-- A faithful generating triple equipped with the local data verified in F.1.9.
The kernel condition concerns actual normal subgroups of the completion.
Identification with Definition F.1.7 awaits the comparison with DGS85 p.94
noted above; this predicate alone is not yet an audited DGS input. -/
structure LocallyRankOneTriple (P : Fin 2 → Subgroup G) (B : Subgroup G) : Prop where
  generate : P 0 ⊔ P 1 = ⊤
  intersection : P 0 ⊓ P 1 = B
  faithful : ∀ N : Subgroup G, N.Normal → N ≤ B → N = ⊥
  local_data : ∀ i, Nonempty (LocalRankOneData (P i) B)

end CFSG.Quasithin.ChapterF.Source
