module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Preparation
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Quotient
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Earlier source premises for selecting the parabolic

These are explicit, universally quantified theorem inputs, not axioms or a
certificate of Proposition 8.2.2. The witness premise is exactly existence
in E.2.9's family. E.2.9(2), E.2.11(3,5), E.2.13(5,6), and the center
conclusion established in the proof of E.2.14(2) remain with the existing
producers `qt-e02-witnesses`, `qt-e02-module-bounds`, and
`qt-e02-ti-refinement`, assembled by `qt-e-02`. Each uses the literal
normal-core quotient and the source's right conjugation.

The last three premises are just Sylow normalizers and center orders in
actual dihedral, PSL₂ and Suzuki groups. No simplicity, full order table,
representation recognition, or Sp₄/derived-group identification is assumed.
Source: Aschbacher–Smith, combined manuscript, E.2.9–14, pp.221–228,
and Proposition 8.2.2, pp.714–715.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open Subgroup ChapterE Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G]

/-- The precise portions of earlier E.2 used by selection. -/
structure SelectionSources [Finite G] (K : GroupClass) : Prop where
  e29 : ∀ H T M V : Subgroup G, HypothesisE28 K H T M V →
    ∃ I k, Family H T M V I k
  e292 : ∀ {H T M V I : Subgroup G} {k : ℕ}, HypothesisE28 K H T M V →
    Family H T M V I k → generalizedFitting H = pCore 2 H →
    generalizedFitting I = pCore 2 I
  e2115 : ∀ {H T M V I : Subgroup G} {k : ℕ}, HypothesisE28 K H T M V →
    Family H T M V I k → localCore M I = pCore 2 I
  e2113 : ∀ {H T M V I : Subgroup G} {k : ℕ}, HypothesisE28 K H T M V →
    Family H T M V I k →
    starImage M I M ≤ normalizer (starImage M I T : Set (Star M I))
  e2135 : ∀ {H T M V I : Subgroup G} [IsElementaryAbelian 2 V] {k : ℕ},
    HypothesisE28 K H T M V → generalizedFitting H = pCore 2 H →
    Family H T M V I k → ∀ i : I,
    V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I →
    V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = ⊥ →
    quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V H).subtype) ≤ 1
  e2136 : ∀ {H T M V I : Subgroup G} {k : ℕ}, HypothesisE28 K H T M V →
    generalizedFitting H = pCore 2 H → Family H T M V I k →
    (∀ i : I, (V.subgroupOf I).map (MulAut.conj i⁻¹).toMonoidHom ≤ T.subgroupOf I →
      (V.subgroupOf I).map (MulAut.conj i⁻¹).toMonoidHom ≤ centralizer (V.subgroupOf I : Set I)) →
    ∀ n : ℕ, 0 < n → ¬ Nonempty (Star M I ≃* Sp (BinaryGaloisField n))
  e2142_center : ∀ {H T M V I : Subgroup G} {k : ℕ}, HypothesisE28 K H T M V →
    generalizedFitting H = pCore 2 H → Family H T M V I k →
    (∀ x ∈ H ⊓ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V) → ∀ i : I,
    V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I →
    V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≠ ⊥ →
    starImage M I V = embeddedCenter (starImage M I T)

/-- Only the concrete model facts used to mark the quotient. -/
structure SelectionModelSources : Prop where
  dihedral : ∀ p a : ℕ, p.Prime → Odd p → 0 < a →
    ∀ S : Sylow 2 (DihedralGroup (p ^ a)),
      normalizer (S : Set (DihedralGroup (p ^ a))) = (S : Subgroup _) ∧
      Nat.card (center S) = 2
  psl2 : ∀ k : ℕ, 1 < k → ∀ S : Sylow 2 (PSL2 (BinaryGaloisField k)),
    (S : Subgroup _) ≤ PBorel (BinaryGaloisField k) →
    PBorel (BinaryGaloisField k) = normalizer (S : Set _) ∧ Nat.card (center S) = 2 ^ k
  suzuki : ∀ m : ℕ, 0 < m → ∀ S : Sylow 2 (SuzukiMatrixGroup m),
    (S : Subgroup _) ≤ SuzukiBorelSubgroup m →
    SuzukiBorelSubgroup m = normalizer (S : Set _) ∧ Nat.card (center S) = 2 ^ (2 * m + 1)

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
