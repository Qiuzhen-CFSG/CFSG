module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.LocalStructure
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.BinaryPermutationMulAction

/-!
# Source inputs for the S₆ block argument

The marking alone does not identify its action kernel with O₂(L), or say
that its range is internal to the two-core. `ModuleData` retains those
earlier module facts, characteristic two of L, two-perfection, and the
cubic quotient of the actual residual C_L(v). It contains no block or
core-equality conclusion. `SourceData` adds the preceding local and
Fundamental Setup facts used after block recognition. Its L₀ is the
T-conjugate closure from 3.2.1, not the different L₀ of Notation 13.2.1
in the triple-cover case.

`EarlierC113c` records the full normal alternating-block clause: the
internal direct product, the actual natural action on U, both quotient
possibilities, the center clause, and centralization of O₂(L). Normality
inside LT together with shortness is precisely the normal-block
hypothesis of C.1.7; Sylow membership is relative to that same LT.
This is an explicit earlier theorem parameter, not a proof of C.1.13(c).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
3.2.1 and 3.2.11, printed pp.579, 584; C.1.13(c), pp.124–125;
13.2.3–6, 13.3.2–5 and the S₆ paragraph of 13.6.6, pp.926–927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
open Subgroup Theory.GroupTheory A5Module ChapterC
open scoped IsMulCommutative
universe u

variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}

/-- Structural facts about the actual internal A₅ module, before block recognition. -/
structure ModuleData (s : Marking L V) : Prop where
  twoPerfect : IsPPerfect 2 L
  fitting : generalizedFitting L = pCore 2 L
  action_kernel : s.action.ker = pCore 2 L
  V_le_core : V ≤ (pCore 2 L).map L.subtype
  V_central_core : V ≤ centralizer ((pCore 2 L).map L.subtype : Set G)
  residual_quotient_card : Nat.card (Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s))) = 3

/-- The literal L₀ in the Fundamental Setup. -/
def fundamentalClosure (L T : Subgroup G) : Subgroup G := conjugateSpanBy L T

/-- Earlier source assertions needed for the block contradiction, separately
from the applicability bundle `Setup`. No block or desired core equality is assumed. -/
structure SourceData {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}
    (d : Setup κ T s) (M : Subgroup G) : Prop where
  moduleData : ModuleData s
  T_normalizes : (T : Subgroup G) ≤ normalizer (L : Set G)
  M_definition : M = normalizer (fundamentalClosure L (T : Subgroup G) : Set G)
  maximal : IsMaximalTwoLocal M
  characteristic_two : centralizer (pCore 2 M : Set M) ≤ pCore 2 M
  unique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M
  outside_omega : ∃ H : Subgroup G, ¬ H ≤ M ∧
    H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)
  z_outside : ¬ Gv (markedZ s) ≤ M
  normalizer_V : normalizer (V : Set G) ≤ M
  abelian_span : IsMulCommutative (conjugateSpanBy V (Gv (markedZ s)))

/-- The natural action on U itself, as asserted by C.1.13(c), rather
than just on U/C_U(L) from the definition of block type. -/
structure NaturalBlockUModel (A : Type u) [Group A] (n : ℕ) where
  quotientIso : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin n)
  moduleIso : blockU A ≃* Multiplicative (BinaryPermutation.natural (Fin n))
  intertwining : ∀ (a : A) (x : blockU A),
    moduleIso (blockConjugate A a x) =
      BinaryPermutation.naturalMulAction (Fin n)
        (quotientIso (QuotientGroup.mk' (pCore 2 A) a)).val (moduleIso x)

/-- All conclusions of C.1.13(c), with every subgroup embedded in the
same ambient group. The join, trivial intersection and commutation
express the internal direct product Q = U × C_T(L). -/
structure C113cConclusion (L T : Subgroup G) (n : ℕ) : Prop where
  product : (pCore 2 ↥(L ⊔ T)).map (L ⊔ T).subtype =
    (blockU L).map L.subtype ⊔ (T ⊓ centralizer (L : Set G))
  disjoint : Disjoint ((blockU L).map L.subtype) (T ⊓ centralizer (L : Set G))
  commute : ∀ x ∈ (blockU L).map L.subtype,
    ∀ y ∈ T ⊓ centralizer (L : Set G), Commute x y
  natural : Nonempty (NaturalBlockUModel L n)
  three : n = 3 → Nonempty (L ≃* alternatingGroup (Fin 4))
  five : n = 5 → Nonempty ((L ⧸ blockU L) ≃* alternatingGroup (Fin 5)) ∨
    (Nonempty ((L ⧸ blockU L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      Nat.card (center L) = 2)
  centralizes_core : (pCore 2 ↥(L ⊔ T)).map (L ⊔ T).subtype ≤
    centralizer ((pCore 2 L).map L.subtype : Set G)

/-- The universal full C.1.13(c) source contract. The shortness in
`IsAlternatingBlock` and the displayed relative normality supply a
normal block of LT; the Sylow witness also lives in LT. -/
def EarlierC113c : Prop :=
  ∀ (H : Type u) [Group H] [Finite H] (A S : Subgroup H) (n : ℕ),
    (A.subgroupOf (A ⊔ S)).Normal →
    (∃ P : Sylow 2 ↥(A ⊔ S), (P : Subgroup ↥(A ⊔ S)).map (A ⊔ S).subtype = S) →
    IsAlternatingBlock A n → (n = 3 ∨ n = 5) → C113cConclusion A S n

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
