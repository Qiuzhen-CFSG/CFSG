module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.GroupTheory.Frattini

/-!
# The complete target of the outside-overgroup lemma

These are the twelve literal conclusions of Aschbacher–Smith 15.3.11,
combined manuscript (1 March 2004), pp.1123–1124. They retain the actual
centralizer quotient I*, the two-core Frattini preimage, O^{3′}, normality
inside the stated overgroup, and characteristic-normalizer generation
inside I. The group of order 27 is specified intrinsically as extraspecial
of exponent three; the other quotient identifications are multiplicative
equivalences to concrete groups.

`Conclusions` is a proof target. It is not a standing-hypothesis certificate
and no projection from an assumed inhabitant is offered as a source theorem.
The two structural alternatives can be developed independently of the
Thompson argument and combined by the outside-structure assembly owner.
-/

@[expose] public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G]

/-- The second, uniqueness-dependent choice of 15.3.10. -/
def SecondChoice (d : CharacteristicTwo.LocalData G) : Prop :=
  Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M ∧
    d.Yplus = twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G))

/-- `O_{2,Φ}(H)` formed inside H, so that its quotient is the literal
quotient by the preimage of the Frattini subgroup of H/O₂(H). -/
def coreFrattiniSubgroup (H : Type*) [Group H] : Subgroup H :=
  (frattini (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))

instance coreFrattiniSubgroup_normal (H : Type*) [Group H] :
    (coreFrattiniSubgroup H).Normal := inferInstanceAs
      ((frattini (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))).Normal

/-- The intrinsic description of the two permitted three-group quotients.
The extraspecial branch includes both order 27 and exponent three. -/
def CubicQuotient (H : Type*) [Group H] : Prop :=
  Nonempty (H ≃* Multiplicative (Fin 2 → ZMod 3)) ∨
    (IsExtraspecial 3 H ∧ Nat.card H = 27 ∧ ∀ x : H, x ^ 3 = 1)

/-- The full first alternative of 15.3.11(5). -/
def RankTwoCase (d : CharacteristicTwo.LocalData G) (I : Subgroup G) : Prop :=
  CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus) ∧
    Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ coreFrattiniSubgroup ↥(d.Yplus ⊔ d.S)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
    d.R = (d.Y ⊔ d.S).pCoreIn 2 ∧
    (d.R.subgroupOf (d.Y ⊔ (d.T : Subgroup G))).Normal ∧
    d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) ∧
    d.R = (I ⊓ normalizer (d.R : Set G)).pCoreIn 2 ∧
    (∃ P : Sylow 2 (localSpan d.R (d.MI I)),
      (P : Subgroup _).map (localSpan d.R (d.MI I)).subtype = d.R) ∧
    d.R.characteristicNormalizerClosure ≤ d.M

/-- The full second alternative of 15.3.11(5), with O^{3′}, not O₃. -/
def RankOneCase (d : CharacteristicTwo.LocalData G) (I : Subgroup G) : Prop :=
  SecondChoice d ∧
    Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) ≃* Equiv.Perm (Fin 3)) ∧
    d.Yplus = (primeToResidual 3 (d.MI I)).map (d.MI I).subtype ∧
    d.R = d.S ⊓ centralizer (d.V₂ : Set G)

/-- The complete alternative of (10). Characteristic-normalizer generation
is formed inside I, then embedded in G; it is not a centralizer. -/
def ThompsonAlternative (d : CharacteristicTwo.LocalData G) (I : Subgroup G) : Prop :=
  (ChapterB.baumann d.R = ChapterB.baumann d.S ∧
    ((ChapterB.baumann d.S).subgroupOf I).characteristicNormalizerClosure.map I.subtype ≤ d.MI I) ∨
  (d.Yplus = ⁅d.Yplus, elementaryAbelianMaxJ d.S⁆ ∧
    d.starImage I d.Yplus ≤ d.starImage I (elementaryAbelianMaxJ I))

/-- The twelve conclusions of 15.3.11, as a target only. Constructing this
record requires proofs of all fields. No theorem is obtained by assuming it. -/
structure Conclusions (d : CharacteristicTwo.LocalData G) (I : Subgroup G) : Prop where
  sylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S
  centralizer_le : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I
  second_choice : SecondChoice d →
    d.Yplus = twoResidualAmbient (d.Y ⊓ I) ∧
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M ∧
      normalizer (d.Yplus : Set G) ≤ d.M
  normalizer_eq : I ⊓ normalizer (d.Yplus : Set G) = d.MI I
  local_structure : RankTwoCase d I ∨ RankOneCase d I
  theta_eq : d.Yplus = theta (d.MI I)
  generalized_fitting : Theory.GroupTheory.generalizedFitting (d.MI I) = pCore 2 (d.MI I)
  odd_core : pPrimeCore 2 I = ⊥
  action_normalizer : normalizer (d.starImage I d.Yplus : Set (d.Star I)) =
      d.starImage I d.M ∧ d.starImage I d.M < ⊤ ∧ d.starImage I d.Yplus ≠ ⊥
  thompson_alternative : ThompsonAlternative d I
  thompson_outside : ¬ d.starImage I (elementaryAbelianMaxJ I) ≤ d.starImage I d.M
  characteristic_exclusion : ∀ L : Subgroup G, L ≤ I →
    ⁅d.V, twoResidualAmbient (d.Y ⊓ L)⁆ ≠ ⊥ → ¬ L ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (L ⊔ d.S)).Normal

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure

end
