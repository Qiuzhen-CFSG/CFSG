module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Residuals
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Seeds
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Normalizer
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree

/-!
# Applications of the corrected small-action reductions

The actual wreath quotient of the original H supplies M ∩ K = O₂(K),
completing 15.2.21(2) from PlaneUniquenessPreceding and K = Kc. The corrected
two-perfect seed and conjugate-pair normalizer calculation also consume
the original binary component's commutator bound on Y₁ = O^{3′}(NI).

The split, the seed's S₃ quotient, and the same-family commutators remain
explicit local geometry inputs in that application. This is checked progress
toward 15.2.22, not its complete source proof. Constructing these inputs,
and the L₄(2) split exclusion of 15.2.21(3), stays with this source owner.
Earlier 15.2.1--14 premises are produced by qt-e-152-plane-geometry and
qt-e-152-small-parabolic; final discharge remains with qt-e-152-plane-uniqueness.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.21--23, printed pp.1114--1116; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- 15.2.21(2) on the original chosen plane. The earlier intersection
identity is discharged by the actual wreath quotient of H. -/
theorem source_15_2_21_2_from_preceding
    (hK : smallActionK H = smallActionKc H Mc) :
    IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)) := by
  apply source_15_2_21_2 d hK
  simpa only [inf_comm] using
    PlaneUniquenessPreceding.LinearThree.residual_intersection_eq_core d

/-- The local 15.2.22 exclusion, with the noncontainment in MI derived
from the corrected two-perfect seed and the three-prime centralizer.
Construction of the split and the same-family commutators remains source work. -/
theorem commutator_exclusion_of_pair
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (split : SmallActionSplit (T : Subgroup G) (smallActionS T ZS) (smallActionK H))
    {Y : Subgroup G} (seed : Seed M I (smallActionS T ZS) Y)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (hYY : ⁅Y, Y.map (MulAut.conj split.t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj split.t).toMonoidHom)
    (hKK : ⁅split.K₁, split.K₂⁆ ≤ split.K₁ ⊓ split.K₂) :
    ¬ ⁅Y, split.K₂⁆ ≤ Y ⊓ split.K₂ :=
  not_commutator_le_inf_of_conjugate_pair d hI hfit split
    (seed.le_NI.trans inf_le_right) (seed.not_le_MI d hC) seed.normalized hYY hKK

/-- Apply the repaired local exclusion to the literal binary component and
Y₁ = O^{3′}(NI). The component calculation supplies the forbidden commutator;
the original H quotient supplies the three-prime centralizer.
The marked split, S₃ quotient and conjugate-factor geometry remain explicit. -/
theorem binary_component_false_of_pair
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X 1 F)
    (split : SmallActionSplit (T : Subgroup G) (smallActionS T ZS) (smallActionK H))
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃*
          PlaneUniquenessPreceding.LinearThree.BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤)
    (hK₂ : IsPPerfect 2 split.K₂) (hc : ⁅X, split.K₂⁆ ≤ X.pCoreIn 2)
    (hindex : Nat.Coprime 3 ((M ⊓ X).subgroupOf (M ⊓ I)).index)
    (hK : smallActionK H = smallActionKc H Mc)
    (hquot : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      Nonempty (((Y ⊔ smallActionS T ZS : Subgroup G) ⧸
        pCore 2 (Y ⊔ smallActionS T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hYY : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      ⁅Y, Y.map (MulAut.conj split.t).toMonoidHom⁆ ≤
        Y ⊓ Y.map (MulAut.conj split.t).toMonoidHom)
    (hKK : ⁅split.K₁, split.K₂⁆ ≤ split.K₁ ⊓ split.K₂) : False := by
  obtain ⟨⟨hle,hp,hn⟩,hcomm⟩ := b.binary_smallActions_data d hI hmove f hker hfull
    split.S_normalizes_K₂ hK₂ hc hindex
  exact commutator_exclusion_of_pair d hI hfit split ⟨hle,hp,hn,hquot⟩
    (source_15_2_21_2_from_preceding d hK) hYY hKK hcomm
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
