module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Preparation
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Preparation
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface
public import Theory.GroupTheory.PResidual.PrimeToIntersection

/-!
# Literal subgroups in the terminal binary-linear branch

We keep M₁ = C_X(ZS), U = [⟨ZS^X⟩,X], K_I = O^{3′}(M₁), and
Q_I = O₂(KS) in the original ambient group. The binary branch retains
the actual C.2.3 input and the full positive-rank flag parabolic in the
star quotient. It does not identify that quotient with X/O₂(X).

If the later component argument proves X = O^{3′}(I), restriction of
prime-to-three residuals identifies K_I with O^{3′}(C_G(ZS)). Since T
normalizes ZS, this proves T-invariance of K_I without assuming that T
normalizes I or X. The component-residual identity remains an explicit
input; no terminal module classification or contradiction is asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.23, printed pp.1116--1117; refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G]

def M1 (X ZS : Subgroup G) : Subgroup G := X ⊓ centralizer (ZS : Set G)

def U (X ZS : Subgroup G) : Subgroup G := ⁅conjugateSpanBy ZS X, X⁆

def KI (X ZS : Subgroup G) : Subgroup G :=
  (primeToResidual 3 (M1 X ZS)).map (M1 X ZS).subtype

def KS (H : Subgroup G) (T : Sylow 2 G) (ZS : Subgroup G) : Subgroup G :=
  (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS

def QI (H : Subgroup G) (T : Sylow 2 G) (ZS : Subgroup G) : Subgroup G :=
  (KS H T ZS).pCoreIn 2

/-- The literal O₂,₃ subgroup in its original ambient group. -/
def twoThreeIn (A : Subgroup G) : Subgroup G :=
  ((pCore 3 (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A))).map A.subtype

/-- The characteristic subgroup used to exclude the exterior-five row. -/
def cubicResidual (X ZS : Subgroup G) : Subgroup G :=
  (primeToResidual 3 (twoThreeIn (KI X ZS))).map (twoThreeIn (KI X ZS)).subtype

/-- The literal C.2.7(3)(h) branch, with its source input and marked flag.
This is an input contract, not an assertion that this branch occurs. -/
structure BinaryBranch (M I X : Subgroup G) (n : ℕ) : Prop where
  source : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X
  degree : n = 4 ∨ n = 5
  parabolic : IsBinaryPositiveRankParabolic
    ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X)) n

variable [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

/-- The source centralizer stays in the literal partner intersection. -/
theorem M1_le_partner_intersection (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hXI : X ≤ I) :
    M1 X ZS ≤ Mc ⊓ I :=
  le_inf (inf_le_right.trans ((d.centralizer_le_intersection hI).trans inf_le_left))
    (inf_le_left.trans hXI)

/-- Once KS lies in the component, its original action puts it in M₁. -/
theorem KS_le_M1 (d : PlaneUniquenessPreceding hsource H ZS)
    (hKSX : KS H T ZS ≤ X) : KS H T ZS ≤ M1 X ZS :=
  le_inf hKSX (sup_le d.residual_centralizes inf_le_right)

/-- The residual comparison uses C_G(ZS) ≤ I, not T-normality of I. -/
theorem KI_eq_global_centralizer_residual (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I)
    (hX : X = (primeToResidual 3 I).map I.subtype) :
    KI X ZS = (primeToResidual 3 (centralizer (ZS : Set G))).map
      (centralizer (ZS : Set G)).subtype := by
  unfold KI M1
  rw [hX, embedded_primeToResidual_intersection,
    inf_eq_right.mpr ((d.centralizer_le_intersection hI).trans inf_le_right)]

/-- T acts on the actual residual K_I in the exterior-five argument. -/
theorem KI_normalized (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I)
    (hX : X = (primeToResidual 3 I).map I.subtype) :
    (T : Subgroup G) ≤ normalizer (KI X ZS : Set G) := by
  rw [KI_eq_global_centralizer_residual d hI hX]
  have hTH : (T : Subgroup G) ≤ H := by
    rw [← d.residual_sup_sylow]
    exact le_sup_right
  exact hTH.trans (d.geometry.normalized.trans
    ((normalizer_le_normalizer_centralizer _).trans
      (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))))

/-- T-invariance of O^{3′}(O₂,₃(K_I)) follows on the original subgroup maps.
Its nontrivial cubic image and rank one still require the exterior model. -/
theorem cubicResidual_normalized (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I)
    (hX : X = (primeToResidual 3 I).map I.subtype) :
    (T : Subgroup G) ≤ normalizer (cubicResidual X ZS : Set G) := by
  let A := KI X ZS
  let C := (pCore 3 (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A))
  let : C.Characteristic := Characteristic.comap_quotient_mk inferInstance
  have hn : (T : Subgroup G) ≤ normalizer (twoThreeIn A : Set G) :=
    (KI_normalized d hI hX).trans (normalizer_le_normalizer_characteristic_image A C)
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
