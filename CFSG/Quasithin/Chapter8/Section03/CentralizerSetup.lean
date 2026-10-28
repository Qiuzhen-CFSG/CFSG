module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The literal centralizer constructions in §8.3

The notation takes the original L₀, Sylow subgroup T and element z.
In particular X is the embedded two-residual of C_{L₀}(z), not its
two-core, and K_z is the actual normal closure of X in C_G(z).
The star map is the quotient of K_z T by its two-core.

This is notation, not the Fundamental Setup or an assertion of the
classification of C_G(z). The elementary containments and relative
normality proved here allow independent local calculations to use the
same ambient subgroups and quotient maps.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), §8.3,
printed pp.724--726, PDF pp.741--743.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter8.Section03

open Subgroup

/-- The original data needed to define the centralizer subgroups. The
source FSU and tensor-action hypotheses are additional mathematical inputs. -/
structure CentralizerSetup (G : Type*) [Group G] where
  T : Sylow 2 G
  L₀ : Subgroup G
  z : G

namespace CentralizerSetup

variable {G : Type*} [Group G] (D : CentralizerSetup G)

def M : Subgroup G := normalizer (D.L₀ : Set G)
def Gz : Subgroup G := centralizer ({D.z} : Set G)
def Mz : Subgroup G := D.M ⊓ D.Gz

/-- O²(C_{L₀}(z)), embedded in G. -/
def X : Subgroup G :=
  (pResidual 2 (D.L₀ ⊓ D.Gz : Subgroup G)).map (D.L₀ ⊓ D.Gz).subtype

def XT : Subgroup G := D.X ⊔ (D.T : Subgroup G)
def S : Subgroup G := D.XT.pCoreIn 2

/-- The genuine normal closure ⟨X^{G_z}⟩. -/
def Kz : Subgroup G := conjugateSpanBy D.X D.Gz
def KzT : Subgroup G := D.Kz ⊔ (D.T : Subgroup G)
def Qz : Subgroup G := D.KzT.pCoreIn 2

abbrev Star := D.KzT ⧸ pCore 2 D.KzT

/-- Restrict to K_z T, then apply its actual two-core quotient map. -/
def star (A : Subgroup G) : Subgroup D.Star :=
  (A.subgroupOf D.KzT).map (QuotientGroup.mk' (pCore 2 D.KzT))

theorem X_le : D.X ≤ D.L₀ ⊓ D.Gz := map_subtype_le _

theorem X_le_Kz : D.X ≤ D.Kz := le_conjugateSpanBy _ _

theorem Kz_le_Gz : D.Kz ≤ D.Gz :=
  conjugateSpanBy_le_self (D.X_le.trans inf_le_right)

/-- Only normality inside the element centralizer is asserted. -/
theorem Kz_normal : (D.Kz.subgroupOf D.Gz).Normal :=
  (normal_subgroupOf_iff_le_normalizer D.Kz_le_Gz).mpr
    (le_normalizer_conjugateSpanBy _ _)

theorem Kz_eq_X_of_normal (hX : (D.X.subgroupOf D.Gz).Normal) : D.Kz = D.X := by
  have hnorm := (normal_subgroupOf_iff_le_normalizer
    (D.X_le.trans inf_le_right)).mp hX
  exact le_antisymm (conjugateSpanBy_le le_rfl hnorm) D.X_le_Kz

theorem XT_le_KzT : D.XT ≤ D.KzT := sup_le_sup_right D.X_le_Kz _

theorem KzT_le_Gz (hT : (D.T : Subgroup G) ≤ D.Gz) : D.KzT ≤ D.Gz :=
  sup_le D.Kz_le_Gz hT

/-- The two-core of XT is contained in the original Sylow subgroup T. -/
theorem S_le_T : D.S ≤ (D.T : Subgroup G) := by
  have hT : (D.T : Subgroup G) ≤ D.XT := le_sup_right
  have h := pCoreIn_le_sylow D.XT (D.T.subtype hT)
  simpa only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hT] using h

end CentralizerSetup

end CFSG.Quasithin.Chapter8.Section03
