module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalCartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.PointResidual
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Literal subgroups in the chosen-natural closure argument

These data name the original quotient flag, Cartan subgroup and selected
outside subgroup. All derived groups are definitions: Lᵢ is the solvable
residual of N_L(Vᵢ), Rᵢ is O₂(LᵢT), G₁ is N_G(V₁), and K is the G₁-closure
of L₁. In particular G₁ is not the earlier C_G(V₁).

The quotient centralizer is the kernel of the actual normalizer action on
K/O₂(K), embedded back into G. Its normalization, and hence that of Y,
follows without an ambient-normality assumption on K.

The data contain no source conclusions. Constructing the field flag and
proving the preceding geometry remain with LocalGeometry and ShadowReduction.
Source: Aschbacher--Smith, 11.1 and 11.4--11.5, printed pp.760,777--784.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Choices in the original marked quotient. This only names data; it does
not assert that arbitrary binary subspaces form the source field flag. -/
structure Geometry (D : ChosenModule T L V) where
  input : D.NonbinaryNaturalInput
  point : Submodule (ZMod 2) D.chosenCentralQuotient
  plane : Submodule (ZMod 2) D.chosenCentralQuotient
  threeSpace : Submodule (ZMod 2) D.chosenCentralQuotient
  X : Subgroup G
  z : G
  H : Subgroup G

/-- The literal quotient action, defined on N_G(K) without requiring K normal in G. -/
def coreQuotientAction (K : Subgroup G) :
    normalizer (K : Set G) →* MulAut (K ⧸ pCore 2 K) :=
  (quotientAut (pCore 2 K)).comp K.normalizerMonoidHom

omit [Finite G] in
/-- The quotient action uses the same representatives as the actual normalizer action. -/
theorem coreQuotientAction_apply_mk (K : Subgroup G)
    (g : normalizer (K : Set G)) (k : K) :
    coreQuotientAction K g (QuotientGroup.mk' (pCore 2 K) k) =
      QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom g k) :=
  quotientAut_apply_mk (pCore 2 K) (K.normalizerMonoidHom g) k

/-- C_G(K/O₂(K)), with setwise preservation of K included in its definition. -/
def coreQuotientCentralizer (K : Subgroup G) : Subgroup G :=
  (coreQuotientAction K).ker.map (normalizer (K : Set G)).subtype

omit [Finite G] in
/-- The quotient kernel is normalized by the full normalizer of K. -/
theorem normalizer_normalizes_coreQuotientCentralizer (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (coreQuotientCentralizer K : Set G) := by
  apply le_normalizer_iff.mpr
  rintro g hg _ ⟨x, hx, rfl⟩
  refine ⟨(⟨g, hg⟩ : normalizer (K : Set G)) * x * ⟨g, hg⟩⁻¹, ?_, rfl⟩
  exact (inferInstance : (coreQuotientAction K).ker.Normal).conj_mem x hx ⟨g, hg⟩

namespace Geometry
variable {D : ChosenModule T L V} (E : Geometry D)

def V₁ : Subgroup G := D.centralQuotientPreimage E.point
def V₂ : Subgroup G := D.centralQuotientPreimage E.plane
def V₃ : Subgroup G := D.centralQuotientPreimage E.threeSpace

def M (_E : Geometry D) : Subgroup G := normalizer (L : Set G)
def G₁ : Subgroup G := normalizer (E.V₁ : Set G)
def M₁ : Subgroup G := E.M ⊓ E.G₁

def L₁ : Subgroup G := residualIn (L ⊓ E.G₁)
def L₂ : Subgroup G := residualIn (L ⊓ normalizer (E.V₂ : Set G))
def R₁ : Subgroup G := (E.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
def R₂ : Subgroup G := (E.L₂ ⊔ (T : Subgroup G)).pCoreIn 2

def K : Subgroup G := conjugateSpanBy E.L₁ E.G₁
def Kz : Subgroup G := conjugateSpanBy E.L₁ (centralizer ({E.z} : Set G))
def U : Subgroup G := conjugateSpanBy E.V₃ E.G₁
def W : Subgroup G := conjugateSpanBy V E.G₁

def Y : Subgroup G := centralizer (E.V₁ : Set G) ⊓ coreQuotientCentralizer E.K

instance point_normal : (E.V₁.subgroupOf E.G₁).Normal := by
  change (E.V₁.subgroupOf (normalizer (E.V₁ : Set G))).Normal
  infer_instance

/-- The final quotient G₁/V₁, separate from the original chosen fixed-space quotient. -/
abbrev Tilde := E.G₁ ⧸ E.V₁.subgroupOf E.G₁

/-- Images in the actual final quotient. -/
def tilde (A : Subgroup G) : Subgroup E.Tilde :=
  (A.subgroupOf E.G₁).map (QuotientGroup.mk' (E.V₁.subgroupOf E.G₁))

theorem V₁_le : E.V₁ ≤ V := D.centralQuotientPreimage_le E.point

theorem L₁_le : E.L₁ ≤ L := (residualIn_le _).trans inf_le_left

theorem G₁_normalizes_K : E.G₁ ≤ normalizer (E.K : Set G) :=
  le_normalizer_conjugateSpanBy _ _

theorem K_le_G₁ : E.K ≤ E.G₁ :=
  conjugateSpanBy_le_self ((residualIn_le _).trans inf_le_right)

theorem K_relative_normal : (E.K.subgroupOf E.G₁).Normal :=
  (normal_subgroupOf_iff_le_normalizer E.K_le_G₁).mpr E.G₁_normalizes_K

theorem Y_le_G₁ : E.Y ≤ E.G₁ :=
  inf_le_left.trans (centralizer_le_normalizer _)

/-- The geometric inclusion X≤G₁ suffices for the normalization in 11.5.6(1). -/
theorem X_normalizes_Y (hX : E.X ≤ E.G₁) : E.X ≤ normalizer (E.Y : Set G) :=
  (le_inf (hX.trans (normalizer_le_normalizer_centralizer E.V₁))
    ((hX.trans E.G₁_normalizes_K).trans
      (normalizer_normalizes_coreQuotientCentralizer E.K))).trans
    inf_normalizer_le_normalizer_inf

/-- The actual Chapter12 Cartan application, now with normalization and
membership of Y constructed. Cartan ranks and disjointness remain geometric inputs. -/
theorem cartan_coprime (hp : E.point ≠ ⊥) (hX : E.X ≤ E.G₁)
    (hr : ∀ p : ℕ, p.Prime → p ∣ 2 ^ E.input.field.degree - 1 → 2 ≤ primeRank p E.X)
    (hd : Disjoint E.X E.Y) :
    Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1) := by
  exact D.centralQuotientPreimage_cartan_coprime_of_many E.input E.point hp E.X E.Y
    hX E.Y_le_G₁ hr (E.X_normalizes_Y hX) hd

/-- The literal source identification needed to use the point-closure
intersection theorem; the solvable residual is not replaced by O². -/
theorem pointClosure_eq_K
    (hres : pointResidual L E.z = E.L₁) (hK : E.Kz = E.K) :
    pointClosure L E.z = E.K := by
  simpa only [pointClosure, hres, Kz] using hK

end Geometry
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
