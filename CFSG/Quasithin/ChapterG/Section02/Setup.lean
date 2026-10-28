module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.ElementaryAbelian.Basic

/-!
# The literal local data of G.2

The data retain the two ambient subgroups L and H and their common
Sylow two-subgroup T. The point stabilizer uses the two-residual O²,
not the two-core O₂. Irreducibility is expressed on the interval [V₁,V]
of invariant subgroups, which is the subgroup formulation of the binary
module V/V₁. The hypothesis contains no almost-special conclusion.

Conjugation is right conjugation. Stars are images in LT/O₂(LT), and
tildes are images in N_G(V₁)/V₁; the two quotient maps are kept distinct.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis G.2.1, printed p.332, PDF p.343.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterG.Section02
variable (G : Type*) [Group G]

/-- The five original ambient subgroups in Hypothesis G.2.1. -/
structure Setup where
  V : Subgroup G
  V₁ : Subgroup G
  L : Subgroup G
  T : Subgroup G
  H : Subgroup G

namespace Setup
variable {G} (D : Setup G)

/-- Right conjugation Aᵍ = g⁻¹Ag. -/
def conjugate (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g⁻¹).toMonoidHom

def G₁ : Subgroup G := normalizer (D.V₁ : Set G)
def LT : Subgroup G := D.L ⊔ D.T

/-- The embedded two-residual of N_L(V₁). -/
def L₁ : Subgroup G :=
  let N := D.L ⊓ D.G₁
  (pResidual 2 N).map N.subtype

def QH : Subgroup G := D.H.pCoreIn 2
def U : Subgroup G := conjugateSpanBy D.V D.H
def VL : Subgroup G := conjugateSpanBy D.V₁ D.L

def I (g : G) : Subgroup G := D.U ⊔ conjugate D.U g
def S (g : G) : Subgroup G := (D.I g).pCoreIn 2
def W (g : G) : Subgroup G := D.U ⊓ D.S g
def S₂ (g : G) : Subgroup G := D.U ⊓ conjugate D.U g

abbrev Star := D.LT ⧸ pCore 2 D.LT

def star (A : Subgroup G) : Subgroup D.Star :=
  (A.subgroupOf D.LT).map (QuotientGroup.mk' (pCore 2 D.LT))

instance point_normal : (D.V₁.subgroupOf D.G₁).Normal := by
  change (D.V₁.subgroupOf (normalizer (D.V₁ : Set G))).Normal
  infer_instance

abbrev Tilde := D.G₁ ⧸ D.V₁.subgroupOf D.G₁

def tilde (A : Subgroup G) : Subgroup D.Tilde :=
  (A.subgroupOf D.G₁).map (QuotientGroup.mk' (D.V₁.subgroupOf D.G₁))

/-- The assumptions of G.2.1 before irreducibility. G.2.6 retains these
and substitutes the conclusions of G.2.2 for irreducibility. -/
structure BaseHypothesis [Finite G] : Prop where
  elementary : IsElementaryAbelian 2 D.V
  point_ne_bot : D.V₁ ≠ ⊥
  point_le : D.V₁ ≤ D.V
  residual : pResidual 2 D.L = ⊤
  V_le_T : D.V ≤ D.T
  T_normalizes_point : D.T ≤ D.G₁
  T_normalizes_V : D.T ≤ normalizer (D.V : Set G)
  T_normalizes_L : D.T ≤ normalizer (D.L : Set G)
  sylow_LT : ∃ P : Sylow 2 D.LT, (P : Subgroup D.LT).map D.LT.subtype = D.T
  H_le : D.H ≤ D.G₁
  local_le : D.L₁ ⊔ D.T ≤ D.H
  sylow_H : ∃ P : Sylow 2 D.H, (P : Subgroup D.H).map D.H.subtype = D.T
  characteristic_two : Theory.GroupTheory.generalizedFitting D.H = pCore 2 D.H

/-- The genuine assumptions of G.2.1. The nonzero quotient and invariant
interval specify irreducibility without choosing vector-space coordinates. -/
structure Hypothesis [Finite G] : Prop extends BaseHypothesis D where
  local_normalizes_V : D.L₁ ⊔ D.T ≤ normalizer (D.V : Set G)
  quotient_nonzero : D.V₁ ≠ D.V
  irreducible : ∀ A : Subgroup G, D.V₁ ≤ A → A ≤ D.V →
    D.L₁ ⊔ D.T ≤ normalizer (A : Set G) → A = D.V₁ ∨ A = D.V

variable [Finite G] {D}

/-- The seed and its H-closure lie in the actual local overgroup. -/
theorem BaseHypothesis.U_le_H (h : D.BaseHypothesis) : D.U ≤ D.H :=
  conjugateSpanBy_le_self (h.V_le_T.trans (le_sup_right.trans h.local_le))

/-- Relative normality of the H-closure, not ambient normality. -/
theorem BaseHypothesis.U_normal (h : D.BaseHypothesis) : (D.U.subgroupOf D.H).Normal :=
  (normal_subgroupOf_iff_le_normalizer h.U_le_H).mpr
    (le_normalizer_conjugateSpanBy D.V D.H)

/-- The entire closure centralizes the fixed point subgroup. This is the
first reduction in the source proof of G.2.2. -/
theorem BaseHypothesis.U_le_centralizer_point (h : D.BaseHypothesis) :
    D.U ≤ centralizer (D.V₁ : Set G) := by
  let := h.elementary
  apply conjugateSpanBy_le
  · intro v hv a ha
    exact congrArg Subtype.val (mul_comm (⟨a, h.point_le ha⟩ : D.V) ⟨v, hv⟩)
  · exact h.H_le.trans ((normal_subgroupOf_iff_le_normalizer
      (centralizer_le_normalizer (D.V₁ : Set G))).mp inferInstance)

end Setup
end CFSG.Quasithin.ChapterG.Section02
