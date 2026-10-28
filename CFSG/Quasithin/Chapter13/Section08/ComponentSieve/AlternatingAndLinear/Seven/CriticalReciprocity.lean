module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.CriticalReciprocity.Transport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.CriticalReciprocity.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.FirstCase

/-!
# The reciprocal marked transvection in the four-plus-three branch

Assume the chosen case-(2) critical pair has m(Vγ*) = 1. The proved
13.8.18(3) implication, including its component-generation step, forces
U_H to act on Uγ by transvections with axis Dγ. Strictness of D_H supplies
an action nontrivial modulo A₁. Inverse endpoint conjugation transports
that action to Uβ on the literal U_H/V₁; its displacement survives the
quotient and has rank exactly one. F.9.13(2) puts Vβ in O₂(L₁T), hence
Vβ* in the intrinsic two-core of (L₁T)*.

`Earlier` lists the preceding flag, kernel, component and case-(2) inputs;
it contains no transvection, reciprocal-action or classification conclusion.
`marked_transvection_of_rank_one` is the transport result. The optional
`exclude_of_rank_one` uses the full 13.8.5 alternatives and the existing
seven-point parity argument to contradict this marked transvection.
The rank-one premise and the earlier source inputs remain the responsibility
of the 13.8.24 assembly owner.

The β marking is corrected explicitly in `CriticalReciprocity.Geometry`:
β is the inverse image of γ₁, whereas the inverse image of γ is γ₁ itself.
No inverse conjugates of U_H and Uγ are identified with each other.

Source: Aschbacher–Smith, 13.8.24, printed pp.958–959/PDF pp.975–976,
using 13.8.8, 13.8.11 and 13.8.18(3), printed pp.949–950 and 953,
and F.9.12–13, printed p.322 (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.CriticalReciprocity
open CriticalGeometry
variable {G : Type*} [Group G] [Finite G] {L T H V : Subgroup G}

/-- Earlier source data at the chosen case-(2) critical pair. The component
conditions are relative to Gγ. No transvection or rank-one conclusion is a field. -/
structure Earlier (c : CriticalPair L T H V) (L₁ K V₃ V₁ : Subgroup G) : Prop where
  product : H = K ⊔ (L₁ ⊔ T)
  edge : (L ⊔ T) ⊓ H = L₁ ⊔ T
  component_normal : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
    (vertexGroup L T H c.gamma)).Normal
  component_residual : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
    (vertexGroup L T H c.gamma)) = ⊤
  component_quasisimple : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
    (K.map (MulAut.conj (c.gb : G)).toMonoidHom))
  terminal_core : Source.VH H V ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2
  flag : V₃ ≤ V
  V_le : V ≤ H
  line_le : V₁ ≤ Source.UH H V₃
  line_normalized : H ≤ normalizer (V₁ : Set G)
  Vgamma_le : c.Vgamma ≤ H
  core_commutator : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁
  noncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃
  edge_commutator : ⁅edgeGroup L T H c.gamma c.previous,
    V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃
  Dgamma_kernel : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
    c.Ugamma V₃ ⊓ Source.QH H
  DH_kernel : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
    Source.UH H V₃ ⊓ c.Qgamma
  DH_proper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃
  Dgamma_proper : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃
  Qgamma_le_edge : c.Qgamma ≤ edgeGroup L T H c.gamma c.previous
  edge_proper : edgeGroup L T H c.gamma c.previous < vertexGroup L T H c.gamma
  comparison : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
      (Source.UH H V₃) ≤
    (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)
  line_card : Nat.card V₁ = 2

namespace Earlier
variable {c : CriticalPair L T H V} {L₁ K V₃ V₁ : Subgroup G}
  (d : Earlier c L₁ K V₃ V₁)
include d

omit [Finite G] in
/-- F.9.13(2) supplies U_H's actual containment in the terminal two-core. -/
theorem UH_le_terminal_core :
    Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2 :=
  (conjugateSpanBy_mono d.flag le_rfl).trans d.terminal_core

omit [Finite G] in
/-- The terminal vertex acts by conjugation on Uγ. -/
theorem normalizes_Ugamma : Source.UH H V₃ ≤ normalizer (c.Ugamma V₃ : Set G) :=
  (d.UH_le_terminal_core.trans ((pCoreIn_le 2 _).trans inf_le_left)).trans
    (c.normalizes_Ugamma V₃)

/-- Contraposition of the proved 13.8.18(3), with its genuine endpoint
hypotheses. The rank-one premise forces the common-axis transvection action. -/
theorem axis_of_rank_one [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (hrank : rank (Source.starImage H c.Vgamma) = 1) :
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁) d.normalizes_Ugamma := by
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  by_contra hn
  have hlineH := d.line_le.trans (conjugateSpanBy_le_self (d.flag.trans d.V_le))
  have hgt := c.rank_gt_one_of_component_generation L₁ K V₃ V₁ d.product d.edge
    d.component_normal d.component_residual d.component_quasisimple d.UH_le_terminal_core
    d.DH_kernel d.flag d.V_le hlineH d.line_normalized d.Vgamma_le
    d.core_commutator d.noncentral d.edge_commutator d.Dgamma_kernel d.DH_proper
    d.Dgamma_proper d.Qgamma_le_edge d.edge_proper d.comparison d.line_card hn
  omega

end Earlier

/-- The actual reciprocal Uβ* contains a nonidentity transvection on U_H/V₁.
Both quotient survival and the fixed codimension are conclusions. -/
theorem marked_transvection_of_rank_one
    (c : CriticalPair L T H V) (L₁ K V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (d : Earlier c L₁ K V₃ V₁)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : Compatible H (Source.UH H V₃) V₁ (le_normalizer_conjugateSpanBy V₃ H) ρ)
    (hrank : rank (Source.starImage H c.Vgamma) = 1) :
    ∃ a ∈ Source.starImage H (Ubeta c V₃), a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1 := by
  have hUbeta := (Ubeta_le_Vbeta c V₃ d.flag).trans
    (Vbeta_le_H c L₁ d.edge d.terminal_core)
  exact reciprocal_of_axis H (Source.UH H V₃) V₁ (c.gb : G) hUbeta
    (le_normalizer_conjugateSpanBy V₃ H) d.normalizes_Ugamma ρ hρ d.DH_proper
    (d.axis_of_rank_one hrank).2.2

/-- The marked actor and its ambient Vβ both land in the literal local two-core. -/
theorem marked_transvection_and_placement
    (c : CriticalPair L T H V) (L₁ K V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (d : Earlier c L₁ K V₃ V₁)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : Compatible H (Source.UH H V₃) V₁ (le_normalizer_conjugateSpanBy V₃ H) ρ)
    (hrank : rank (Source.starImage H c.Vgamma) = 1) :
    (∃ a ∈ Source.starImage H (Ubeta c V₃), a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) ∧
      Source.starImage H (Vbeta c) ≤ (Source.starImage H (L₁ ⊔ T)).pCoreIn 2 :=
  ⟨marked_transvection_of_rank_one c L₁ K V₃ V₁ d ρ hρ hrank,
    star_Vbeta_le_twoCore c L₁ d.edge d.terminal_core⟩

/-- Conditional endpoint for the four-plus-three branch. The genuine earlier
13.8.5 alternatives select the whole natural module after the reciprocal
transvection has been constructed. The partition is derived by FirstCase;
no natural-module identification or A₇ exclusion is assumed. -/
theorem exclude_of_rank_one
    (c : CriticalPair L T H V) (L₁ K V₃ V₁ G₁ M : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (d : Earlier c L₁ K V₃ V₁)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : Compatible H (Source.UH H V₃) V₁ (le_normalizer_conjugateSpanBy V₃ H) ρ)
    (hrank : rank (Source.starImage H c.Vgamma) = 1)
    (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ → Group.IsSolvable J → J ≤ M)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (h5 : ∀ a : Source.Hstar H, a ≠ 1 → fixedCodim ρ (zpowers a) = 1 →
      LocalGeometry.TransvectionModels ρ L)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* Multiplicative (Fin 2 → ZMod 3))) : False := by
  let _ : IsElementaryAbelian 2 (Ubeta c V₃) := IsElementaryAbelian.map _
  exact LocalGeometry.exclude_first_case_actor H L L₁ T G₁ M (Ubeta c V₃) (Vbeta c)
    (d.edge ▸ inf_le_right) hHG htheta h13 S hS ρ φ hφ hAlt h5 hcover
    (Vbeta_le_H c L₁ d.edge d.terminal_core) (Ubeta_le_Vbeta c V₃ d.flag)
    ⟨1, by
      change (Vbeta c).conjBy 1 ≤ _
      rw [conjBy_one]
      exact Vbeta_le_twoCore c L₁ d.edge d.terminal_core⟩
    (marked_transvection_of_rank_one c L₁ K V₃ V₁ d ρ hρ hrank)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.CriticalReciprocity
end
