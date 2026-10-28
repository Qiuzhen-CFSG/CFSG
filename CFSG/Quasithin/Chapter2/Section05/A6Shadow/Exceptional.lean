module
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalFrattini.Source
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.OriginalExceptional

/-!
# Literal exceptional overcomponent adapter

The ambient marked A₈ overcomponent and centralizer-four identity give the
exact local data used by the source exceptional argument. We use the inverse
crossing element to convert source right conjugation to left conjugation.

Source: Aschbacher--Smith, 2.5.26, printed p.569.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

/-- The original overcomponent data, without any terminal model conclusions. -/
structure MarkedA8Overcomponent (d : EarlierSetup κ G) (i : G) where
  Ki : Subgroup G
  model : Ki ≃* alternatingGroup (Fin 8)
  le_centralizer : Ki ≤ centralizer ({i} : Set G)
  component : IsComponent (centralizer ({i} : Set G))
    (Ki.subgroupOf (centralizer {i}))
  residual : d.K = (solvableResidual (Ki ⊓ centralizer ({d.t} : Set G) : Subgroup G)).map
    (Ki ⊓ centralizer ({d.t} : Set G)).subtype
  transposition : ∀ k : Ki,
    (model.symm (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) (model k)) : G) =
      d.t * k * d.t⁻¹

/-- Convert the exact ambient four-centralizer identity to the literal
relative centralizer used by the exceptional A₈ source argument. -/
private theorem core_centralizer_eq_of_ambient (d : EarlierSetup κ G)
    (i : G) (hi : i ∈ d.SC)
    (hR : d.SC ⊓ centralizer ({i} : Set G) = zpowers i ⊔ zpowers d.t) :
    centralizer ({(⟨i,hi⟩ : d.SC)} : Set d.SC) =
      zpowers (⟨i,hi⟩ : d.SC) ⊔ zpowers (⟨d.t,d.t_mem⟩ : d.SC) := by
  apply map_injective d.SC.subtype_injective
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
  have he : (centralizer ({(⟨i,hi⟩ : d.SC)} : Set d.SC)).map d.SC.subtype =
      d.SC ⊓ centralizer ({i} : Set G) := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hb))⟩
    · intro ha
      exact ⟨⟨a,ha.1⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp ha.2)),rfl⟩
  exact he.trans hR

/-- The exceptional source setup keeps the original H,K,S,SC,t and uses the
inverse original crossing element to respect the left-conjugation convention. -/
private def toExceptionalLocalData (d : EarlierSetup κ G)
    (hGt : d.H = centralizer ({d.t} : Set G)) (hphi : frattini d.SC ≠ ⊥)
    (i : G) (hi : i ∈ d.SC) (hi2 : orderOf i = 2) (hit : i ≠ d.t)
    (hR : d.SC ⊓ centralizer ({i} : Set G) = zpowers i ⊔ zpowers d.t)
    (a : MarkedA8Overcomponent d i) : A6ShadowRankOne.A8Reduction.LocalData G where
  H := d.H
  K := d.K
  S := d.S
  SC := d.SC
  Ki := a.Ki
  t := d.t
  i := i
  x := d.x⁻¹
  centralizer_t := hGt
  generated := d.generated
  modelK := d.modelK
  modelKi := a.model
  sylow := d.sylow
  sylow_eq := d.sylow_eq
  centralizer_K := d.centralizer_K
  core := d.core
  t_mem := d.t_mem
  t_order := d.t_order
  t_central := fun _s hs => mem_centralizer_singleton_iff.mp (d.h_le_centralizer_t (d.s_le_h hs))
  x_normalizes := (normalizer (d.S : Set G)).inv_mem d.x_normalizes
  disjoint_conjugate := d.disjoint_conjugate
  frattini_ne := hphi
  i_mem := hi
  i_order := hi2
  i_ne_t := hit
  centralizer_i := core_centralizer_eq_of_ambient d i hi hR
  Ki_le_centralizer := a.le_centralizer
  component := a.component
  residual := a.residual
  t_action := a.transposition
  action := d.action
  action_surjective := d.action_surjective
  action_compatible := d.action_compatible
  action_kernel := d.action_kernel

/-- The marked exceptional A₈ overcomponent contradicts the original source
configuration; all quotient, square, fusion and selection marks are proved. -/
theorem EarlierSetup.marked_a8_overcomponent_false (d : EarlierSetup κ G)
    (hGt : d.H = centralizer ({d.t} : Set G)) (hphi : frattini d.SC ≠ ⊥)
    (i : G) (hi : i ∈ d.SC) (hi2 : orderOf i = 2) (hit : i ≠ d.t)
    (hR : d.SC ⊓ centralizer ({i} : Set G) = zpowers i ⊔ zpowers d.t)
    (a : MarkedA8Overcomponent d i) : False :=
  A6ShadowRankOne.original_exceptional_branch_impossible d
    (toExceptionalLocalData d hGt hphi i hi hi2 hit hR a) rfl rfl rfl rfl

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
