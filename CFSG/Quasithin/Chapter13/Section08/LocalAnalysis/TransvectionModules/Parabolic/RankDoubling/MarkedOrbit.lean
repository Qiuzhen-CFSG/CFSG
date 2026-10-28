module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.OrbitModels
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Transport of the marked source orbit in 13.8.6

The marking starts on the literal source quotient `U_H/V₁`. It identifies
`V₂/V₁` with the weight-four point and `V₃/V₁` with the plane through
`e₁₂₃₄` and `e₁₂₅₆`, and intertwines actual K₂-conjugation with a surjective
actor map onto `BinaryFlags.K`.

Let B = ⟨V₃^{K₂}⟩. Only B, rather than all of U₂, lies in U_H. Restricting
the maps into U₂/V₂ and into the marked model modulo its point to B gives
the same kernel: the elements of V₂. Their quotient maps are injective.
The first image is the literal W of `RankDoubling.Quotient`; the second is
the model orbit span, by the marked plane and the surjectivity of the actor.
The first isomorphism theorem therefore constructs the required equivalence,
with evaluation on every actual source conjugate retained.

The cover and natural specializations reuse the orbit calculations in
`OrbitModels`, giving dimensions three and two. The standing flags ensure
that each denominator is contained in its numerator; normality is relative
and follows from the elementary abelian source groups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the orbit
rank calculation in 13.8.6, printed p.948 (PDF p.965). Construction of the
markings and the dimension doubling for U₂/V₂ belong to the source assembly;
neither a model for W nor its dimension is assumed here.
-/

@[expose] public section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.MarkedOrbit
open Theory.SpecificGroups.SymmetricSix
abbrev F := ZMod 2
variable {G : Type*} [Group G]
variable (H V V₁ V₂ V₃ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The map from the actual source group to its quotient by V₁. -/
def sourceMap : Additive (Source.UH H V₃) →ₗ[F] Additive (Source.Utilde H V₃ V₁) :=
  (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))).toAdditive.toZModLinearMap 2

@[simp] theorem sourceMap_eq_zero (x : Additive (Source.UH H V₃)) :
    sourceMap H V₁ V₃ x = 0 ↔ (x.toMul : G) ∈ V₁ :=
  QuotientGroup.eq_one_iff x.toMul

variable {X : Type*} [AddCommGroup X] [Module F X]

def coordinates (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[F] X) :
    Additive (Source.UH H V₃) →ₗ[F] X := e.toLinearMap.comp (sourceMap H V₁ V₃)

def flagImage (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[F] X) (A : Subgroup G) :
    Submodule F X :=
  (AddSubgroup.toZModSubmodule (n := 2) (A.subgroupOf (Source.UH H V₃)).toAddSubgroup).map
    (coordinates H V₁ V₃ e)

/-- Conjugation is evaluated in U_H, never on arbitrary elements of U₂. -/
def conjugate (k : Source.K2 H V₂) (u : Source.UH H V₃) : Source.UH H V₃ :=
  ⟨(k : G) * (u : G) * (k : G)⁻¹,
    (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H
      (Source.K2_le H V₂ k.property)) u).mp u.property⟩

/-- Coordinates on the literal U_H/V₁, including the marked flag and actor.
No quotient model or rank for W is part of this input. -/
structure Marking (ρ : Representation F BinaryFlags.S X) (p s : X) where
  equiv : Additive (Source.Utilde H V₃ V₁) ≃ₗ[F] X
  actor : Source.K2 H V₂ →* BinaryFlags.K
  actor_surjective : Function.Surjective actor
  point_image : flagImage H V₁ V₃ equiv V₂ = Submodule.span F {p}
  plane_image : flagImage H V₁ V₃ equiv V₃ = Submodule.span F {p, s}
  intertwines : ∀ (k : Source.K2 H V₂) (u : Source.UH H V₃),
    coordinates H V₁ V₃ equiv (Additive.ofMul (conjugate H V₂ V₃ k u)) =
      ρ (actor k).val (coordinates H V₁ V₃ equiv (Additive.ofMul u))

variable {H V₁ V₂ V₃}
variable {ρ : Representation F BinaryFlags.S X} {p s : X}
variable (d : Marking H V₁ V₂ V₃ ρ p s)

theorem coordinates_eq_zero (x : Additive (Source.UH H V₃)) :
    coordinates H V₁ V₃ d.equiv x = 0 ↔ (x.toMul : G) ∈ V₁ := by
  change d.equiv (sourceMap H V₁ V₃ x) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact QuotientGroup.eq_one_iff x.toMul

theorem coordinates_mem_point (h₁ : V₁ ≤ V₂) (x : Additive (Source.UH H V₃)) :
    coordinates H V₁ V₃ d.equiv x ∈ Submodule.span F {p} ↔ (x.toMul : G) ∈ V₂ := by
  rw [← d.point_image]
  constructor
  · rintro ⟨y, hy, he⟩
    have hh : coordinates H V₁ V₃ d.equiv (x - y) = 0 := by
      rw [map_sub, he, sub_self]
    have hm := h₁ ((coordinates_eq_zero d (x - y)).mp hh)
    change (y.toMul : G) ∈ V₂ at hy
    change (x.toMul : G) / (y.toMul : G) ∈ V₂ at hm
    simpa using V₂.mul_mem hm hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable (H V₂ V₃)
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

/-- B, viewed as a submodule of the actual U₂. -/
def orbitDomain : Submodule F (Additive (Source.U2 H V V₂)) :=
  AddSubgroup.toZModSubmodule (n := 2)
    ((conjugateSpanBy V₃ (Source.K2 H V₂)).subgroupOf (Source.U2 H V V₂)).toAddSubgroup

/-- The restriction B → U₂/V₂. -/
def toSource : orbitDomain H V V₂ V₃ →ₗ[F] Additive (Uhat H V V₂) :=
  (quotientMap H V V₂).domRestrict (orbitDomain H V V₂ V₃)

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
theorem toSource_range (h₃ : V₃ ≤ V) :
    (toSource H V V₂ V₃).range = W H V V₂ V₃ h₃ := by
  rw [W_eq_image_span, toSource, LinearMap.range_domRestrict]
  rfl

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
theorem toSource_eq_zero (b : orbitDomain H V V₂ V₃) :
    toSource H V V₂ V₃ b = 0 ↔ (b.val.toMul : G) ∈ V₂ :=
  quotientMap_eq_zero H V V₂ b.val

/-- The inclusion of B in U_H supplied by the source conjugate spans. -/
def toUH (h₃ : V₃ ≤ V) : orbitDomain H V V₂ V₃ →ₗ[F] Additive (Source.UH H V₃) :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun b := Additive.ofMul ⟨b.val.toMul.val, (threeOrbit_le H V V₂ V₃ h₃ b.property).1⟩
    map_zero' := rfl
    map_add' _ _ := rfl }

theorem toUH_injective (h₃ : V₃ ≤ V) : Function.Injective (toUH H V V₂ V₃ h₃) := by
  intro b c he
  apply Subtype.ext
  exact congrArg Additive.ofMul
    (Subtype.ext (congrArg (fun y : Additive (Source.UH H V₃) => y.toMul.val) he))

variable {H V V₂ V₃}

/-- Restrict the marked quotient map to B, then kill the marked point. -/
def toModel (h₃ : V₃ ≤ V) : orbitDomain H V V₂ V₃ →ₗ[F] X ⧸ Submodule.span F {p} :=
  (Submodule.span F {p}).mkQ.comp
    ((coordinates H V₁ V₃ d.equiv).comp (toUH H V V₂ V₃ h₃))

theorem toModel_eq_zero (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V)
    (b : orbitDomain H V V₂ V₃) :
    toModel d h₃ b = 0 ↔ (b.val.toMul : G) ∈ V₂ := by
  change (Submodule.span F {p}).mkQ _ = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact coordinates_mem_point d h₁ _

theorem kernels_eq (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V) :
    (toSource H V V₂ V₃).ker = (toModel d h₃).ker := by
  ext b
  exact (toSource_eq_zero H V V₂ V₃ b).trans (toModel_eq_zero d h₁ h₃ b).symm

/-- The model orbit after quotienting by its marked point. -/
def modelOrbit (ρ : Representation F BinaryFlags.S X) (p s : X) :
    Submodule F (X ⧸ Submodule.span F {p}) :=
  Submodule.span F {v | ∃ k ∈ BinaryFlags.K, (Submodule.span F {p}).mkQ (ρ k s) = v}

private theorem plane_to_orbit (hfix : ∀ k ∈ BinaryFlags.K, ρ k p = p)
    (k : BinaryFlags.K) (v : X) (hv : v ∈ Submodule.span F {p, s}) :
    (Submodule.span F {p}).mkQ (ρ k.val v) ∈ modelOrbit ρ p s := by
  let f := (Submodule.span F {p}).mkQ.comp (ρ k.val)
  have hh : Submodule.span F {p, s} ≤ (modelOrbit ρ p s).comap f := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      change (Submodule.span F {p}).mkQ (ρ k.val p) ∈ modelOrbit ρ p s
      rw [hfix k.val k.property]
      have hp : (Submodule.span F {p}).mkQ p = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span (Set.mem_singleton p))
      rw [hp]
      exact (modelOrbit ρ p s).zero_mem
    · have he : x = s := Set.mem_singleton_iff.mp hx
      subst x
      exact Submodule.subset_span ⟨k.val, k.property, rfl⟩
  exact hh hv

theorem toModel_range (h₃ : V₃ ≤ V)
    (hfix : ∀ k ∈ BinaryFlags.K, ρ k p = p) :
    (toModel d h₃).range = modelOrbit ρ p s := by
  let B := conjugateSpanBy V₃ (Source.K2 H V₂)
  have hBU := (threeOrbit_le H V V₂ V₃ h₃).trans inf_le_left
  have hBQ := (threeOrbit_le H V V₂ V₃ h₃).trans inf_le_right
  let m := coordinates H V₁ V₃ d.equiv
  let q := (Submodule.span F {p}).mkQ
  apply le_antisymm
  · have hall : ∀ (z : G) (hz : z ∈ B),
        q (m (Additive.ofMul ⟨z, hBU hz⟩)) ∈ modelOrbit ρ p s := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨k, hk, v, hv, rfl⟩ := hz
        have hvU := le_conjugateSpanBy V₃ H hv
        change q (m (Additive.ofMul
          (conjugate H V₂ V₃ ⟨k,hk⟩ ⟨v,hvU⟩))) ∈ _
        rw [d.intertwines]
        apply plane_to_orbit hfix
        rw [← d.plane_image]
        exact ⟨Additive.ofMul ⟨v,hvU⟩, hv, rfl⟩
      | one =>
        change q (m 0) ∈ _
        rw [map_zero, map_zero]
        exact (modelOrbit ρ p s).zero_mem
      | mul a b ha hb ha' hb' =>
        change q (m (Additive.ofMul ⟨a,hBU ha⟩ + Additive.ofMul ⟨b,hBU hb⟩)) ∈ _
        rw [map_add, map_add]
        exact (modelOrbit ρ p s).add_mem ha' hb'
      | inv a ha ha' =>
        change q (m (-Additive.ofMul ⟨a,hBU ha⟩)) ∈ _
        rw [map_neg, map_neg]
        exact (modelOrbit ρ p s).neg_mem ha'
    rintro x ⟨b,rfl⟩
    exact hall b.val.toMul.val b.property
  · apply Submodule.span_le.mpr
    rintro x ⟨k,hk,rfl⟩
    obtain ⟨a,ha⟩ := d.actor_surjective ⟨k,hk⟩
    have hs : s ∈ flagImage H V₁ V₃ d.equiv V₃ := by
      rw [d.plane_image]
      exact Submodule.subset_span (by simp)
    obtain ⟨u,hu,he⟩ := hs
    change (u.toMul : G) ∈ V₃ at hu
    have hb : (a : G) * (u.toMul : G) * (a : G)⁻¹ ∈ B :=
      Subgroup.subset_closure ⟨a,a.property,u.toMul,hu,rfl⟩
    refine ⟨⟨Additive.ofMul ⟨_, hBQ hb⟩, hb⟩, ?_⟩
    change q (m (Additive.ofMul (conjugate H V₂ V₃ a u.toMul))) = _
    rw [d.intertwines, ofMul_toMul, he, ha]

/-- The first-isomorphism comparison, with the kernels proved on B. -/
noncomputable def rangeEquiv (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V) :
    (toSource H V V₂ V₃).range ≃ₗ[F] (toModel d h₃).range :=
  (toSource H V V₂ V₃).quotKerEquivRange.symm |>.trans
    ((Submodule.quotEquivOfEq _ _ (kernels_eq d h₁ h₃)).trans
      (toModel d h₃).quotKerEquivRange)

theorem rangeEquiv_apply (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V)
    (b : orbitDomain H V V₂ V₃) :
    (rangeEquiv d h₁ h₃ ⟨toSource H V V₂ V₃ b, LinearMap.mem_range_self _ b⟩).val =
      toModel d h₃ b := by
  simp [rangeEquiv]

/-- The literal source orbit is linearly equivalent to the marked model orbit. -/
noncomputable def orbitEquiv (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V)
    (hfix : ∀ k ∈ BinaryFlags.K, ρ k p = p) :
    W H V V₂ V₃ h₃ ≃ₗ[F] modelOrbit ρ p s :=
  (LinearEquiv.ofEq _ _ (toSource_range H V V₂ V₃ h₃).symm).trans
    ((rangeEquiv d h₁ h₃).trans (LinearEquiv.ofEq _ _ (toModel_range d h₃ hfix)))

theorem orbitEquiv_apply (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V)
    (hfix : ∀ k ∈ BinaryFlags.K, ρ k p = p)
    (b : orbitDomain H V V₂ V₃)
    (hb : toSource H V V₂ V₃ b ∈ W H V V₂ V₃ h₃) :
    (orbitEquiv d h₁ h₃ hfix ⟨toSource H V V₂ V₃ b, hb⟩).val = toModel d h₃ b := by
  exact rangeEquiv_apply d h₁ h₃ b

omit [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 V]
    [IsMulCommutative (Source.VH H V)] in
/-- The denominator really lies in B for the standing source flag. -/
theorem denominator_le_orbit (h₂ : V₂ ≤ V₃) :
    V₂ ≤ conjugateSpanBy V₃ (Source.K2 H V₂) :=
  h₂.trans (le_conjugateSpanBy V₃ (Source.K2 H V₂))

/-- The common quotient is B modulo precisely its V₂ elements. -/
abbrev CommonQuotient := orbitDomain H V V₂ V₃ ⧸ (toSource H V V₂ V₃).ker

/-- The induced embedding of B/V₂ into the literal U₂/V₂. -/
def quotientToSource : CommonQuotient (H := H) (V := V) (V₂ := V₂) (V₃ := V₃) →ₗ[F]
    Additive (Uhat H V V₂) :=
  (toSource H V V₂ V₃).ker.liftQ (toSource H V V₂ V₃) le_rfl

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
theorem quotientToSource_injective : Function.Injective
    (quotientToSource (H := H) (V := V) (V₂ := V₂) (V₃ := V₃)) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

/-- The induced embedding in the model modulo the marked point. -/
def quotientToModel (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V) :
    CommonQuotient (H := H) (V := V) (V₂ := V₂) (V₃ := V₃) →ₗ[F]
      X ⧸ Submodule.span F {p} :=
  (toSource H V V₂ V₃).ker.liftQ (toModel d h₃) (kernels_eq d h₁ h₃).le

theorem quotientToModel_injective (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V) :
    Function.Injective (quotientToModel d h₁ h₃) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (kernels_eq d h₁ h₃).ge)

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
theorem quotientToSource_mk (b : orbitDomain H V V₂ V₃) :
    quotientToSource (Submodule.Quotient.mk b) = toSource H V V₂ V₃ b := rfl

theorem quotientToModel_mk (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V)
    (b : orbitDomain H V V₂ V₃) :
    quotientToModel d h₁ h₃ (Submodule.Quotient.mk b) = toModel d h₃ b := rfl

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
theorem quotientToSource_range (h₃ : V₃ ≤ V) :
    (quotientToSource (H := H) (V := V) (V₂ := V₂) (V₃ := V₃)).range =
      W H V V₂ V₃ h₃ := by
  rw [quotientToSource, Submodule.range_liftQ, toSource_range H V V₂ V₃ h₃]

theorem quotientToModel_range (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V)
    (hfix : ∀ k ∈ BinaryFlags.K, ρ k p = p) :
    (quotientToModel d h₁ h₃).range = modelOrbit ρ p s := by
  rw [quotientToModel, Submodule.range_liftQ, toModel_range d h₃ hfix]

/-- A specified actual conjugate, as an element of B. -/
def orbitElement (h₃ : V₃ ≤ V) (k : Source.K2 H V₂) (v : V₃) : orbitDomain H V V₂ V₃ :=
  ⟨Additive.ofMul ⟨(k : G) * (v : G) * (k : G)⁻¹,
    Subgroup.subset_closure ⟨k,k.property,v,h₃ v.property,rfl⟩⟩,
    Subgroup.subset_closure ⟨k,k.property,v,v.property,rfl⟩⟩

/-- The same conjugate in the actual source orbit subspace W. -/
def orbitVector (h₃ : V₃ ≤ V) (k : Source.K2 H V₂) (v : V₃) : W H V V₂ V₃ h₃ :=
  ⟨toSource H V V₂ V₃ (orbitElement h₃ k v), Submodule.subset_span ⟨k,v,rfl⟩⟩

theorem orbitEquiv_orbitVector (h₁ : V₁ ≤ V₂) (h₃ : V₃ ≤ V)
    (hfix : ∀ k ∈ BinaryFlags.K, ρ k p = p)
    (k : Source.K2 H V₂) (v : V₃) :
    (orbitEquiv d h₁ h₃ hfix (orbitVector h₃ k v)).val =
      (Submodule.span F {p}).mkQ (ρ (d.actor k).val
        (coordinates H V₁ V₃ d.equiv
          (Additive.ofMul ⟨v, le_conjugateSpanBy V₃ H v.property⟩))) := by
  exact (orbitEquiv_apply d h₁ h₃ hfix (orbitElement h₃ k v)
    (orbitVector h₃ k v).property).trans
      (congrArg (Submodule.span F {p}).mkQ
        (d.intertwines k ⟨v, le_conjugateSpanBy V₃ H v.property⟩))

open BinaryPermutation
variable (H V₁ V₂ V₃)

/-- Cover coordinates on the actual U_H/V₁, with the weight-four point and plane. -/
abbrev CoverMarking :=
  Marking H V₁ V₂ V₃ (coreRepresentation (Fin 6)) OrbitModels.point OrbitModels.seed

/-- Natural-module coordinates on the actual U_H/V₁, marking the images of the
same two weight-four vectors. -/
abbrev NaturalMarking :=
  Marking H V₁ V₂ V₃ (naturalRepresentation (Fin 6)) OrbitModels.naturalPoint
    (coreToNatural (Fin 6) OrbitModels.seed)

variable {H V₁ V₂ V₃}

private theorem natural_point_fixed (k : BinaryFlags.S) (hk : k ∈ BinaryFlags.K) :
    naturalRepresentation (Fin 6) k OrbitModels.naturalPoint = OrbitModels.naturalPoint := by
  change naturalRepresentation (Fin 6) k (coreToNatural (Fin 6) OrbitModels.point) = _
  rw [← coreToNatural_equivariant, OrbitModels.point_fixed k hk]
  rfl

/-- Transport the literal source orbit to the computed three-dimensional cover orbit.
The flag makes all the subgroup quotients genuine. -/
noncomputable def coverEquiv (h₁ : V₁ ≤ V₂) (_h₂ : V₂ ≤ V₃) (h₃ : V₃ ≤ V)
    (d : CoverMarking H V₁ V₂ V₃) :
    W H V V₂ V₃ h₃ ≃ₗ[F] OrbitModels.coverOrbit :=
  (orbitEquiv d h₁ h₃ OrbitModels.point_fixed).trans
    (LinearEquiv.ofEq _ _ OrbitModels.coverOrbit_eq_span.symm)

/-- Transport the literal source orbit to the computed two-dimensional natural orbit. -/
noncomputable def naturalEquiv (h₁ : V₁ ≤ V₂) (_h₂ : V₂ ≤ V₃) (h₃ : V₃ ≤ V)
    (d : NaturalMarking H V₁ V₂ V₃) :
    W H V V₂ V₃ h₃ ≃ₗ[F] OrbitModels.naturalQuotientOrbit :=
  (orbitEquiv d h₁ h₃ (by exact natural_point_fixed)).trans
    (LinearEquiv.ofEq _ _ OrbitModels.naturalQuotientOrbit_eq_span.symm)

/-- Evaluation retains the exact source conjugate and its marked actor. -/
theorem coverEquiv_orbitVector (h₁ : V₁ ≤ V₂) (h₂ : V₂ ≤ V₃) (h₃ : V₃ ≤ V)
    (d : CoverMarking H V₁ V₂ V₃) (k : Source.K2 H V₂) (v : V₃) :
    (coverEquiv h₁ h₂ h₃ d (orbitVector h₃ k v)).val =
      OrbitModels.pointSpace.mkQ (coreRepresentation (Fin 6) (d.actor k).val
        (coordinates H V₁ V₃ d.equiv
          (Additive.ofMul ⟨v, le_conjugateSpanBy V₃ H v.property⟩))) :=
  orbitEquiv_orbitVector d h₁ h₃ OrbitModels.point_fixed k v

/-- The natural transport uses the same literal quotient vectors. -/
theorem naturalEquiv_orbitVector (h₁ : V₁ ≤ V₂) (h₂ : V₂ ≤ V₃) (h₃ : V₃ ≤ V)
    (d : NaturalMarking H V₁ V₂ V₃) (k : Source.K2 H V₂) (v : V₃) :
    (naturalEquiv h₁ h₂ h₃ d (orbitVector h₃ k v)).val =
      OrbitModels.naturalPointSpace.mkQ (naturalRepresentation (Fin 6) (d.actor k).val
        (coordinates H V₁ V₃ d.equiv
          (Additive.ofMul ⟨v, le_conjugateSpanBy V₃ H v.property⟩))) :=
  orbitEquiv_orbitVector d h₁ h₃ natural_point_fixed k v

/-- The source W has rank three in the cover branch. -/
theorem cover_finrank (h₁ : V₁ ≤ V₂) (h₂ : V₂ ≤ V₃) (h₃ : V₃ ≤ V)
    (d : CoverMarking H V₁ V₂ V₃) : finrank F (W H V V₂ V₃ h₃) = 3 :=
  (coverEquiv h₁ h₂ h₃ d).finrank_eq.trans OrbitModels.coverOrbit_finrank

/-- The source W has rank two in the natural branch. -/
theorem natural_finrank (h₁ : V₁ ≤ V₂) (h₂ : V₂ ≤ V₃) (h₃ : V₃ ≤ V)
    (d : NaturalMarking H V₁ V₂ V₃) : finrank F (W H V V₂ V₃ h₃) = 2 :=
  (naturalEquiv h₁ h₂ h₃ d).finrank_eq.trans OrbitModels.naturalQuotientOrbit_finrank

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.MarkedOrbit
