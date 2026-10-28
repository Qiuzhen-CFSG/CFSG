module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.Basic

/-!
# The exact sequence attached to a supplement

For Y ≤ X ∩ W and X + W = U, inclusion induces the exact sequence
`0 → (X ∩ W)/Y → X/Y → U/W → 0`. We construct the maps, identify the
kernel and quotient by equivariant linear equivalences, and lift an
invariant complement of the kernel to a submodule C of X satisfying
`C + (X ∩ W) = X` and `C ∩ (X ∩ W) = Y`.

These are the section identifications needed to apply the two-factor
premise B.4.9(1) in the finite-length induction for Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March
2004, 13.8.25, printed p.961. The constructions do not assume splitting.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.TwoStep

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U) (W X Y : Subrepresentation ρ)

/-- The map from the literal section X/(X ∩ Y) to U/W, induced by inclusion. -/
def projection (hYW : Y ≤ W) :
    (sectionRepresentation ρ Y X).IntertwiningMap W.quotientRepresentation :=
  ((sectionLower ρ Y X).toSubmodule.liftQ
    (W.toSubmodule.mkQ.comp X.toSubmodule.subtype) (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hYW hx))).intertwiningMap_of_isIntertwiningMap _ _ (by
        intro g q
        induction q using Submodule.Quotient.induction_on with | _ x => rfl)

@[simp] theorem projection_mk (hYW : Y ≤ W) (x : X.toSubmodule) :
    projection ρ W X Y hYW ((sectionLower ρ Y X).toSubmodule.mkQ x) =
      W.toSubmodule.mkQ (x : U) := rfl

/-- A supplement to W maps onto its quotient. -/
theorem projection_surjective (hYW : Y ≤ W) (hX : X ⊔ W = ⊤) :
    Function.Surjective (projection ρ W X Y hYW) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ u =>
  have hu : u ∈ X.toSubmodule ⊔ W.toSubmodule := by
    change u ∈ (X ⊔ W).toSubmodule
    rw [hX]
    trivial
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
  refine ⟨(sectionLower ρ Y X).toSubmodule.mkQ ⟨x, hx⟩, ?_⟩
  change W.toSubmodule.mkQ x = W.toSubmodule.mkQ (x + w)
  have hw0 : W.toSubmodule.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hw
  rw [map_add, hw0, add_zero]

/-- Inclusion of the section of X ∩ W above Y into the section of X above Y. -/
def kernelInclusion :
    (sectionRepresentation ρ Y (X ⊓ W)).IntertwiningMap (sectionRepresentation ρ Y X) :=
  ((sectionLower ρ Y (X ⊓ W)).toSubmodule.liftQ
    ((sectionLower ρ Y X).toSubmodule.mkQ.comp
      (Submodule.inclusion (show (X ⊓ W).toSubmodule ≤ X.toSubmodule from inf_le_left)))
    (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx)).intertwiningMap_of_isIntertwiningMap _ _ (by
        intro g q
        induction q using Submodule.Quotient.induction_on with | _ x => rfl)

theorem kernelInclusion_injective : Function.Injective (kernelInclusion ρ W X Y) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro q hq
  induction q using Submodule.Quotient.induction_on with | _ x =>
  change (sectionLower ρ Y X).toSubmodule.mkQ ⟨(x : U), x.property.1⟩ = 0 at hq
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero (sectionLower ρ Y X).toSubmodule).mp hq)

/-- Exactness identifies the kernel of X/Y → U/W with the chosen chief section. -/
theorem kernelInclusion_range (hYW : Y ≤ W) :
    (kernelInclusion ρ W X Y).range = (projection ρ W X Y hYW).ker := by
  apply Subrepresentation.toSubmodule_injective
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    induction z using Submodule.Quotient.induction_on with | _ x =>
    exact (Submodule.Quotient.mk_eq_zero _).mpr x.property.2
  · intro hq
    induction q using Submodule.Quotient.induction_on with | _ x =>
    have hxW : (x : U) ∈ W := (Submodule.Quotient.mk_eq_zero _).mp hq
    exact ⟨(sectionLower ρ Y (X ⊓ W)).toSubmodule.mkQ
      ⟨x, x.property, hxW⟩, rfl⟩

/-- The actual equivariant identification of the simple kernel. -/
noncomputable def kernelEquiv (hYW : Y ≤ W) :
    ((X ⊓ W).toSubmodule ⧸ (sectionLower ρ Y (X ⊓ W)).toSubmodule) ≃ₗ[ZMod 2]
      (projection ρ W X Y hYW).ker.toSubmodule :=
  LinearEquiv.ofBijective
    ((kernelInclusion ρ W X Y).toLinearMap.codRestrict _ (by
      intro q
      rw [← kernelInclusion_range]
      exact ⟨q, rfl⟩)) (by
        constructor
        · intro q r h
          exact kernelInclusion_injective ρ W X Y (congrArg Subtype.val h)
        · intro q
          have hq : (q : X.toSubmodule ⧸ (sectionLower ρ Y X).toSubmodule) ∈
              (kernelInclusion ρ W X Y).range :=
            (kernelInclusion_range ρ W X Y hYW).ge q.property
          obtain ⟨z, hz⟩ := hq
          exact ⟨z, Subtype.ext hz⟩)

theorem kernelEquiv_equivariant (hYW : Y ≤ W) (g : H)
    (q : (X ⊓ W).toSubmodule ⧸ (sectionLower ρ Y (X ⊓ W)).toSubmodule) :
    kernelEquiv ρ W X Y hYW (sectionRepresentation ρ Y (X ⊓ W) g q) =
      (projection ρ W X Y hYW).ker.toRepresentation g (kernelEquiv ρ W X Y hYW q) := by
  apply Subtype.ext
  change kernelInclusion ρ W X Y (sectionRepresentation ρ Y (X ⊓ W) g q) =
    sectionRepresentation ρ Y X g (kernelInclusion ρ W X Y q)
  induction q using Submodule.Quotient.induction_on with | _ x => rfl

/-- The quotient by that kernel is U/W, through the first isomorphism theorem. -/
noncomputable def quotientEquiv (hYW : Y ≤ W) (hX : X ⊔ W = ⊤) :
    ((X.toSubmodule ⧸ (sectionLower ρ Y X).toSubmodule) ⧸
      (projection ρ W X Y hYW).ker.toSubmodule) ≃ₗ[ZMod 2] (U ⧸ W.toSubmodule) :=
  (projection ρ W X Y hYW).toLinearMap.quotKerEquivOfSurjective
    (projection_surjective ρ W X Y hYW hX)

theorem quotientEquiv_equivariant (hYW : Y ≤ W) (hX : X ⊔ W = ⊤) (g : H)
    (q : (X.toSubmodule ⧸ (sectionLower ρ Y X).toSubmodule) ⧸
      (projection ρ W X Y hYW).ker.toSubmodule) :
    quotientEquiv ρ W X Y hYW hX ((projection ρ W X Y hYW).ker.quotientRepresentation g q) =
      W.quotientRepresentation g (quotientEquiv ρ W X Y hYW hX q) := by
  induction q using Submodule.Quotient.induction_on with | _ q =>
  change (projection ρ W X Y hYW).toLinearMap.quotKerEquivOfSurjective _
    (Submodule.Quotient.mk (sectionRepresentation ρ Y X g q)) =
      W.quotientRepresentation g
        ((projection ρ W X Y hYW).toLinearMap.quotKerEquivOfSurjective _ (Submodule.Quotient.mk q))
  simp only [LinearMap.quotKerEquivOfSurjective_apply_mk]
  induction q using Submodule.Quotient.induction_on with | _ x => rfl

/-- The inverse image in X of a submodule of X/Y, viewed in U. -/
def lift (D : Subrepresentation (sectionRepresentation ρ Y X)) : Subrepresentation ρ where
  toSubmodule := (D.toSubmodule.comap (sectionLower ρ Y X).toSubmodule.mkQ).map
    X.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨X.toRepresentation g x, D.apply_mem_toSubmodule g hx, rfl⟩

theorem lift_le (D : Subrepresentation (sectionRepresentation ρ Y X)) :
    lift ρ X Y D ≤ X := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem mem_lift (D : Subrepresentation (sectionRepresentation ρ Y X))
    (x : X.toSubmodule) :
    (x : U) ∈ lift ρ X Y D ↔ (sectionLower ρ Y X).toSubmodule.mkQ x ∈ D := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := Subtype.ext hzx
    subst z
    exact hz
  · exact fun hx => ⟨x, hx, rfl⟩

/-- Lifting a complement to the section kernel gives exactly the local
complement required by the finite-length induction. -/
theorem lift_complement (hY : Y ≤ X ⊓ W)
    (D : Subrepresentation (sectionRepresentation ρ Y X))
    (hi : (projection ρ W X Y (hY.trans inf_le_right)).ker ⊓ D = ⊥)
    (hs : (projection ρ W X Y (hY.trans inf_le_right)).ker ⊔ D = ⊤) :
    lift ρ X Y D ≤ X ∧ lift ρ X Y D ⊔ (X ⊓ W) = X ∧
      lift ρ X Y D ⊓ (X ⊓ W) = Y := by
  let p := projection ρ W X Y (hY.trans inf_le_right)
  let q := (sectionLower ρ Y X).toSubmodule.mkQ
  refine ⟨lift_le ρ X Y D, le_antisymm (sup_le (lift_le ρ X Y D) inf_le_left) ?_, ?_⟩
  · intro x hx
    have hxq : q ⟨x, hx⟩ ∈ p.ker.toSubmodule ⊔ D.toSubmodule := by
      change q ⟨x, hx⟩ ∈ (p.ker ⊔ D).toSubmodule
      rw [hs]
      trivial
    obtain ⟨k, hk, d, hd, hkd⟩ := Submodule.mem_sup.mp hxq
    obtain ⟨z, hz⟩ := (sectionLower ρ Y X).toSubmodule.mkQ_surjective d
    have hzD : (z : U) ∈ lift ρ X Y D := (mem_lift ρ X Y D z).mpr (by rwa [hz])
    have hrem : q (⟨x, hx⟩ - z) = k := by
      rw [map_sub, hz, ← hkd, add_sub_cancel_right]
    have hremW : x - (z : U) ∈ W := by
      apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
      change p (q (⟨x, hx⟩ - z)) = 0
      rw [hrem]
      exact hk
    exact Submodule.mem_sup.mpr
      ⟨z, hzD, x - z, ⟨X.toSubmodule.sub_mem hx z.property, hremW⟩, by abel⟩
  · apply le_antisymm
    · intro x hx
      have hqD := (mem_lift ρ X Y D ⟨x, hx.2.1⟩).mp hx.1
      have hqK : q ⟨x, hx.2.1⟩ ∈ p.ker :=
        (Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr hx.2.2
      have hzero : q ⟨x, hx.2.1⟩ = 0 := by
        have hm : q ⟨x, hx.2.1⟩ ∈ p.ker ⊓ D := ⟨hqK, hqD⟩
        rw [hi] at hm
        exact hm
      exact (Submodule.Quotient.mk_eq_zero (sectionLower ρ Y X).toSubmodule).mp hzero
    · intro y hy
      refine ⟨(mem_lift ρ X Y D ⟨y, (hY hy).1⟩).mpr ?_, hY hy⟩
      have hzero : q ⟨y, (hY hy).1⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hy
      change q ⟨y, (hY hy).1⟩ ∈ D
      rw [hzero]
      exact D.toSubmodule.zero_mem

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.TwoStep
