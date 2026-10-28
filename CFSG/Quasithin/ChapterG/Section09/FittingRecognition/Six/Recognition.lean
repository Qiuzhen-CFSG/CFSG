module

public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Models
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Centralizers
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.BinaryAction.Centralizer
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Applying the extraspecial normalizer calculation in degree six

Coordinates identifying the actual three-core with the binary Heisenberg
image make that core self-centralizing. Thus the generalized Fitting subgroup
is the three-core, discharging the source hypothesis of A.1.31(1). The actual
SQTK cover then supplies cyclic centralizers for nontrivial two-subgroups.
For the final Sylow-three exclusion, the stronger local application controls
every three-subgroup centralized by an involution moving the core; this does
not require that three-subgroup to lie in the core.

The second part constructs the marked model realization from containment of
the represented group in the concrete linear interval, including a change
of coordinates by conjugation. The final assembly is conditional on the
separate core reduction, Heisenberg module comparison and normalizer placement
proofs; none of these recognition conclusions is asserted here.

Source: Aschbacher--Smith, G.9.4(5), printed p.355 (PDF p.366).
-/

@[expose] public section

open Representation Subgroup

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six

universe u v

open Representation.RankTwo.ExtraspecialModel

local notation "W" => BinaryAction.V
local notation "GL" => (W ≃ₗ[ZMod 2] W)

variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The original action in specified coordinates on the concrete binary space. -/
def coordinateAction (ρ : Representation (ZMod 2) G V) (f : V ≃ₗ[ZMod 2] W) :
    G →* GL :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv f).toMonoidHom.comp ρ.asGroupHom)

theorem coordinateAction_apply (ρ : Representation (ZMod 2) G V)
    (f : V ≃ₗ[ZMod 2] W) (g : G) (v : W) :
    coordinateAction ρ f g v = f (ρ g (f.symm v)) := rfl

theorem coordinateAction_injective {ρ : Representation (ZMod 2) G V}
    (hf : Function.Injective ρ) (f : V ≃ₗ[ZMod 2] W) :
    Function.Injective (coordinateAction ρ f) := by
  intro g k he
  apply hf
  apply LinearMap.ext
  intro v
  apply f.injective
  simpa only [coordinateAction_apply, f.symm_apply_apply] using
    LinearEquiv.congr_fun he (f v)

/-- Literal coordinates for the three-core; no overgroup recognition is included. -/
def CoreCoordinates (ρ : Representation (ZMod 2) G V) : Prop :=
  ∃ f : V ≃ₗ[ZMod 2] W,
    (pCore 3 G).map (coordinateAction ρ f) = BinaryAction.heisenbergImage

/-- A group identification of the core and an actual module intertwiner give
the literal image equality required by the normalizer calculation. -/
theorem coreCoordinates_of_heisenberg_intertwining
    {ρ : Representation (ZMod 2) G V}
    (e : pCore 3 G ≃* P) (f : V ≃ₗ[ZMod 2] W)
    (hf : ∀ (p : pCore 3 G) v,
      f (ρ p v) = BinaryAction.heisenberg (e p) (f v)) : CoreCoordinates ρ := by
  refine ⟨f, ?_⟩
  have he (p : pCore 3 G) :
      coordinateAction ρ f p = BinaryAction.heisenberg (e p) := by
    apply LinearEquiv.ext
    intro v
    rw [coordinateAction_apply, hf, f.apply_symm_apply]
  rw [BinaryAction.heisenbergImage_eq_range]
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨e ⟨p, hp⟩, (he ⟨p, hp⟩).symm⟩
  · rintro _ ⟨p, rfl⟩
    refine ⟨e.symm p, (e.symm p).property, ?_⟩
    rw [he, e.apply_symm_apply]

/-- The concrete centralizer calculation transfers through any faithful image. -/
theorem threeCore_selfCentralizing_of_image (φ : G →* GL)
    (hφ : Function.Injective φ)
    (hB : (pCore 3 G).map φ = BinaryAction.heisenbergImage) :
    centralizer (pCore 3 G : Set G) ≤ pCore 3 G := by
  intro x hx
  have hx' : φ x ∈ centralizer (BinaryAction.heisenbergImage : Set GL) := by
    rw [← hB]
    exact map_centralizer_le_centralizer_image (pCore 3 G : Set G) φ
      (mem_map_of_mem φ hx)
  have hm := BinaryAction.centralizer_heisenbergImage_le hx'
  rw [← hB] at hm
  obtain ⟨b, hb, he⟩ := hm
  exact hφ he ▸ hb

/-- This proves, rather than assumes, the generalized-Fitting premise used by
the source cyclic-centralizer theorem. -/
theorem generalizedFitting_eq_threeCore_of_image [Finite G] (φ : G →* GL)
    (hφ : Function.Injective φ)
    (hB : (pCore 3 G).map φ = BinaryAction.heisenbergImage) :
    Theory.GroupTheory.generalizedFitting G = pCore 3 G :=
  Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 3
    (threeCore_selfCentralizing_of_image φ hφ hB)

/-- Application to the original SQTK covering map in G.9.4. -/
theorem cyclic_threeCore_centralizers_of_image [Finite G]
    [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
    {A : Subgroup G} {m : ℕ} (h : FittingHypothesis K ρ A m)
    (φ : G →* GL) (hφ : Function.Injective φ)
    (hB : (pCore 3 G).map φ = BinaryAction.heisenbergImage)
    (T : Subgroup G) (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    IsCyclic (pCore 3 G ⊓ centralizer (T : Set G) : Subgroup G) :=
  cyclic_threeCore_centralizer h
    (generalizedFitting_eq_threeCore_of_image φ hφ hB) T hT hne

/-- The last source exclusion concerns a subgroup of a Sylow three-group,
which need not lie in the three-core. A.1.31 must therefore be applied to the
local subgroup generated by that subgroup, the core, and the involution. -/
theorem cyclic_threeSubgroup_in_involution_centralizer [Finite G]
    [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
    {A : Subgroup G} {m : ℕ} (h : FittingHypothesis K ρ A m)
    (t : G) (ht : orderOf t = 2)
    (htB : t ∉ centralizer (pCore 3 G : Set G))
    (R : Subgroup G) (hR : IsPGroup 3 R)
    (hRt : R ≤ centralizer ({t} : Set G)) : IsCyclic R := by
  obtain ⟨c⟩ := h.quotient
  exact Theory.GroupTheory.cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
    (by decide : Odd 3) c.projection c.surjective
    (c.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
    (pCore 3 G) pCore_isPGroup t ht htB R hR hRt

/-- Recover the actual marked semidirect-product subgroup and its action from
an injective representation with image in the concrete linear interval. -/
theorem extraspecialRealization_of_linear_image
    {ρ : Representation (ZMod 2) G V}
    (φ : G →* GL) (hφ : Function.Injective φ)
    (f : V ≃ₗ[ZMod 2] W)
    (hf : ∀ g v, f (ρ g v) = φ g (f v))
    (hlo : BinaryAction.fourImage ≤ φ.range)
    (hhi : φ.range ≤ BinaryAction.binaryImage) : ExtraspecialRealization ρ := by
  let e := MonoidHom.ofInjective hφ
  let d := BinaryAction.subgroupEquiv φ.range hhi
  refine ⟨φ.range.comap BinaryAction.linearAction,
    BinaryAction.fourExtension_le_comap φ.range hlo, e.trans d.symm, f, ?_⟩
  intro g v
  have he := BinaryAction.subgroupEquiv_apply φ.range hhi (d.symm (e g))
  change (d (d.symm (e g)) : GL) = BinaryAction.linearAction (d.symm (e g)) at he
  rw [d.apply_symm_apply] at he
  change f (ρ g v) = BinaryAction.linearAction (d.symm (e g)) (f v)
  rw [← he]
  exact hf g v

/-- Conjugating the represented subgroup changes the module coordinates by
the same linear automorphism. Both changes are explicit in the realization. -/
theorem extraspecialRealization_of_conjugate_image
    {ρ : Representation (ZMod 2) G V}
    (φ : G →* GL) (hφ : Function.Injective φ)
    (f : V ≃ₗ[ZMod 2] W)
    (hf : ∀ g v, f (ρ g v) = φ g (f v))
    (c : GL)
    (hlo : BinaryAction.fourImage ≤ φ.range.map (MulAut.conj c).toMonoidHom)
    (hhi : φ.range.map (MulAut.conj c).toMonoidHom ≤ BinaryAction.binaryImage) :
    ExtraspecialRealization ρ := by
  let ψ := (MulAut.conj c).toMonoidHom.comp φ
  have hr : ψ.range = φ.range.map (MulAut.conj c).toMonoidHom :=
    MonoidHom.range_comp _ _
  apply extraspecialRealization_of_linear_image ψ
    ((MulAut.conj c).injective.comp hφ) (f.trans c)
  · intro g v
    change c (f (ρ g v)) = (c * φ g * c⁻¹) (c (f v))
    rw [hf]
    change c (φ g (f v)) = c (φ g (c.symm (c (f v))))
    rw [c.symm_apply_apply]
  · rwa [hr]
  · rwa [hr]

/-- The remaining concrete normalizer calculation. Its hypotheses are the
literal three-core image, the rank-two actor, and the cyclic-centralizer
restriction. It is a separate proof obligation, not a supplied model record. -/
def MarkedNormalizerPlacement : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (φ : D →* GL) (E : Subgroup D),
    Function.Injective φ →
    (pCore 3 D).map φ = BinaryAction.heisenbergImage →
    IsElementaryAbelian 2 E → Nat.card E = 4 →
    (∀ t : D, orderOf t = 2 → t ∉ centralizer (pCore 3 D : Set D) →
      ∀ R : Subgroup D, IsPGroup 3 R → R ≤ centralizer ({t} : Set D) → IsCyclic R) →
    ∃ c : GL,
      BinaryAction.fourImage ≤ φ.range.map (MulAut.conj c).toMonoidHom ∧
      φ.range.map (MulAut.conj c).toMonoidHom ≤ BinaryAction.binaryImage

/-- Final transport and A.1.31 application, conditional on the independent
core coordinates and the genuine concrete normalizer-placement theorem. -/
theorem extraspecialRealization_of_coreCoordinates [Finite G]
    [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2) (hcoords : CoreCoordinates ρ)
    (hnorm : MarkedNormalizerPlacement.{u}) : ExtraspecialRealization ρ := by
  obtain ⟨f, hB⟩ := hcoords
  have hf := coordinateAction_injective h.faithful f
  obtain ⟨c, hlo, hhi⟩ := hnorm G (coordinateAction ρ f) A hf hB
    h.elementary h.card_actor (cyclic_threeSubgroup_in_involution_centralizer h)
  apply extraspecialRealization_of_conjugate_image (coordinateAction ρ f) hf f
    (fun g v => ?_) c hlo hhi
  simp only [coordinateAction_apply, f.symm_apply_apply]

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
