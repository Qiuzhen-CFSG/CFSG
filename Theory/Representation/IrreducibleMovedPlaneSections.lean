module

public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# The marked moved plane on actual invariant sections

Suppose the displacement of v is an irreducible two-dimensional module for
an actor L commuting with v. On every invariant section moved by v, the
original plane embeds through the literal quotient map and is precisely the
section's moved space. The equivalence retains the original L-action.

The proof applies irreducibility twice: the upper displacement map surjects
onto the plane, and the plane's map into the section is injective. Separately,
commutator generation detects which sections v moves; passage to their actual
faithful image gives quadratic ratio at most two from an ambient rank bound.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21, printed p.924 (PDF p.941), the paragraph eliminating natural linear
modules. This does not classify the chief factors or the whole module.
-/

@[expose] public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {E V : Type*} [Group E] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) E V) (L : Subgroup E) (v : E)

/-- An actual irreducible displacement plane, with its commuting local actor. -/
structure MovedPlane where
  plane : Subrepresentation (ρ.comp L.subtype)
  moved : plane.toSubmodule = LinearMap.range (ρ v - 1)
  dimension : Module.finrank (ZMod 2) plane.toSubmodule = 2
  irreducible : IsIrreducible plane.toRepresentation
  commutes : ∀ l : L, Commute (l : E) v

variable {ρ L v}

def MovedPlane.upperMap (p : MovedPlane ρ L v) (N : Subrepresentation ρ) :
    N.toSubmodule →ₗ[ZMod 2] p.plane.toSubmodule :=
  ((ρ v - 1).comp N.toSubmodule.subtype).codRestrict _ (by
    intro n
    rw [p.moved]
    exact ⟨n, rfl⟩)

theorem MovedPlane.upperMap_equivariant (p : MovedPlane ρ L v)
    (N : Subrepresentation ρ) (l : L) (n : N.toSubmodule) :
    p.upperMap N (N.toRepresentation l n) =
      p.plane.toRepresentation l (p.upperMap N n) := by
  apply Subtype.ext
  change ρ v (ρ l n) - ρ l n = ρ l (ρ v n - n)
  rw [map_sub]
  congr 1
  exact LinearMap.congr_fun
    ((ρ.map_mul v l).symm.trans ((congrArg ρ (p.commutes l).eq.symm).trans
      (ρ.map_mul l v))) n

theorem MovedPlane.upperMap_surjective (p : MovedPlane ρ L v)
    (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w) :
    Function.Surjective (p.upperMap N) := by
  let := p.irreducible
  let f : Representation.IntertwiningMap
      (N.toRepresentation.comp L.subtype) p.plane.toRepresentation :=
    (p.upperMap N).intertwiningMap_of_isIntertwiningMap _ _
      (p.upperMap_equivariant N)
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hf | hf
  · exact hf
  · have hn' := hn
    obtain ⟨w, hw⟩ := hn'
    apply False.elim (hw ?_)
    apply (sectionRepresentation_trivial_iff ρ U N v).mpr
    intro n hn
    have he : p.upperMap N ⟨n, hn⟩ = 0 :=
      congrArg (fun t : Representation.IntertwiningMap
        (N.toRepresentation.comp L.subtype) p.plane.toRepresentation => t ⟨n, hn⟩) hf
    have hz : ρ v n - n = 0 := congrArg Subtype.val he
    rw [hz]
    exact U.toSubmodule.zero_mem

theorem MovedPlane.le_upper (p : MovedPlane ρ L v)
    (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w) :
    p.plane.toSubmodule ≤ N.toSubmodule := by
  intro x hx
  obtain ⟨n, he⟩ := p.upperMap_surjective U N hn ⟨x, hx⟩
  have he' : ρ v n - n = x := congrArg Subtype.val he
  rw [← he']
  exact N.toSubmodule.sub_mem (N.apply_mem_toSubmodule v n.property) n.property

def MovedPlane.sectionMap (p : MovedPlane ρ L v) (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w) :
    p.plane.toSubmodule →ₗ[ZMod 2]
      (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) :=
  (sectionLower ρ U N).toSubmodule.mkQ.comp (Submodule.inclusion (p.le_upper U N hn))

theorem MovedPlane.sectionMap_equivariant (p : MovedPlane ρ L v)
    (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w)
    (l : L) (x : p.plane.toSubmodule) :
    p.sectionMap U N hn (p.plane.toRepresentation l x) =
      sectionRepresentation ρ U N l (p.sectionMap U N hn x) := rfl

theorem MovedPlane.sectionMap_injective (p : MovedPlane ρ L v)
    (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w) :
    Function.Injective (p.sectionMap U N hn) := by
  let := p.irreducible
  let f : Representation.IntertwiningMap p.plane.toRepresentation
      ((sectionRepresentation ρ U N).comp L.subtype) :=
    (p.sectionMap U N hn).intertwiningMap_of_isIntertwiningMap _ _
      (p.sectionMap_equivariant U N hn)
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hf | hf
  · exact hf
  · have hn' := hn
    obtain ⟨w, hw⟩ := hn'
    apply False.elim (hw ?_)
    apply (sectionRepresentation_trivial_iff ρ U N v).mpr
    intro n hnN
    have he : p.sectionMap U N hn (p.upperMap N ⟨n, hnN⟩) = 0 :=
      congrArg (fun t : Representation.IntertwiningMap p.plane.toRepresentation
        ((sectionRepresentation ρ U N).comp L.subtype) => t (p.upperMap N ⟨n, hnN⟩)) hf
    exact (Submodule.Quotient.mk_eq_zero (sectionLower ρ U N).toSubmodule).mp he

theorem MovedPlane.range_sectionMap (p : MovedPlane ρ L v)
    (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w) :
    (p.sectionMap U N hn).range =
      LinearMap.range (sectionRepresentation ρ U N v - 1) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨n, rfl⟩ := p.upperMap_surjective U N hn x
    refine ⟨(sectionLower ρ U N).toSubmodule.mkQ n, ?_⟩
    change (sectionLower ρ U N).toSubmodule.mkQ (N.toRepresentation v n) -
      (sectionLower ρ U N).toSubmodule.mkQ n = _
    rw [← map_sub]
    rfl
  · rintro _ ⟨w, rfl⟩
    obtain ⟨n, rfl⟩ := (sectionLower ρ U N).toSubmodule.mkQ_surjective w
    refine ⟨p.upperMap N n, ?_⟩
    change _ = (sectionLower ρ U N).toSubmodule.mkQ (N.toRepresentation v n) -
      (sectionLower ρ U N).toSubmodule.mkQ n
    rw [← map_sub]
    rfl

noncomputable def MovedPlane.sectionEquiv (p : MovedPlane ρ L v)
    (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w) :
    p.plane.toSubmodule ≃ₗ[ZMod 2]
      LinearMap.range (sectionRepresentation ρ U N v - 1) :=
  (LinearEquiv.ofInjective (p.sectionMap U N hn) (p.sectionMap_injective U N hn)).trans
    (LinearEquiv.ofEq _ _ (p.range_sectionMap U N hn))

theorem MovedPlane.section_rank (p : MovedPlane ρ L v)
    (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w) :
    Module.finrank (ZMod 2)
      (LinearMap.range (sectionRepresentation ρ U N v - 1)) = 2 :=
  (p.sectionEquiv U N hn).finrank_eq.symm.trans p.dimension


theorem MovedPlane.sectionEquiv_apply (p : MovedPlane ρ L v)
    (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w) (x : p.plane.toSubmodule) :
    (p.sectionEquiv U N hn x).val = p.sectionMap U N hn x := rfl

theorem MovedPlane.sectionEquiv_equivariant (p : MovedPlane ρ L v)
    (U N : Subrepresentation ρ)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w)
    (l : L) (x : p.plane.toSubmodule) :
    (p.sectionEquiv U N hn (p.plane.toRepresentation l x)).val =
      sectionRepresentation ρ U N l (p.sectionEquiv U N hn x).val := rfl

/-- Commutator generation forces the distinguished involution to move every
section on which the component acts nontrivially. -/
theorem generator_moves_of_noncentral (σ : Representation (ZMod 2) E V)
    (K : Subgroup E) (v : E) (hgen : ⁅K, zpowers v⁆ = K)
    (hn : ¬ K ≤ σ.ker) : ∃ w, σ v w ≠ w := by
  by_contra! hz
  have hv : v ∈ σ.ker := LinearMap.ext hz
  have hA : zpowers v ≤ σ.ker := zpowers_le.mpr hv
  exact hn (hgen ▸ (commutator_mono le_rfl hA).trans (commutator_le_right K σ.ker))

/-- Pass to the faithful action image before using its quadratic ratio.
Neither component faithfulness nor component irreducibility is assumed here. -/
theorem section_image_ratio_le_two [Finite E] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) E V) (U N : Subrepresentation ρ) (v : E)
    (hv : v ^ 2 = 1)
    (hn : ∃ w, sectionRepresentation ρ U N v w ≠ w)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ v - 1)) ≤ 2) :
    quadraticRatio (imageRepresentation (sectionRepresentation ρ U N)) ≤ 2 := by
  let σ := sectionRepresentation ρ U N
  let t := actionHom σ v
  have ht2 : t ^ 2 = 1 := by
    change actionHom σ v ^ 2 = 1
    rw [← map_pow, hv, map_one]
  have ht1 : t ≠ 1 := by
    intro ht
    obtain ⟨w, hw⟩ := hn
    exact hw ((actionHom_eq_one_iff σ v).mp ht w)
  have horder : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  obtain ⟨hA, hAr, hq, _⟩ := involution_actor_rank_and_fixedCodim
    (imageRepresentation σ) t horder
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨zpowers t, hA, hq, ?_⟩
  have hcod := fixedCodim_section_le ρ U N (zpowers v)
  rw [fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at hcod
  rw [hAr, fixedCodim_zpowers_eq_displacement_rank]
  exact hcod.trans hr

end Representation.BinaryOffender
