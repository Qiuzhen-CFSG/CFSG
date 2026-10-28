module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.MarkedModule
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.InvolutionGeometry

/-!
# Ambient actor bounds for the marked J₂ module

The checked standard-pair orbit calculations identify the actual degree-100
permutation extension with Aut(J₂). Composing its inverse with the marking's
faithful action identifies the inverse image of the literal inner inclusion
with the marked J₂ subgroup. Thus its index is at most two, every noncyclic
actor meets it nontrivially, and an actor containing an outer element has rank
at most three. These are the group inputs to the semilinear exclusion in K.4.5.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.4.5,
printed p.460 / PDF p.471.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Sporadic.LeechRelated.J2.InnerInvolutionCores
namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)

private noncomputable def extensionMap : G →* Extension :=
  (extensionEquivAut_of_pair_calculations first_generator_conjugate
    second_generator_orbits).symm.toMonoidHom.comp D.ambientEmbedding

private theorem extensionMap_action (x : G) :
    extensionAction (D.extensionMap x) = D.ambientEmbedding x :=
  (extensionEquivAut_of_pair_calculations first_generator_conjugate
    second_generator_orbits).apply_symm_apply _

private theorem extensionMap_injective : Function.Injective D.extensionMap := by
  intro x y h
  apply D.ambient_injective
  simpa only [D.extensionMap_action] using congrArg extensionAction h

private theorem extensionMap_mem_inner (x : G) :
    D.extensionMap x ∈ intoExtension.range ↔ x ∈ D.inner := by
  constructor
  · rintro ⟨y,hy⟩
    have he : (D.carrierEquiv.symm y : G) = x := by
      apply D.ambient_injective
      rw [D.ambient_inner, D.carrierEquiv.apply_symm_apply]
      rw [← D.extensionMap_action, ← hy, extensionAction_inner]
    exact he ▸ (D.carrierEquiv.symm y).property
  · intro hx
    refine ⟨D.carrierEquiv ⟨x,hx⟩, extensionAction_injective ?_⟩
    rw [extensionAction_inner, D.extensionMap_action, ← D.ambient_inner]

/-- The outer rank-three bound on the literal permutation extension transports
to every marked ambient actor containing an outer element. -/
theorem outer_actor_rank (A : Subgroup G) (hA : IsElementaryTwo A)
    (i : G) (hi : i ∈ A) (ho : i ∉ D.inner) : rank A ≤ 3 := by
  let := hA.2
  have hi2 : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian i hi)
    (fun h => ho (h ▸ D.inner.one_mem))
  have h := outer_elementary_rank_le (A.map D.extensionMap)
    (IsElementaryAbelian.map _) (D.extensionMap i) (mem_map_of_mem _ hi)
    ((orderOf_injective _ D.extensionMap_injective i).trans hi2)
    (fun h => ho ((D.extensionMap_mem_inner i).mp h))
  rwa [rank_map_injective _ D.extensionMap_injective] at h

private theorem extension_inner_index : intoExtension.range.index = 2 := by
  have hc := intoExtension.range.card_mul_index
  have he : Nat.card intoExtension.range = Nat.card Carrier :=
    Nat.card_congr (MonoidHom.ofInjective
      SecondParabolic.intoExtension_injective).toEquiv.symm
  rw [he, SecondParabolic.card_carrier FirstParabolic.card_l₁,
    SecondParabolic.card_extension FirstParabolic.card_l₁] at hc
  omega

/-- The compatible faithful automorphism action forces the marked J₂ subgroup
to have index at most two. -/
theorem inner_index_le_two : D.inner.index ≤ 2 := by
  have he : intoExtension.range.comap D.extensionMap = D.inner := by
    ext x
    exact D.extensionMap_mem_inner x
  rw [← he, index_comap]
  have h := relIndex_le_of_le_right (H := intoExtension.range)
    (show D.extensionMap.range ≤ ⊤ from le_top)
    (by rw [relIndex_top_right, extension_inner_index]; decide)
  simpa only [relIndex_top_right, extension_inner_index] using h

/-- Every actor of rank greater than one meets the actual marked J₂ subgroup
nontrivially, by its index bound. -/
theorem exists_nontrivial_inner [Finite G]
    (A : Subgroup G) (hr : 1 < rank A) :
    ∃ x : D.inner, (x : G) ∈ A ∧ x ≠ 1 := by
  by_contra! hn
  have hb : D.inner.subgroupOf A = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    exact Subtype.ext (congrArg (fun z : D.inner => (z : G)) (hn ⟨x,hx⟩ x.property))
  have hle := relIndex_le_of_le_right (H := D.inner) (show A ≤ ⊤ from le_top)
    (by rw [relIndex_top_right]; exact Subgroup.FiniteIndex.index_ne_zero)
  rw [relIndex, hb, index_bot] at hle
  have hcard : Nat.card A ≤ 2 := hle.trans (by
    simpa only [relIndex_top_right] using D.inner_index_le_two)
  have hh := Nat.log_mono_right (b := 2) hcard
  change rank A ≤ Nat.log 2 2 at hh
  norm_num at hh
  omega
end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
