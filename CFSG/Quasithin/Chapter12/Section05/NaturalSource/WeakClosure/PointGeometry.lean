module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Subgroups

/-!
# The literal exterior points and their two component orbits

The chosen quotient marking lifts every SL₅(2) actor to an element of the
original L. Thus the intrinsic two-orbit theorem acts on the ambient V,
with representatives z and z′ from NaturalSource.Subgroups. The binary
line V₁ has precisely the elements 1 and z, so G₁ = C_G(z). The marked
Sylow flag makes T fix z. No ambient fusion conclusion is assumed.

Source: Aschbacher--Smith, 12.5.5(2) and the setup of 12.5.9, pp.819--821.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
namespace ExteriorMarking
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (a : ExteriorMarking D)

theorem z_mem : a.z ∈ V := (a.coordinates.symm _).property

theorem zPrime_mem : a.zPrime ∈ V := (a.coordinates.symm _).property

theorem z_ne_one : a.z ≠ 1 := by
  intro h
  have he : a.coordinates.symm
      (Multiplicative.ofAdd Representation.SL5ExteriorSquare.decomposable) = 1 :=
    Subtype.ext h
  have := congrArg a.coordinates he
  simp only [MulEquiv.apply_symm_apply, map_one] at this
  exact Representation.SL5ExteriorSquare.decomposable_ne_zero
    (congrArg Multiplicative.toAdd this)

theorem zPrime_ne_one : a.zPrime ≠ 1 := by
  intro h
  have he : a.coordinates.symm
      (Multiplicative.ofAdd Representation.SL5ExteriorSquare.nondecomposable) = 1 :=
    Subtype.ext h
  have := congrArg a.coordinates he
  simp only [MulEquiv.apply_symm_apply, map_one] at this
  exact Representation.SL5ExteriorSquare.nondecomposable_ne_zero
    (congrArg Multiplicative.toAdd this)

theorem mem_V₁ (x : G) : x ∈ a.Vi 1 ↔ x = 1 ∨ x = a.z := by
  constructor
  · intro hx
    have hxV : x ∈ V := a.subspace_le _ hx
    have h := (a.mem_subspace Representation.SL5ExteriorSquare.V₁ ⟨x, hxV⟩).mp hx
    rw [Representation.SL5ExteriorSquare.V₁_eq_decomposablePoint,
      Representation.SL5ExteriorSquare.mem_binaryPoint] at h
    rcases h with h | h
    · left
      have he : a.coordinates ⟨x, hxV⟩ = 1 := congrArg Multiplicative.ofAdd h
      exact congrArg Subtype.val (a.coordinates.injective (he.trans a.coordinates.map_one.symm))
    · right
      have he := congrArg a.coordinates.symm (congrArg Multiplicative.ofAdd h)
      exact congrArg Subtype.val ((a.coordinates.symm_apply_apply ⟨x, hxV⟩).symm.trans he)
  · rintro (rfl | rfl)
    · exact (a.Vi 1).one_mem
    · apply (a.mem_subspace Representation.SL5ExteriorSquare.V₁
        (a.coordinates.symm (Multiplicative.ofAdd Representation.SL5ExteriorSquare.decomposable))).mpr
      simp only [MulEquiv.apply_symm_apply]
      rw [Representation.SL5ExteriorSquare.V₁_eq_decomposablePoint]
      exact Submodule.mem_span_singleton_self _

theorem z_mem_V₁ : a.z ∈ a.Vi 1 := (a.mem_V₁ _).mpr (Or.inr rfl)

theorem card_V₁ : Nat.card (a.Vi 1) = 2 := by
  apply (Nat.card_eq_two_iff' (1 : a.Vi 1)).mpr
  refine ⟨⟨a.z, a.z_mem_V₁⟩, ?_, ?_⟩
  · exact fun h => a.z_ne_one (congrArg Subtype.val h)
  · intro y hy
    apply Subtype.ext
    exact (a.mem_V₁ y).mp y.property |>.resolve_left (fun h => hy (Subtype.ext h))

theorem Gi_one_eq_centralizer : a.Gi 1 = centralizer ({a.z} : Set G) := by
  apply le_antisymm
  · intro g hg
    have hz := (mem_normalizer_iff.mp hg a.z).mp a.z_mem_V₁
    rcases (a.mem_V₁ _).mp hz with hz | hz
    · have he : MulAut.conj g a.z = 1 := hz
      exact (a.z_ne_one ((MulAut.conj g).injective
        (he.trans (map_one (MulAut.conj g)).symm))).elim
    · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hz)
  · intro g hg
    apply centralizer_le_normalizer (a.Vi 1 : Set G)
    apply mem_centralizer_iff.mpr
    intro x hx
    rcases (a.mem_V₁ x).mp hx with rfl | rfl
    · simp
    · exact (mem_centralizer_singleton_iff.mp hg).symm

theorem V₁_le_V₆ : a.Vi 1 ≤ a.Vi 6 := by
  apply a.subspace_mono
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_singleton] at hi
  subst i
  decide

theorem V₆_ne_bot : a.Vi 6 ≠ ⊥ := by
  intro he
  exact a.z_ne_one (mem_bot.mp (he ▸ (a.V₁_le_V₆ a.z_mem_V₁)))

/-- Lift the actual quotient actor, preserving the original conjugation convention. -/
theorem exists_conjugator_of_coordinate_orbit (v w : V)
    (horbit : Representation.SL5ExteriorSquare.InExteriorOrbit
      (a.coordinates v).toAdd (a.coordinates w).toAdd) :
    ∃ l ∈ L, MulAut.conj l (v : G) = (w : G) := by
  obtain ⟨g, hg⟩ := horbit
  obtain ⟨q, hq⟩ := a.quotientEquiv.surjective g
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  refine ⟨l, l.property, ?_⟩
  have he := a.equivariant l v
  rw [hl, hq, hg] at he
  exact congrArg Subtype.val (a.coordinates.injective he)

theorem point_orbits (x : G) (hx : x ∈ V) (hne : x ≠ 1) :
    (∃ l ∈ L, MulAut.conj l a.z = x) ∨
      (∃ l ∈ L, MulAut.conj l a.zPrime = x) := by
  let v : V := ⟨x, hx⟩
  have hv : (a.coordinates v).toAdd ≠ 0 := by
    intro he
    have hc : a.coordinates v = 1 := congrArg Multiplicative.ofAdd he
    exact hne (congrArg Subtype.val
      (a.coordinates.injective (hc.trans a.coordinates.map_one.symm)))
  rcases Representation.SL5ExteriorSquare.exterior_orbits_exactly_one
    (a.coordinates v).toAdd hv with h | h
  · left
    apply a.exists_conjugator_of_coordinate_orbit
      (a.coordinates.symm (Multiplicative.ofAdd Representation.SL5ExteriorSquare.decomposable)) v
    simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using h.1
  · right
    apply a.exists_conjugator_of_coordinate_orbit
      (a.coordinates.symm (Multiplicative.ofAdd Representation.SL5ExteriorSquare.nondecomposable)) v
    simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using h.1

end ExteriorMarking

namespace SylowExteriorMarking
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (s : SylowExteriorMarking D)

theorem sylow_normalizes_subspace
    (W : Submodule (ZMod 2) Representation.SL5ExteriorSquare.V)
    (hW : Representation.SL5ExteriorSquare.flagGroup ≤
      Representation.SL5ExteriorSquare.exteriorStabilizer W) :
    (T : Subgroup G) ≤ normalizer (s.marking.subspace W : Set G) := by
  apply le_normalizer_iff.mpr
  intro t ht x hx
  have hxV := s.marking.subspace_le W hx
  let v : V := ⟨x, hxV⟩
  let h : (L ⊔ (T : Subgroup G) : Subgroup G) :=
    ⟨t, (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) ht⟩
  have hv := (s.marking.mem_subspace W v).mp hx
  apply (s.marking.mem_subspace W
    ⟨t * x * t⁻¹, (mem_normalizer_iff.mp (s.normalizes h.property) x).mp hxV⟩).mpr
  rw [s.equivariant h v]
  exact (hW (s.sylow_flag ⟨t, ht⟩) _).mpr hv

theorem sylow_le_G₁ : (T : Subgroup G) ≤ s.marking.Gi 1 :=
  s.sylow_normalizes_subspace _
    Representation.SL5ExteriorSquare.flagGroup_stabilizes_standard.1

theorem sylow_centralizes_z : (T : Subgroup G) ≤ centralizer ({s.marking.z} : Set G) := by
  rw [← s.marking.Gi_one_eq_centralizer]
  exact s.sylow_le_G₁

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
