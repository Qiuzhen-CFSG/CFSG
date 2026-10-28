module
public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# Cubic parabolics fixed by the natural A₆ automorphisms

For every Sylow two-subgroup of A₆ the two incident parabolics have
relative index three and generate A₆. Every automorphism induced by S₆
which preserves that Sylow fixes each of these parabolics. In particular,
this includes the natural outer transpositions, not only inner automorphisms.

Two elements of the standard Sylow detect its natural normalizer. The
small finite test is checked by the kernel; conjugation then transports
the fixed parabolics to an arbitrary Sylow subgroup.

Source: Aschbacher--Smith 14.3.6(2), printed p.991, and the A₆/S₆
quadrangle of I.5, printed pp.419--422.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymmetricSix
open AlternatingSix.ShadowLocal hiding A6
namespace AlternatingSix.NaturalCubicGeneration
private def u : A6 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩
private def v : A6 := ⟨Equiv.swap 2 4 * Equiv.swap 3 5, by decide⟩
private theorem u_mem : u ∈ a6Borel := by decide
private theorem v_mem : v ∈ a6Borel := by decide
set_option maxRecDepth 10000 in
private theorem borel_test (s : S6)
    (hu : s * u.val * s⁻¹ ∈ borel) (hv : s * v.val * s⁻¹ ∈ borel) : s ∈ borel := by
  revert s
  decide +kernel
private theorem comap_fixed (s : S6) (J : Subgroup S6) (hs : s ∈ J) :
    (J.comap (alternatingGroup (Fin 6)).subtype).map (permutationAction s).toMonoidHom =
      J.comap (alternatingGroup (Fin 6)).subtype := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact J.mul_mem (J.mul_mem hs hy) (J.inv_mem hs)
  · intro x hx
    refine ⟨permutationAction s⁻¹ x, ?_, ?_⟩
    · exact J.mul_mem (J.mul_mem (J.inv_mem hs) hx) (by simpa using hs)
    · rw [map_inv]
      exact (permutationAction s).apply_symm_apply x

private theorem standard_fixed (b : MulAut A6) (hb : b ∈ natural)
    (hP : a6Borel.map b.toMonoidHom = a6Borel) :
    a6DuadStabilizer.map b.toMonoidHom = a6DuadStabilizer ∧
      a6SynthemeStabilizer.map b.toMonoidHom = a6SynthemeStabilizer := by
  obtain ⟨s,rfl⟩ := hb
  have hu : permutationAction s u ∈ a6Borel := by
    rw [← hP]
    exact mem_map_of_mem (permutationAction s).toMonoidHom u_mem
  have hv : permutationAction s v ∈ a6Borel := by
    rw [← hP]
    exact mem_map_of_mem (permutationAction s).toMonoidHom v_mem
  have hs := borel_test s hu hv
  exact ⟨comap_fixed s duadStabilizer hs.1, comap_fixed s synthemeStabilizer hs.2⟩

private theorem conjugate_transfer (J : Subgroup A6) (a b : MulAut A6) :
    (J.map (a⁻¹ * b * a).toMonoidHom).map a.toMonoidHom =
      (J.map a.toMonoidHom).map b.toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact a.apply_symm_apply _

/-- Natural automorphisms preserving a Sylow fix both cubic parabolics. -/
theorem invariant_cubic_pair (P : Sylow 2 A6) :
    ∃ J₁ J₂ : Subgroup A6,
      (P : Subgroup A6) ≤ J₁ ∧ (P : Subgroup A6) ≤ J₂ ∧
      (P : Subgroup A6).relIndex J₁ = 3 ∧ (P : Subgroup A6).relIndex J₂ = 3 ∧
      J₁ ⊔ J₂ = ⊤ ∧
      ∀ b : MulAut A6, b ∈ natural → (P : Subgroup A6).map b.toMonoidHom = P →
        J₁.map b.toMonoidHom = J₁ ∧ J₂.map b.toMonoidHom = J₂ := by
  obtain ⟨g,hg,_⟩ := a6_coatoms_over_sylow P
  let a := MulAut.conj g
  refine ⟨a.mapSubgroup a6DuadStabilizer,a.mapSubgroup a6SynthemeStabilizer,
    hg ▸ a.mapSubgroup.monotone a6Borel_le_duadStabilizer,
    hg ▸ a.mapSubgroup.monotone a6Borel_le_synthemeStabilizer,?_,?_,?_,?_⟩
  · rw [← hg]
    exact (relIndex_map_map_of_injective _ _ a.injective).trans a6Borel_relIndex_duad
  · rw [← hg]
    exact (relIndex_map_map_of_injective _ _ a.injective).trans a6Borel_relIndex_syntheme
  · rw [← a.mapSubgroup.map_sup, a6_parabolics_sup,a.mapSubgroup.map_top]
  · intro b hb hP
    have ha : a ∈ natural := inner_le_natural ⟨g,rfl⟩
    have hc : a⁻¹ * b * a ∈ natural := natural.mul_mem (natural.mul_mem (natural.inv_mem ha) hb) ha
    have hp : a6Borel.map (a⁻¹ * b * a).toMonoidHom = a6Borel := by
      apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
      rw [conjugate_transfer]
      change (a.mapSubgroup a6Borel).map b.toMonoidHom = a.mapSubgroup a6Borel
      rw [hg,hP]
    obtain ⟨h1,h2⟩ := standard_fixed _ hc hp
    constructor
    · exact (conjugate_transfer a6DuadStabilizer a b).symm.trans (congrArg (Subgroup.map a.toMonoidHom) h1)
    · exact (conjugate_transfer a6SynthemeStabilizer a b).symm.trans (congrArg (Subgroup.map a.toMonoidHom) h2)
end AlternatingSix.NaturalCubicGeneration
