module

public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.GroupTheory.FiniteParabolicTransfer

/-!
# Sylow overgroups in the derived binary symplectic model

Under the actual A₆ identification, a proper Sylow-two overgroup is either
that Sylow subgroup or maximal. The marked flag has index three in each
of its two maximal overgroups. Self-normalization and the Frattini argument
also show that every Sylow overgroup equals its prime-to-two residual.

Source: Aschbacher–Smith, E.6.8(2), printed pp.247–248, and the intrinsic
six-letter parabolic geometry of I.5, printed pp.419–422.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymmetricSix
open AlternatingSix.ShadowLocal hiding A6
namespace Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry

private theorem overgroup_standard (H : Subgroup A6) (hBH : a6Borel ≤ H)
    (hH : H ≠ ⊤) : H = a6Borel ∨ IsCoatom H := by
  have between (P : Subgroup A6) (hHP : H ≤ P)
      (hidx : a6Borel.relIndex P = 3) : H = a6Borel ∨ H = P := by
    have he := relIndex_mul_relIndex a6Borel H P hBH hHP
    have hd : a6Borel.relIndex H ∣ 3 :=
      ⟨H.relIndex P, (he.trans hidx).symm⟩
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h1 | h3
    · exact Or.inl (le_antisymm (relIndex_eq_one.mp h1) hBH)
    · have h1 : H.relIndex P = 1 := by rw [hidx, h3] at he; omega
      exact Or.inr (le_antisymm hHP (relIndex_eq_one.mp h1))
  rcases a6_overgroup_borel H hBH hH with hd | hs
  · rcases between a6DuadStabilizer hd a6Borel_relIndex_duad with he | he
    · exact Or.inl he
    · exact Or.inr (he ▸ a6DuadStabilizer_isCoatom)
  · rcases between a6SynthemeStabilizer hs a6Borel_relIndex_syntheme with he | he
    · exact Or.inl he
    · exact Or.inr (he ▸ a6SynthemeStabilizer_isCoatom)

private theorem alternating_overgroup (S : Sylow 2 A6) (H : Subgroup A6) (hSH : (S : Subgroup A6) ≤ H)
    (hH : H ≠ ⊤) : H = (S : Subgroup A6) ∨ IsCoatom H := by
  obtain ⟨g, hg, _⟩ := a6_coatoms_over_sylow S
  let e := (MulAut.conj g).mapSubgroup
  have hb : a6Borel ≤ e.symm H := by
    have hh := e.symm.monotone hSH
    rwa [← hg, e.symm_apply_apply] at hh
  have hn : e.symm H ≠ ⊤ := by
    intro he
    exact hH (e.symm.injective (he.trans e.symm.map_top.symm))
  rcases overgroup_standard (e.symm H) hb hn with he | hc
  · left
    exact (e.apply_symm_apply H).symm.trans ((congrArg e he).trans hg)
  · exact Or.inr ((e.symm.isCoatom_iff H).mp hc)

variable {X : Type*} [Group X] [Finite X]

/-- The actual alternating-six Sylow subgroup is self-normalizing. -/
theorem normalizer_sylow (e : X ≃* A6) (S : Sylow 2 X) :
    normalizer (S : Set X) = (S : Subgroup X) := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Sylow.normalizer_map_surjective S e.toMonoidHom e.surjective]
  exact sylow_normalizer_eq (S.mapSurjective e.surjective)

/-- There are no intermediate proper subgroups between the Borel and the
maximal parabolics of the derived binary group. -/
theorem sylow_overgroup_cases (e : X ≃* A6) (S : Sylow 2 X)
    (H : Subgroup X) (hSH : (S : Subgroup X) ≤ H) (hH : H ≠ ⊤) :
    H = (S : Subgroup X) ∨ IsCoatom H := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn : H.map e.toMonoidHom ≠ ⊤ := by
    intro he
    exact hH (e.mapSubgroup.injective (he.trans e.mapSubgroup.map_top.symm))
  rcases alternating_overgroup P (H.map e.toMonoidHom) (map_mono hSH) hn with he | hc
  · exact Or.inl (e.mapSubgroup.injective he)
  · exact Or.inr ((e.mapSubgroup.isCoatom_iff H).mp hc)

/-- O^{2′}(H) = H for every subgroup containing a Sylow two-subgroup.
This uses relative normality inside H and the Frattini argument. -/
theorem sylow_overgroup_residual (e : X ≃* A6) (S : Sylow 2 X)
    (H : Subgroup X) (hSH : (S : Subgroup X) ≤ H) :
    primeToResidual 2 H = ⊤ := by
  let P := S.subtype hSH
  have hp : (P : Subgroup H) ≤ primeToResidual 2 H :=
    le_primeToResidual_of_isPGroup P.isPGroup'
  have he : normalizer (P : Set H) = (P : Subgroup H) := by
    change normalizer ((S : Subgroup X).subgroupOf H : Set H) = _
    rw [← subgroupOf_normalizer_eq hSH]
    change (normalizer (S : Set X)).subgroupOf H = _
    rw [normalizer_sylow e S]
    rfl
  have hf := P.normalizer_sup_eq_top' hp
  rw [he, sup_of_le_right hp] at hf
  exact hf

end Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry
