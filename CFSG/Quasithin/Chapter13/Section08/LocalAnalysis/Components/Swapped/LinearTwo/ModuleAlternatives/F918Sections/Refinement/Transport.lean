module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.Filtering
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.MarkingTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.CrossFixation

/-!
# From the hatted constituent to the canonical factor spaces

For H = K₀T, the ambient orbit of a K₀-invariant section is its T-orbit.
The complete source split clauses lift its central-image identity to
I_H = I + Iᵗ. Cross-factor fixation then identifies I with [I_H,K].
The actual conjugation operator identifies the other canonical commutator
space, and CrossFixation supplies fixation in both directions.

The hypothesis that the ambient orbit is the full module is explicit;
the source assembly constructs it on Ũ_H. No direct sum of the original
spaces or splitting of a central extension is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.18(5iiia), printed p.325, and 13.8.16(1b1), p.952 (PDF p.969).
-/

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open Cases Cases.Exchanged Cases.Exchanged.PairCoordinates
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement
@[expose] public noncomputable section
variable {D E V X : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]
  (ρ : Representation (ZMod 2) D V) {K K₀ T : Subgroup D}
  {I : Submodule (ZMod 2) V}

theorem ambient_orbit_eq (hi : IsIrrPlusWith ρ K₀ T I) (hgen : K₀ ⊔ T = ⊤) :
    orbitSpan ρ ⊤ I = orbitSpan ρ T I := by
  apply le_antisymm _ (orbitSpan_mono_actor ρ le_top I)
  apply orbitSpan_le ρ (le_orbitSpan ρ T I)
  rw [← hgen]
  exact sup_le (orbitSpan_component_invariant ρ hi.normalizes hi.isIrrPlus)
    (orbitSpan_invariant ρ T I)

theorem conjugation_intertwines (t : D) (g : D) (v : V) :
    operator ρ t (ρ g v) = ρ ((MulAut.conj t) g) (operator ρ t v) := by
  change ρ t (ρ g v) = ρ (t * g * t⁻¹) (ρ t v)
  simp only [map_mul, Module.End.mul_apply, inv_self_apply]

theorem right_conjugate_moved (t : D) :
    rightConjugate ρ (subspaceCommutator ρ ⊤ K) t =
      subspaceCommutator ρ ⊤ (K.conjBy t⁻¹) :=
  moved_map_automorphism ρ (MulAut.conj t⁻¹) (operator ρ t⁻¹)
    (conjugation_intertwines ρ t⁻¹) K

theorem canonical_spaces {t : D} (p : ProductMarking K K₀ t)
    (hi : IsIrrPlusWith ρ K₀ T I) (hgen : K₀ ⊔ T = ⊤)
    (hfull : orbitSpan ρ ⊤ I = ⊤)
    (hN : K₀ ≤ normalizer (K : Set D))
    (split : FiveSplit ρ K K₀ T I t)
    (first : (subspaceCommutator ρ (orbitSpan ρ ⊤ I) K).map (fixedSpace ρ K₀).mkQ =
      I.map (fixedSpace ρ K₀).mkQ) :
    subspaceCommutator ρ ⊤ K = I ∧
      subspaceCommutator ρ ⊤ (K.conjBy t⁻¹) = rightConjugate ρ I t ∧
      subspaceCommutator ρ ⊤ K ⊔ subspaceCommutator ρ ⊤ (K.conjBy t⁻¹) = ⊤ ∧
      subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ (K.conjBy t⁻¹) ∧
      subspaceCommutator ρ ⊤ (K.conjBy t⁻¹) ≤ fixedSpace ρ K := by
  obtain ⟨horbit, hcross⟩ := split.literal ρ hi hN first
  have hsum : I ⊔ rightConjugate ρ I t = ⊤ := by
    rw [← horbit, ← ambient_orbit_eq ρ hi hgen, hfull]
  have hIK : subspaceCommutator ρ ⊤ K = I := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, v, _, rfl⟩
      have hv : v ∈ I ⊔ rightConjugate ρ I t := hsum ▸ Submodule.mem_top
      obtain ⟨i, hi', w, ⟨j, hj, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
      have hf := p.conjugate_fixed_first ρ hcross ⟨j, hj⟩ ⟨k, hk⟩
      change ρ k (ρ t⁻¹ j) = ρ t⁻¹ j at hf
      rw [map_add, hf, add_sub_add_right_eq_sub]
      exact I.sub_mem ((hi.invariant (p.le hk) i).2 hi') hi'
    · simpa only [hfull] using le_component_commutator_of_image ρ hi.isIrrPlus
        (le_top : K₀ ≤ ⊤) hN first.symm.le
  have hJK : subspaceCommutator ρ ⊤ (K.conjBy t⁻¹) = rightConjugate ρ I t := by
    rw [← right_conjugate_moved ρ t, hIK]
  have hcentral : subspaceCommutator ρ ⊤ K = fixedSpace ρ (K.conjBy t⁻¹) := by
    simpa only [hfull, top_inf_eq] using split.centralizer
  have hreturn : (K.conjBy t⁻¹).map (MulAut.conj t⁻¹).toMonoidHom = K := by
    change (K.conjBy t⁻¹).conjBy t⁻¹ = K
    rw [← p.return_eq, conjBy_conjBy]
    simp only [inv_mul_cancel, Subgroup.conjBy, map_one]
    exact Subgroup.map_id K
  refine ⟨hIK, hJK, ?_, ?_⟩
  · rw [hIK, hJK, hsum]
  · exact canonical_cross_fixation ρ K (K.conjBy t⁻¹) (MulAut.conj t⁻¹)
      (operator ρ t⁻¹) (conjugation_intertwines ρ t⁻¹) rfl hreturn hcentral.le

def changeCentralSpace {J : Submodule (ZMod 2) V}
    {hI : K ≤ subspaceStabilizer ρ I} {σ : Representation (ZMod 2) E X}
    (d : CentralQuotientIdentification ρ K I hI σ) (h : I = J)
    (hJ : K ≤ subspaceStabilizer ρ J) : CentralQuotientIdentification ρ K J hJ σ := by
  subst J
  exact d

end
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement
