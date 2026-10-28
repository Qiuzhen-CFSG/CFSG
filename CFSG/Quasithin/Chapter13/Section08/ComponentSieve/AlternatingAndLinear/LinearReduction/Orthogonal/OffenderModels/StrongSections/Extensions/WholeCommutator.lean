module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Extensions.PerfectCover

/-!
# Whole-group commutators in the orthogonal extension step

Let U = [U,K], with K marked as A₈ inside H ≃ S₈, and let U/W be the marked
natural module. Quotienting by J = [W,K] gives a perfect central cover of U/W.
Its kernel W/J has dimension at most one, hence the whole H fixes it over F₂.
Consequently [W,H] = [W,K]. The proof constructs J as an H-subrepresentation;
normality is relative to H and is proved from the component marking.

The ambient generation hypothesis is the earlier source conclusion about
Ũ_H; a flag of K-central factors in W alone does not supply it. This module
proves the linear deduction for that actual representation when the source
setup supplies the stated inputs. It does not assert the earlier source setup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.21–25 (printed pp.956–960), especially
13.8.25, printed p.960, PDF p.977.
-/

@[expose] public section

open Representation Representation.BinaryOffender Representation.OneCohomology BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.Extensions
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

omit [FiniteDimensional (ZMod 2) U] in
private lemma quotient_generated (ρ : Representation (ZMod 2) H U)
    (K : Subgroup H) (hgen : subspaceCommutator ρ ⊤ K = ⊤) (J : Subrepresentation ρ) :
    subspaceCommutator J.quotientRepresentation ⊤ K = ⊤ := by
  have hle : subspaceCommutator ρ ⊤ K ≤
      (subspaceCommutator J.quotientRepresentation ⊤ K).comap J.toSubmodule.mkQ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, u, _, rfl⟩
    change J.toSubmodule.mkQ (ρ k u - u) ∈ subspaceCommutator J.quotientRepresentation ⊤ K
    rw [map_sub]
    exact Submodule.subset_span ⟨k, hk, J.toSubmodule.mkQ u, Submodule.mem_top, rfl⟩
  apply top_unique
  intro v _
  obtain ⟨u, rfl⟩ := J.toSubmodule.mkQ_surjective v
  apply hle
  rw [hgen]
  trivial

/-- The earlier equality U = [U,K] forces H to centralize W/[W,K]
when U/W is the marked natural module. Thus the two commutators coincide.
The generation hypothesis concerns U, not just a flag in W. -/
private lemma whole_commutator_eq_component_aux (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤)
    (J : Subrepresentation ρ)
    (hJ : J.toSubmodule = subspaceCommutator ρ W.toSubmodule K) :
    subspaceCommutator ρ W.toSubmodule ⊤ = subspaceCommutator ρ W.toSubmodule K := by
  obtain ⟨e, he⟩ := hQ
  have hJW : J ≤ W := by
    change J.toSubmodule ≤ W.toSubmodule
    rw [hJ]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, _, u, hu, rfl⟩
    exact W.toSubmodule.sub_mem (W.apply_mem_toSubmodule k hu) hu
  let q : U →ₗ[ZMod 2] natural (Fin 8) := e.toLinearMap.comp W.toSubmodule.mkQ
  have hq (u : U) : q u = 0 ↔ u ∈ W.toSubmodule := by
    change e (W.toSubmodule.mkQ u) = 0 ↔ _
    rw [e.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  let p : (U ⧸ J.toSubmodule) →ₗ[ZMod 2] natural (Fin 8) :=
    J.toSubmodule.liftQ q (fun u hu => (hq u).mpr (hJW hu))
  have hp (g : H) (v : U ⧸ J.toSubmodule) :
      p (J.quotientRepresentation g v) = naturalRepresentation (Fin 8) (eH g) (p v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ u => exact he g (W.toSubmodule.mkQ u)
  have hsur : Function.Surjective p := by
    intro v
    obtain ⟨u, hu⟩ := W.toSubmodule.mkQ_surjective (e.symm v)
    refine ⟨J.toSubmodule.mkQ u, ?_⟩
    change e (W.toSubmodule.mkQ u) = v
    rw [hu, e.apply_symm_apply]
  have hker : p.ker ≤ fixedSpace J.quotientRepresentation K := by
    intro v hv
    induction v using Submodule.Quotient.induction_on with
    | _ u =>
      have hu : u ∈ W.toSubmodule := (hq u).mp hv
      intro k
      apply (Submodule.Quotient.eq J.toSubmodule).mpr
      rw [hJ]
      exact Submodule.subset_span ⟨k, k.property, u, hu, rfl⟩
  have hfix := (central_cover_kernel_control J.quotientRepresentation eH K hK p hp hsur hker
    (quotient_generated ρ K hgen J)).2
  apply le_antisymm
  · rw [← hJ]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, w, hw, rfl⟩
    have hwk : J.toSubmodule.mkQ w ∈ p.ker := (hq w).mpr hw
    exact (Submodule.Quotient.eq J.toSubmodule).mp (hfix hwk ⟨g, Subgroup.mem_top g⟩)
  · apply Submodule.span_mono
    rintro _ ⟨k, _, w, hw, rfl⟩
    exact ⟨k, Subgroup.mem_top k, w, hw, rfl⟩

omit [FiniteDimensional (ZMod 2) U] in
private lemma component_normal (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) : K.Normal := by
  have he : K = (alternatingGroup (Fin 8)).comap eH.toMonoidHom := by
    ext k
    change k ∈ K ↔ eH k ∈ alternatingGroup (Fin 8)
    rw [← hK]
    exact (Subgroup.mem_map_iff_mem eH.injective).symm
  rw [he]
  infer_instance

omit [FiniteDimensional (ZMod 2) U] in
/-- The action-commutator span is a literal H-subrepresentation. -/
def componentCommutator (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) : Subrepresentation ρ where
  toSubmodule := subspaceCommutator ρ W.toSubmodule K
  apply_mem_toSubmodule g v hv := by
    let : K.Normal := component_normal eH K hK
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, hk, u, hu, rfl⟩ := hv
      have he : ρ g (ρ k u - u) = ρ (g * k * g⁻¹) (ρ g u) - ρ g u := by
        rw [map_sub]
        congr 1
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      rw [he]
      exact Submodule.subset_span ⟨g * k * g⁻¹, Subgroup.Normal.conj_mem ‹_› k hk g,
        ρ g u, W.apply_mem_toSubmodule g hu, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa using (subspaceCommutator ρ W.toSubmodule K).add_mem ihx ihy
    | smul c x hx ih => simpa using (subspaceCommutator ρ W.toSubmodule K).smul_mem c ih

/-- Whole-group commutators equal component commutators under the genuine
ambient generation hypothesis and the marked natural quotient. -/
lemma whole_commutator_eq_component (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) :
    subspaceCommutator ρ W.toSubmodule ⊤ = subspaceCommutator ρ W.toSubmodule K :=
  whole_commutator_eq_component_aux ρ W eH K hK hQ hgen
    (componentCommutator ρ W eH K hK) rfl


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.Extensions
