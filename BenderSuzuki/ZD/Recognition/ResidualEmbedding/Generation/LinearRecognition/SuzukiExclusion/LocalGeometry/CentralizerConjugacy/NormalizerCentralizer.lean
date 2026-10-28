module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Borel
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.CentralizerConjugacy.RootFixer

/-!
# Centralizing the marked center in the ambient normalizer

Transport the pointwise-fixer theorem through the same matrix equivalence
that identifies the Borel, P and A. If x normalizes L and centralizes A,
its induced automorphism is conjugation by p in P, hence p⁻¹x lies in J.
Conversely P centralizes its center A and J centralizes all of L.

Source: GLS4, Chapter 2, Lemma 14.3(a), first equality, using Chapter 4,
Lemma 3.6(c). No Sylow configuration or centralizer embedding is needed
for this equality.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup PFAppendixIII BenderSuzuki.MatrixGroups
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

public theorem Context.centralizer_in_normalizer :
    ((normalizer (residualGenerated M z t : Set G) ⊓
      centralizer (closure (Z ∩ (M : Set G)) : Set G) : Subgroup G) : Set G) =
      (borelTwoCore M z t : Set G) * (centralizer (residualGenerated M z t : Set G) : Set G) := by
  let L := residualGenerated M z t
  let P := borelTwoCore M z t
  let A := closure (Z ∩ (M : Set G))
  obtain ⟨f, _, hP, hA⟩ := d.borel_marking
  let φ := L.subtype.comp f.toMonoidHom
  change (SuzukiRootSubgroup m).map φ = P at hP
  rw [suzukiRootSubgroup_omega_eq_center m d.parameter_pos] at hA
  change ((center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype).map φ = A at hA
  have hPL : P ≤ L := by
    rw [← hP]
    rintro _ ⟨b, _, rfl⟩
    exact (f b).property
  have hAP : A ≤ P := by
    rw [← hA, ← hP]
    exact map_mono (map_subtype_le _)
  have hPC : P ≤ centralizer (A : Set G) := by
    intro p hp a ha
    change a ∈ closure (Z ∩ (M : Set G)) at ha
    rw [← d.borelTwoCore_center] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    exact (congrArg P.subtype (mem_center_iff.mp ha ⟨p, hp⟩)).symm
  ext x
  constructor
  · rintro ⟨hxN, hxC⟩
    let α : MulAut L := L.normalizerMonoidHom ⟨x, hxN⟩
    let β : MulAut (SuzukiMatrixGroup m) := (f.trans α).trans f.symm
    have hfix : ∀ b ∈ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype,
        β b = b := by
      intro b hb
      apply f.injective
      apply Subtype.ext
      change (f (f.symm (α (f b))) : G) = (f b : G)
      rw [f.apply_symm_apply]
      change x * φ b * x⁻¹ = φ b
      have hbA : φ b ∈ A := hA ▸ mem_map_of_mem φ hb
      rw [← hxC _ hbA, mul_inv_cancel_right]
    obtain ⟨b, hb, hβ⟩ := suzuki_aut_fixing_root_center_inner m d.parameter_pos β hfix
    have he (l : L) : x * (l : G) * x⁻¹ = φ b * (l : G) * (φ b)⁻¹ := by
      have hh := congrArg (fun a : MulAut (SuzukiMatrixGroup m) => φ (a (f.symm l))) hβ
      simpa only [β, α, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.subtype_apply, MulEquiv.trans_apply, f.apply_symm_apply, φ, MonoidHom.comp_apply,
        MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
        map_mul, map_inv] using hh
    refine Set.mem_mul.mpr ⟨φ b, (show φ b ∈ P from hP ▸ mem_map_of_mem φ hb), (φ b)⁻¹ * x, ?_, by group⟩
    intro l hl
    calc
      l * ((φ b)⁻¹ * x) = (φ b)⁻¹ * (φ b * l * (φ b)⁻¹) * x := by group
      _ = (φ b)⁻¹ * (x * l * x⁻¹) * x := by rw [he ⟨l, hl⟩]
      _ = ((φ b)⁻¹ * x) * l := by group
  · rintro ⟨p, hp, j, hj, rfl⟩
    exact ⟨(normalizer (L : Set G)).mul_mem (L.le_normalizer (hPL hp))
      (Subgroup.centralizer_le_normalizer _ hj),
      (centralizer (A : Set G)).mul_mem (hPC hp) ((centralizer_le (hAP.trans hPL)) hj)⟩
end BenderSuzuki.ZD.SuzukiExclusion
