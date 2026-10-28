module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import Theory.Representation.DualCommutator
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.PlaneTransport

/-!
# Commutators inside a marked binary plane radical

A subgroup of the radical of a two-plane displaces the natural four-space
into that plane. On the contragredient, its displacements lie in the
annihilator plane. Thus if a subgroup has commutator dimension greater than
one, it fills the plane in either orientation; every intermediate actor
has the same commutator space. Conjugation transports these spaces through
the actual representation, preserving the chosen identification of GL₄(2).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.962 (PDF p.979). The radical
placement and the nonsplitting exclusion are separate hypotheses here.
-/

@[expose] public section

open Representation
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry
variable {H U E : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup E] [Module (ZMod 2) E]

abbrev commSpace (ρ : Representation (ZMod 2) H U) (A : Subgroup H) :=
  Coinvariants.ker (ρ.comp A.subtype)

theorem commSpace_mono (ρ : Representation (ZMod 2) H U)
    {A B : Subgroup H} (hAB : A ≤ B) : commSpace ρ A ≤ commSpace ρ B := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, u⟩, rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp B.subtype) ⟨a, hAB a.property⟩ u

theorem commSpace_map (ρ : Representation (ZMod 2) H U)
    (σ : Representation (ZMod 2) H E) (e : U ≃ₗ[ZMod 2] E)
    (he : ∀ g u, e (ρ g u) = σ g (e u)) (A : Subgroup H) :
    (commSpace ρ A).map e.toLinearMap = commSpace σ A := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, u⟩, rfl⟩
    change e (ρ a u - u) ∈ commSpace σ A
    rw [map_sub, he]
    exact Coinvariants.sub_mem_ker (ρ := σ.comp A.subtype) a (e u)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    refine ⟨ρ a (e.symm v) - e.symm v,
      Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) a _, ?_⟩
    change e (ρ a (e.symm v) - e.symm v) = σ a v - v
    rw [map_sub, he, e.apply_symm_apply]

theorem commSpace_eq_of_plane (ρ : Representation (ZMod 2) H U)
    {A B : Subgroup H} (hAB : A ≤ B) (P : Submodule (ZMod 2) U)
    (hP : Module.finrank (ZMod 2) P = 2) [FiniteDimensional (ZMod 2) U]
    (hB : ∀ b ∈ B, ∀ u, ρ b u - u ∈ P)
    (hA : 1 < Module.finrank (ZMod 2) (commSpace ρ A)) :
    commSpace ρ A = P ∧ commSpace ρ B = P := by
  have hBP : commSpace ρ B ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, u⟩, rfl⟩
    exact hB b b.property u
  have hAP := (commSpace_mono ρ hAB).trans hBP
  have hdim := Submodule.finrank_mono hAP
  have hEq : commSpace ρ A = P := Submodule.eq_of_le_of_finrank_eq hAP (by omega)
  exact ⟨hEq, le_antisymm hBP (hEq ▸ commSpace_mono ρ hAB)⟩

local notation "Vec" => ChiefFactors.NaturalSpace

theorem commSpace_eq_of_natural_or_dual
    (ρ : Representation (ZMod 2) H U) [FiniteDimensional (ZMod 2) U]
    (eH : H ≃* BinaryLinear.GL Vec) (hρ : ChiefFactors.IsNaturalOrDual ρ eH)
    {A B : Subgroup H} (hAB : A ≤ B)
    (P : Submodule (ZMod 2) Vec) (hP : Module.finrank (ZMod 2) P = 2)
    (hB : B.map eH.toMonoidHom ≤ BinaryLinear.radical P)
    (hA : 1 < Module.finrank (ZMod 2) (commSpace ρ A)) :
    commSpace ρ A = commSpace ρ B := by
  rcases hρ with ⟨e, he⟩ | ⟨e, he⟩
  · let Q := P.map e.symm.toLinearMap
    have hQ : Module.finrank (ZMod 2) Q = 2 :=
      (LinearEquiv.finrank_map_eq e.symm P).trans hP
    have hb : ∀ b ∈ B, ∀ u, ρ b u - u ∈ Q := by
      intro b hb u
      refine ⟨e (ρ b u - u), ?_, e.symm_apply_apply _⟩
      change e (ρ b u - u) ∈ P
      rw [map_sub, he]
      exact (hB (Subgroup.mem_map_of_mem _ hb)).2 (e u)
    obtain ⟨ha, hb⟩ := commSpace_eq_of_plane ρ hAB Q hQ hb hA
    exact ha.trans hb.symm
  · let Q := P.dualAnnihilator.map e.symm.toLinearMap
    have hPd : Module.finrank (ZMod 2) P.dualAnnihilator = 2 := by
      have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq P
      have hv : Module.finrank (ZMod 2) Vec = 4 := by simp
      omega
    have hQ : Module.finrank (ZMod 2) Q = 2 :=
      (LinearEquiv.finrank_map_eq e.symm P.dualAnnihilator).trans hPd
    have hb : ∀ b ∈ B, ∀ u, ρ b u - u ∈ Q := by
      intro b hb u
      refine ⟨e (ρ b u - u), ?_, e.symm_apply_apply _⟩
      change e (ρ b u - u) ∈ P.dualAnnihilator
      rw [map_sub, he, Submodule.mem_dualAnnihilator]
      intro p hp
      change e u (eH b⁻¹ p) - e u p = 0
      have hf : eH b⁻¹ p = p := (hB (Subgroup.mem_map_of_mem _ (B.inv_mem hb))).1 p hp
      rw [hf, sub_self]
    obtain ⟨ha, hb⟩ := commSpace_eq_of_plane ρ hAB Q hQ hb hA
    exact ha.trans hb.symm


theorem commSpace_conjugate (ρ : Representation (ZMod 2) H U)
    (A : Subgroup H) (g : H) :
    commSpace ρ (A.map (MulAut.conj g).toMonoidHom) = (commSpace ρ A).map (ρ g) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, u⟩, rfl⟩
    obtain ⟨b, hb, he⟩ := a.property
    refine ⟨ρ b (ρ g⁻¹ u) - ρ g⁻¹ u,
      Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨b, hb⟩ _, ?_⟩
    change ρ g (ρ b (ρ g⁻¹ u) - ρ g⁻¹ u) = ρ a u - u
    rw [← he]
    change ρ g (ρ b (ρ g⁻¹ u) - ρ g⁻¹ u) = ρ (g * b * g⁻¹) u - u
    simp [map_sub, ← Module.End.mul_apply, ← map_mul, mul_assoc]
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, u⟩, rfl⟩
    change ρ g (ρ a u - u) ∈ commSpace ρ (A.map (MulAut.conj g).toMonoidHom)
    have hh := Coinvariants.sub_mem_ker
      (ρ := ρ.comp (A.map (MulAut.conj g).toMonoidHom).subtype)
      ⟨g * a * g⁻¹, Subgroup.mem_map_of_mem _ a.property⟩ (ρ g u)
    change ρ (g * a * g⁻¹) (ρ g u) - ρ g u ∈ _ at hh
    simpa [commSpace, map_sub, ← Module.End.mul_apply, ← map_mul, mul_assoc] using hh

theorem conjugate_commSpace_finrank (ρ : Representation (ZMod 2) H U)
    (A : Subgroup H) (g : H) :
    Module.finrank (ZMod 2) (commSpace ρ (A.map (MulAut.conj g).toMonoidHom)) =
      Module.finrank (ZMod 2) (commSpace ρ A) := by
  rw [commSpace_conjugate]
  exact LinearEquiv.finrank_map_eq
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)) _

theorem commSpaces_of_conjugate_radical
    (ρ : Representation (ZMod 2) H U) [FiniteDimensional (ZMod 2) U]
    (eH : H ≃* BinaryLinear.GL Vec) (hρ : ChiefFactors.IsNaturalOrDual ρ eH)
    {A B : Subgroup H} (hAB : A ≤ B)
    (P : Submodule (ZMod 2) Vec) (hP : Module.finrank (ZMod 2) P = 2) (g : H)
    (hB : (B.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤ BinaryLinear.radical P)
    (hA : 1 < Module.finrank (ZMod 2) (commSpace ρ A)) :
    commSpace ρ (A.map (MulAut.conj g).toMonoidHom) =
        commSpace ρ (B.map (MulAut.conj g).toMonoidHom) ∧
      commSpace ρ A = commSpace ρ B := by
  have ha := commSpace_eq_of_natural_or_dual ρ eH hρ (Subgroup.map_mono hAB) P hP hB
    (by rw [conjugate_commSpace_finrank]; exact hA)
  refine ⟨ha, ?_⟩
  rw [commSpace_conjugate, commSpace_conjugate] at ha
  have hi : Function.Injective (ρ g) :=
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).injective
  exact (Submodule.map_injective_of_injective hi) ha

/-- Every displacement lies on one binary point. For a faithful nontrivial
actor this says its nonidentity elements are transvections with a common center. -/
def HasCommonCenter (ρ : Representation (ZMod 2) H U) (A : Subgroup H) : Prop :=
  ∃ L : Submodule (ZMod 2) U, Module.finrank (ZMod 2) L = 1 ∧
    ∀ a ∈ A, ∀ u, ρ a u - u ∈ L

theorem natural_or_dual_trivial_element
    (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL Vec) (hρ : ChiefFactors.IsNaturalOrDual ρ eH)
    (g : H) (hg : ∀ u, ρ g u = u) : g = 1 := by
  rcases hρ with ⟨e, he⟩ | ⟨e, he⟩
  · apply eH.injective
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    change eH g (e u) = eH 1 (e u)
    rw [← he, hg, map_one]
    rfl
  · have hi : eH g⁻¹ = 1 := by
      apply LinearEquiv.ext
      intro v
      change eH g⁻¹ v = v
      apply sub_eq_zero.mp
      apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp
      intro f
      obtain ⟨u, rfl⟩ := e.surjective f
      have heq := he g u
      rw [hg] at heq
      have hv := LinearMap.congr_fun heq v
      change e u v = e u (eH g⁻¹ v) at hv
      rw [map_sub, hv, sub_self]
    have hgi : g⁻¹ = 1 := eH.injective (by simpa using hi)
    exact inv_eq_one.mp hgi

theorem commSpace_rank_gt_one_of_no_common_center
    (ρ : Representation (ZMod 2) H U) [FiniteDimensional (ZMod 2) U]
    (eH : H ≃* BinaryLinear.GL Vec) (hρ : ChiefFactors.IsNaturalOrDual ρ eH)
    (A : Subgroup H) (hA : 1 < rank A) (hcenter : ¬ HasCommonCenter ρ A) :
    1 < Module.finrank (ZMod 2) (commSpace ρ A) := by
  have hzero : Module.finrank (ZMod 2) (commSpace ρ A) ≠ 0 := by
    intro hz
    have hb := Submodule.finrank_eq_zero.mp hz
    have ha : A = ⊥ := by
      apply le_bot_iff.mp
      intro a ha
      apply natural_or_dual_trivial_element ρ eH hρ a
      intro u
      have hm := Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨a, ha⟩ u
      change ρ a u - u ∈ commSpace ρ A at hm
      rw [hb] at hm
      exact sub_eq_zero.mp hm
    simp [ha, rank] at hA
  have hone : Module.finrank (ZMod 2) (commSpace ρ A) ≠ 1 := by
    intro hdim
    apply hcenter
    refine ⟨commSpace ρ A, hdim, ?_⟩
    intro a ha u
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨a, ha⟩ u
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry
