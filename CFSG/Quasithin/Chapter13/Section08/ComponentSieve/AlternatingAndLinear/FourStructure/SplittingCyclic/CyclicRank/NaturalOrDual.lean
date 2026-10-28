module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.PlaneTransport

/-!
# The cyclic-case order bound in both natural orientations

Evaluation outside a fixed hyperplane embeds the faithful actor in its
two-dimensional displacement space. A subgroup of a marked plane radical
has such a space in the natural module and in the dual, where the actual
annihilator plane supplies it. The specified equivariant identification
and conjugator give order four for the noncyclic elementary actor.

This extends the concrete natural-space bound without choosing an
unrelated group identification for the dual factor.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic

open Representation Representation.BinaryOffender ChiefFactors

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- Evaluation outside a fixed hyperplane embeds a faithful actor whose displacements lie
in a two-space into that two-space. -/
theorem card_le_four_of_faithful_plane_displacement
    (hρ : Function.Injective ρ) (A : Subgroup H)
    (P : Submodule (ZMod 2) U) (hP : Module.finrank (ZMod 2) P = 2)
    (hdisplace : ∀ a ∈ A, ∀ u, ρ a u - u ∈ P)
    (hcodim : fixedCodim ρ A = 1) : Nat.card A ≤ 4 := by
  classical
  let : Finite P := Module.finite_of_finite (ZMod 2)
  let Q := fixedSpace ρ A
  have hQt : Q ≠ ⊤ := by
    intro ht
    have hz := (fixedCodim_eq_zero_iff ρ A).mpr ht
    omega
  obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hQt)
  have hspan : Q ⊔ Submodule.span (ZMod 2) {v} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hv]
    have hf := fixedCodim_add_finrank ρ A
    change fixedCodim ρ A + Module.finrank (ZMod 2) Q = _ at hf
    omega
  let δ : A → P := fun a => ⟨ρ a v - v, hdisplace a a.property v⟩
  have hinj : Function.Injective δ := by
    intro a b hab
    have hev : ρ a v = ρ b v := sub_left_injective (congrArg Subtype.val hab)
    apply Subtype.ext
    apply hρ
    ext u
    have hu : u ∈ Q ⊔ Submodule.span (ZMod 2) {v} := hspan ▸ Submodule.mem_top
    obtain ⟨q, hq, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hqa : ρ a q = q := hq a
    have hqb : ρ b q = q := hq b
    simp only [map_add, map_smul, hqa, hqb, hev]
  have hc : Nat.card P = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hP]
    decide
  exact (Nat.card_le_card_of_injective δ hinj).trans_eq hc

omit [FiniteDimensional (ZMod 2) U] in
/-- A marked plane radical has a two-dimensional displacement space in either natural
orientation; in the dual it is the annihilator plane. -/
theorem exists_displacement_plane_of_naturalOrDual
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hρ : IsNaturalOrDual ρ eH)
    (A : Subgroup H) (P : Submodule (ZMod 2) NaturalSpace)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hrad : A.map eH.toMonoidHom ≤ BinaryLinear.radical P) :
    ∃ Q : Submodule (ZMod 2) U, Module.finrank (ZMod 2) Q = 2 ∧
      ∀ a ∈ A, ∀ u, ρ a u - u ∈ Q := by
  rcases hρ with ⟨e, he⟩ | ⟨e, he⟩
  · refine ⟨P.map e.symm.toLinearMap, (LinearEquiv.finrank_map_eq e.symm P).trans hP, ?_⟩
    intro a ha u
    refine ⟨e (ρ a u - u), ?_, e.symm_apply_apply _⟩
    change e (ρ a u - u) ∈ P
    rw [map_sub, he]
    exact (hrad (Subgroup.mem_map_of_mem _ ha)).2 (e u)
  · have hPd : Module.finrank (ZMod 2) P.dualAnnihilator = 2 := by
      have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq P
      have hv : Module.finrank (ZMod 2) NaturalSpace = 4 := by simp
      omega
    refine ⟨P.dualAnnihilator.map e.symm.toLinearMap,
      (LinearEquiv.finrank_map_eq e.symm P.dualAnnihilator).trans hPd, ?_⟩
    intro a ha u
    refine ⟨e (ρ a u - u), ?_, e.symm_apply_apply _⟩
    change e (ρ a u - u) ∈ P.dualAnnihilator
    rw [map_sub, he, Submodule.mem_dualAnnihilator]
    intro p hp
    change e u (eH a⁻¹ p) - e u p = 0
    have hf : eH a⁻¹ p = p := (hrad (Subgroup.mem_map_of_mem _ (A.inv_mem ha))).1 p hp
    rw [hf, sub_self]

/-- A noncyclic elementary actor fixing a hyperplane of the specified natural-or-dual
module has order four when its actual conjugate lies in the marked radical. -/
theorem card_eq_four_of_naturalOrDual_hyperplane
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hρ : IsNaturalOrDual ρ eH)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hrank : 1 < rank A)
    (P : Submodule (ZMod 2) NaturalSpace) (hP : Module.finrank (ZMod 2) P = 2)
    (g : H)
    (hrad : (A.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤ BinaryLinear.radical P)
    (hcodim : fixedCodim ρ A = 1) : Nat.card A = 4 := by
  let : Finite (BinaryLinear.GL NaturalSpace) :=
    Finite.of_injective (fun g : BinaryLinear.GL NaturalSpace =>
      (g : NaturalSpace → NaturalSpace)) DFunLike.coe_injective
  let : Finite H := Finite.of_injective eH eH.injective
  obtain ⟨Q, hQ, hdisp⟩ := exists_displacement_plane_of_naturalOrDual ρ eH hρ A
    (P.map (eH g⁻¹).toLinearMap) ((LinearEquiv.finrank_map_eq (eH g⁻¹) P).trans hP)
    (le_radical_of_conjugate eH P A g hrad)
  have hle := card_le_four_of_faithful_plane_displacement ρ
    (AxisExclusions.naturalOrDual_faithful ρ eH hρ) A Q hQ hdisp hcodim
  have hge : 4 ≤ Nat.card A := by
    rw [hA.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hrank
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
