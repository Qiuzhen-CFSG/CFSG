module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.Coordinates
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The representation-dependent diagonal choice

The restrictions of the two disjoint three-cycles are the two nonidentity
cubic operators of GL₂(2). The common four-group generator commutes with
the tail cubic, so its involution restriction is trivial. Thus exactly one
diagonal cubic acts trivially, while the other fully moves the plane.
All restrictions and commutators use the original representation and the
literal permutation relabelling.

Source: Aschbacher–Smith, Lemma 13.6.22, printed p.932.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking

private theorem matrix_cubic_cases : ∀ a : Matrix (Fin 2) (Fin 2) (ZMod 2),
    a ^ 3 = 1 → a ≠ 1 → a = !![0,1;1,1] ∨ a = !![1,1;1,0] := by
  decide +kernel

private theorem matrix_cubic_pair (a b : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hna : a ≠ 1) (hnb : b ≠ 1) :
    a = b ∨ a = b ^ 2 := by
  rcases matrix_cubic_cases a ha hna with rfl | rfl <;>
    rcases matrix_cubic_cases b hb hnb with rfl | rfl <;> decide +kernel

private theorem matrix_cubic_involution : ∀ b t : Matrix (Fin 2) (Fin 2) (ZMod 2),
    b ^ 3 = 1 → b ≠ 1 → t ^ 2 = 1 → t * b = b * t → t = 1 := by
  decide +kernel

private theorem plane_cubic_pair {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hd : Module.finrank (ZMod 2) V = 2)
    (a b : Module.End (ZMod 2) V) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hna : a ≠ 1) (hnb : b ≠ 1) :
    (a * b = 1 ∧ a * b ^ 2 = b) ∨ (a * b ^ 2 = 1 ∧ a * b = b ^ 2) := by
  let m := LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq (ZMod 2) V hd)
  have h := matrix_cubic_pair (m a) (m b)
    (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
    (fun h => hna (m.injective (h.trans m.map_one.symm)))
    (fun h => hnb (m.injective (h.trans m.map_one.symm)))
  have he : a = b ∨ a = b ^ 2 := by
    rcases h with h | h
    · exact Or.inl (m.injective h)
    · exact Or.inr (m.injective (by simpa only [map_pow] using h))
  rcases he with rfl | rfl
  · right
    exact ⟨by simpa only [← pow_succ'] using hb, (pow_two _).symm⟩
  · left
    constructor
    · simpa only [← pow_succ] using hb
    · calc
        b ^ 2 * b ^ 2 = b ^ (3 + 1) := by rw [← pow_add]
        _ = b := by rw [pow_succ, hb, one_mul]

private theorem plane_cubic_involution {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hd : Module.finrank (ZMod 2) V = 2)
    (b t : Module.End (ZMod 2) V) (hb : b ^ 3 = 1) (hnb : b ≠ 1)
    (ht : t ^ 2 = 1) (hc : t * b = b * t) : t = 1 := by
  let m := LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq (ZMod 2) V hd)
  apply m.injective
  simpa only [map_one] using matrix_cubic_involution (m b) (m t)
    (by rw [← map_pow, hb, map_one])
    (fun h => hnb (m.injective (h.trans m.map_one.symm)))
    (by rw [← map_pow, ht, map_one])
    (by simpa only [map_mul] using congrArg m hc)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) A7 W) (P : Submodule (ZMod 2) W)

private theorem commutator_eq_of_fixedPointFree (D : Subgroup A7)
    (hD : D ≤ subspaceStabilizer ρ P) (a : A7) (ha : a ∈ D)
    (hf : ∀ w ∈ P, ρ a w = w → w = 0) : subspaceCommutator ρ P D = P := by
  let f : P →ₗ[ZMod 2] P := (ρ a).restrict (fun {w} hw => (hD ha w).mpr hw) - 1
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp (by
    apply bot_unique
    intro w hw
    change w = 0
    apply Subtype.ext
    apply hf w w.property
    have he := congrArg Subtype.val hw
    exact sub_eq_zero.mp he)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, w, hw, rfl⟩
    exact P.sub_mem ((hD hd w).mpr hw) hw
  · intro w hw
    obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    exact Submodule.subset_span ⟨a, ha, v, v.property, (congrArg Subtype.val hv).symm⟩

private def blockRepresentation (g : Equiv.Perm (Fin 7))
    (hB : blockStabilizer.map (relabelling g).toMonoidHom ≤ subspaceStabilizer ρ P) :
    Representation (ZMod 2) blockStabilizer P :=
  (stabilizerRepresentation ρ P).comp
    (((relabelling g).toMonoidHom.comp blockStabilizer.subtype).codRestrict
      (subspaceStabilizer ρ P) fun b => hB ⟨b, b.property, rfl⟩)

omit [FiniteDimensional (ZMod 2) W] in
private theorem pair_commutator_eq_bot (g : Equiv.Perm (Fin 7)) (a t : A7)
    (ha : ∀ w ∈ P, ρ (relabelling g a) w = w)
    (ht : ∀ w ∈ P, ρ (relabelling g t) w = w) :
    subspaceCommutator ρ P ((closure ({a,t} : Set A7)).map (relabelling g).toMonoidHom) = ⊥ := by
  have hle : (closure ({a,t} : Set A7)).map (relabelling g).toMonoidHom ≤
      subspaceKernel ρ P ⊤ := by
    rw [map_le_iff_le_comap, closure_le]
    rintro x (rfl | rfl)
    · exact ⟨mem_top _, ha⟩
    · exact ⟨mem_top _, ht⟩
  exact (subspaceCommutator_eq_bot_iff _ _ _).mpr (fun _ hw d => (hle d.property).2 _ hw)

/-- The cyclic and natural actors fully move the plane. Precisely one of
the two diagonal actors fully moves it, and the other fixes it pointwise. -/
theorem candidate_commutators (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4) (hP : Module.finrank (ZMod 2) P = 2)
    (g : Equiv.Perm (Fin 7))
    (hB : blockStabilizer.map (relabelling g).toMonoidHom ≤ subspaceStabilizer ρ P) :
    subspaceCommutator ρ P (cyclicActor.map (relabelling g).toMonoidHom) = P ∧
    subspaceCommutator ρ P (naturalActor.map (relabelling g).toMonoidHom) = P ∧
    ((subspaceCommutator ρ P (diagonalPlus.map (relabelling g).toMonoidHom) = P ∧
      subspaceCommutator ρ P (diagonalMinus.map (relabelling g).toMonoidHom) = ⊥) ∨
     (subspaceCommutator ρ P (diagonalMinus.map (relabelling g).toMonoidHom) = P ∧
      subspaceCommutator ρ P (diagonalPlus.map (relabelling g).toMonoidHom) = ⊥)) := by
  let σ := blockRepresentation ρ P g hB
  let a : blockStabilizer := ⟨naturalThree, generators_mem_block.1⟩
  let b : blockStabilizer := ⟨tailThree, generators_mem_block.2.2⟩
  let t : blockStabilizer := ⟨fourFlip, generators_mem_block.2.1⟩
  have ha3 : a ^ 3 = 1 := by apply Subtype.ext; apply Subtype.ext; decide +kernel
  have hb3 : b ^ 3 = 1 := by apply Subtype.ext; apply Subtype.ext; decide +kernel
  have ht2 : t ^ 2 = 1 := by apply Subtype.ext; apply Subtype.ext; decide +kernel
  have htb : t * b = b * t := by apply Subtype.ext; apply Subtype.ext; decide +kernel
  have hfa : ∀ w : W, ρ (relabelling g naturalThree) w = w → w = 0 :=
    binaryAlternatingSeven_threeCycle_fixedPointFree ρ hρ hdim _
      (relabelling_isThreeCycle g naturalThree naturalThree_isThreeCycle)
  have hfb : ∀ w : W, ρ (relabelling g tailThree) w = w → w = 0 :=
    binaryAlternatingSeven_threeCycle_fixedPointFree ρ hρ hdim _
      (relabelling_isThreeCycle g tailThree tailThree_isThreeCycle)
  have hfa' (w : P) (hw : σ a w = w) : w = 0 := Subtype.ext (hfa w (congrArg Subtype.val hw))
  have hfb' (w : P) (hw : σ b w = w) : w = 0 := Subtype.ext (hfb w (congrArg Subtype.val hw))
  have : Nontrivial P := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) P)
  have hna : σ a ≠ 1 := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : P)
    exact hw (hfa' w (LinearMap.congr_fun h w))
  have hnb : σ b ≠ 1 := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : P)
    exact hw (hfb' w (LinearMap.congr_fun h w))
  have hσa : (σ a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hσb : (σ b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hσt : σ t = 1 := plane_cubic_involution hP (σ b) (σ t) hσb hnb
    (by rw [← map_pow, ht2, map_one]) (by rw [← map_mul, ← map_mul, htb])
  have hft : ∀ w ∈ P, ρ (relabelling g fourFlip) w = w := fun w hw =>
    congrArg Subtype.val (LinearMap.congr_fun hσt ⟨w, hw⟩)
  have hfb2 (w : P) (hw : ((σ b) ^ 2) w = w) : w = 0 := by
    apply hfb' w
    have h := congrArg (σ b) hw
    have he : σ b (((σ b) ^ 2) w) = w := by
      rw [← Module.End.mul_apply, ← pow_succ', hσb]
      rfl
    exact (he.symm.trans h).symm
  refine ⟨commutator_eq_of_fixedPointFree ρ P _
      ((Subgroup.map_mono cyclicActor_le_block).trans hB) _
      ⟨tailThree, mem_zpowers _, rfl⟩ (fun w _ => hfb w),
    commutator_eq_of_fixedPointFree ρ P _
      ((Subgroup.map_mono naturalActor_le_block).trans hB) _
      ⟨naturalThree, subset_closure (by simp), rfl⟩ (fun w _ => hfa w), ?_⟩
  have full (c : blockStabilizer) (D : Subgroup A7) (hD : D ≤ blockStabilizer)
      (hc : c.val ∈ D) (hf : ∀ w : P, σ c w = w → w = 0) :
      subspaceCommutator ρ P (D.map (relabelling g).toMonoidHom) = P := by
    apply commutator_eq_of_fixedPointFree ρ P _ ((Subgroup.map_mono hD).trans hB)
      (relabelling g c.val) ⟨c.val, hc, rfl⟩
    intro w hw he
    exact congrArg Subtype.val (hf ⟨w,hw⟩ (Subtype.ext he))
  rcases plane_cubic_pair hP (σ a) (σ b) hσa hσb hna hnb with ⟨hp, hm⟩ | ⟨hm, hp⟩
  · right
    constructor
    · apply full (a * b ^ 2) diagonalMinus diagonalMinus_le_block (subset_closure (Or.inl rfl))
      intro w hw
      rw [map_mul, map_pow, hm] at hw
      exact hfb' w hw
    · apply pair_commutator_eq_bot ρ P g _ _ _ hft
      intro w hw
      have he : σ (a * b) = 1 := by rw [map_mul, hp]
      exact congrArg Subtype.val (LinearMap.congr_fun he ⟨w,hw⟩)
  · left
    constructor
    · apply full (a * b) diagonalPlus diagonalPlus_le_block (subset_closure (Or.inl rfl))
      intro w hw
      rw [map_mul, hp] at hw
      exact hfb2 w hw
    · apply pair_commutator_eq_bot ρ P g _ _ _ hft
      intro w hw
      have he : σ (a * b ^ 2) = 1 := by rw [map_mul, map_pow, hm]
      exact congrArg Subtype.val (LinearMap.congr_fun he ⟨w,hw⟩)

/-- In particular, the two diagonal full-commutator conclusions are mutually
exclusive; the representation-dependent disjunction selects exactly one. -/
theorem diagonal_commutators_exclusive (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4) (hP : Module.finrank (ZMod 2) P = 2)
    (g : Equiv.Perm (Fin 7))
    (hB : blockStabilizer.map (relabelling g).toMonoidHom ≤ subspaceStabilizer ρ P) :
    Xor (subspaceCommutator ρ P (diagonalPlus.map (relabelling g).toMonoidHom) = P)
      (subspaceCommutator ρ P (diagonalMinus.map (relabelling g).toMonoidHom) = P) := by
  have hne : P ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hP
    omega
  rcases (candidate_commutators ρ P hρ hdim hP g hB).2.2 with ⟨hp, hm⟩ | ⟨hm, hp⟩
  · exact Or.inl ⟨hp, fun he => hne (he.symm.trans hm)⟩
  · exact Or.inr ⟨hm, fun he => hne (he.symm.trans hp)⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking
