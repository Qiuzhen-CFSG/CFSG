module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# The binary A₂ obstruction to field automorphisms

The coefficient action of an elementary binary actor has image of order at
most two. Its kernel has the same fixed space as the full A₂ actor. A nonzero
fixed vector and its scalar multiples force every coefficient to be trivial.
This is the local step in 6.1.12(2--3), independent of the global rank formula.
Source: Aschbacher--Smith, combined manuscript, printed pp.669--670.
-/

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterE Representation.SL2NaturalOffenders

variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]

/-- The actual binary A₂ convention excludes nontrivial field coefficients. -/
theorem fixedSpaceFamily_two_fieldLinear (ρ : Representation (ZMod 2) H (Fin 2 → F))
    {A : Subgroup H} (hA : A ∈ fixedSpaceFamily ρ 2)
    (hsemi : ∀ a : A, ∃ σ : F ≃+* F, ∀ c v,
      ρ (a : H) (c • v) = σ c • ρ (a : H) v) :
    ∀ a ∈ A, ∀ (c : F) (v : Fin 2 → F), ρ a (c • v) = c • ρ a v := by
  let ψ : A →* (F ≃+* F) := fieldAction (ρ.comp A.subtype) hsemi
  let B := ψ.ker.map A.subtype
  have hBA : B ≤ A := map_subtype_le _
  have hind : B.relIndex A = Nat.card ψ.range := by
    have hh := relIndex_map_map_of_injective ψ.ker (⊤ : Subgroup A)
      A.subtype_injective
    rw [← MonoidHom.range_eq_map, A.range_subtype, relIndex_top_right, index_ker] at hh
    exact hh
  have hsmall : Nat.log 2 (B.relIndex A) < 2 := by
    rw [hind]
    have hh := Nat.log_mono_right (b := 2) (fieldAction_range_card_le_two A hA.2.1.2 ψ)
    exact lt_of_le_of_lt hh (by decide)
  have heq : fixedSpace ρ A = fixedSpace ρ B := hA.2.2 B hBA hsmall
  let := hA.2.1.2
  obtain ⟨v, _, hv, hvA⟩ := PermutedSupports.exists_nonzero_fixed ρ A
    (IsElementaryAbelian.isPGroup 2 A) ⊤ (by exact top_ne_bot)
    (by intro a ha v; exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  have hvB : v ∈ fixedSpace ρ B := heq ▸ hvA
  have hcv (c : F) : c • v ∈ fixedSpace ρ B := by
    rintro ⟨_, b, hb, rfl⟩
    have hlin := (fieldAction_eq_one_iff (ρ.comp A.subtype) hsemi b).mp hb
    change ρ (b : H) (c • v) = c • v
    rw [show ρ (b : H) (c • v) = c • ρ (b : H) v from hlin c v]
    exact congrArg (c • ·) (hvB ⟨b, mem_map_of_mem A.subtype hb⟩)
  intro a ha
  apply (fieldAction_eq_one_iff (ρ.comp A.subtype) hsemi ⟨a,ha⟩).mp
  apply RingEquiv.ext
  intro c
  apply smul_left_injective F hv
  change ψ ⟨a,ha⟩ c • v = c • v
  have hh : c • v ∈ fixedSpace ρ A := heq.symm ▸ hcv c
  calc
    ψ ⟨a,ha⟩ c • v = ψ ⟨a,ha⟩ c • ρ a v :=
      congrArg (ψ ⟨a,ha⟩ c • ·) (hvA ⟨a,ha⟩).symm
    _ = ρ a (c • v) :=
      (fieldAction_smul (ρ.comp A.subtype) hsemi ⟨a,ha⟩ c v).symm
    _ = c • v := hh ⟨a,ha⟩

section Line
variable [CharP F 2]
omit [Algebra (ZMod 2) F] in
/-- A field-linear involution preserving a field line fixes it pointwise. -/
theorem fieldLine_involution_fixes (W : Submodule F (Fin 2 → F)) (hW : Nat.card W = Nat.card F)
    (f : (Fin 2 → F) →ₗ[F] (Fin 2 → F))
    (hf : ∀ v, f (f v) = v) (hn : ∀ v ∈ W, f v ∈ W) :
    ∀ v ∈ W, f v = v := by
  have hdim : Module.finrank F W = 1 := by
    apply Nat.pow_right_injective (show 2 ≤ Nat.card F from Finite.one_lt_card)
    change Nat.card F ^ Module.finrank F W = Nat.card F ^ 1
    rw [pow_one, ← Module.natCard_eq_pow_finrank, hW]
  let d : W →ₗ[F] W := f.restrict hn
  obtain ⟨c, hc, _⟩ := d.existsUnique_eq_smul_id_of_finrank_eq_one hdim
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < Module.finrank F W by omega)
  have hd (w : W) : d w = c • w := by rw [hc]; rfl
  have hsq : c * c = 1 := by
    apply smul_left_injective F hv
    change (c * c) • v = (1 : F) • v
    rw [mul_smul, ← hd, ← hd, one_smul]
    exact Subtype.ext (hf v)
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp (show c ^ 2 = 1 by simpa only [pow_two] using hsq) with he | he
    · exact he
    · simpa only [CharTwo.neg_eq] using he
  intro w hw
  have hh := hd ⟨w,hw⟩
  rw [hc1, one_smul] at hh
  exact congrArg Subtype.val hh
end Line
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
