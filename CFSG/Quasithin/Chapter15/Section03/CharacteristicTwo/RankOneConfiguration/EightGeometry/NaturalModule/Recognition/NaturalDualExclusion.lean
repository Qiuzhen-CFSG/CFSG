module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import Theory.SpecificGroups.BinaryLinear.NaturalDualFlag

/-!
# Excluding the natural-plus-dual alternative by the moving line

The supplied middle-node marking identifies the actual component parabolic
with the stabilizer of a flag of dimensions one and three. We recover its
two subspaces from the flag's types and transport the moving binary plane
through the supplied equivariant coordinates. The binary flag calculation
then gives a nonzero vector fixed by the whole parabolic, hence by Y.
This contradicts the moving line's disjointness from its Y-fixed space.

The natural and contragredient actions use the same PSL₄(2) identification
as the flag stabilizer. The argument applies directly to arbitrary flags;
no standard-position or additional conjugacy hypothesis is needed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
paragraph of the proof of 15.3.32, printed p.1132, using 15.3.28(3) on
printed p.1131. This proves the exclusion branch independently of the
construction of the B.5.1 module alternatives.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.NaturalDualExclusion
open Chapter2.ComponentRefinement.LieType.Binary
open Representation.BinaryOffender

private theorem flag_pair (F : Flag 4) (hF : F.types = {1, 3}) :
    ∃ A H : Space 4, F.spaces = {A, H} ∧
      Module.finrank (ZMod 2) A = 1 ∧ Module.finrank (ZMod 2) H = 3 ∧ A ≤ H := by
  classical
  have ht₁ : 1 ∈ F.types := by rw [hF]; simp
  have ht₃ : 3 ∈ F.types := by rw [hF]; simp
  obtain ⟨A, hm₁, hd₁⟩ := Finset.mem_image.mp ht₁
  obtain ⟨H, hm₃, hd₃⟩ := Finset.mem_image.mp ht₃
  have unique (W W' : Space 4) (hW : W ∈ F.spaces) (hW' : W' ∈ F.spaces)
      (hd : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) W') : W = W' := by
    rcases F.chain W hW W' hW' with hle | hle
    · exact Submodule.eq_of_le_of_finrank_eq hle hd
    · exact (Submodule.eq_of_le_of_finrank_eq hle hd.symm).symm
  refine ⟨A, H, ?_, hd₁, hd₃, ?_⟩
  · apply Finset.Subset.antisymm
    · intro W hW
      have hd : Module.finrank (ZMod 2) W ∈ F.types := Finset.mem_image.mpr ⟨W, hW, rfl⟩
      rw [hF] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
      exact hd.elim (fun hd => Or.inl (unique W A hW hm₁ (hd.trans hd₁.symm)))
        (fun hd => Or.inr (unique W H hW hm₃ (hd.trans hd₃.symm)))
    · intro W hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      exact hW.elim (fun h => h ▸ hm₁) (fun h => h ▸ hm₃)
  · rcases F.chain A hm₁ H hm₃ with hle | hle
    · exact hle
    · have hd := Submodule.finrank_mono hle
      omega

private theorem naturalDualFour_eq_action (g : PSL 4)
    (w : Vector 4 × Module.Dual (ZMod 2) (Vector 4)) :
    Models.naturalDualFour g w = BinaryLinear.NaturalDualFlag.action (pslEquivLinear 4 g) w := by
  apply Prod.ext
  · rw [BinaryLinear.NaturalDualFlag.action_fst]
    rfl
  · apply LinearMap.ext
    intro v
    rw [BinaryLinear.NaturalDualFlag.action_snd]
    change w.2 (pslEquivLinear 4 g⁻¹ v) = w.2 ((pslEquivLinear 4 g).symm v)
    rw [map_inv]
    rfl

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) K V} {L P S Y : Subgroup K}

/-- A moving binary plane for the marked middle parabolic excludes the actual
natural-plus-dual representation in the same projective-linear coordinates. -/
theorem not_nonempty_naturalDual (mark : Models.MiddleNodeMarking L P)
    (line : Models.MovingLine ρ P S Y) (hY : Y ≤ P) :
    ¬ Nonempty (Models.NaturalDual ρ L mark.model) := by
  classical
  rintro ⟨natural⟩
  obtain ⟨A, H, hspaces, hA, hH, hAH⟩ := flag_pair mark.flag mark.middle
  have hP (l : L) : (l : K) ∈ P ↔
      linearModel mark.model l ∈ BinaryLinear.parabolic A ⊓ BinaryLinear.parabolic H := by
    conv_lhs => rw [mark.parabolic]
    change L.subtype l ∈ (flagStabilizer mark.model mark.flag).map L.subtype ↔ _
    rw [Subgroup.mem_map_iff_mem (Subtype.val_injective), mem_flagStabilizer, hspaces]
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Subgroup.mem_inf]
    rfl
  let W := line.space.map natural.coordinates.toLinearMap
  have hWcard : Nat.card W = 4 := by
    rw [← Nat.card_congr (Submodule.equivMapOfInjective natural.coordinates.toLinearMap
      natural.coordinates.injective line.space).toEquiv]
    exact line.card
  have hstable : ∀ g ∈ BinaryLinear.parabolic A ⊓ BinaryLinear.parabolic H,
      ∀ w ∈ W, BinaryLinear.NaturalDualFlag.action g w ∈ W := by
    intro g hg w hw
    obtain ⟨v, hv, rfl⟩ := hw
    let l := (linearModel mark.model).symm g
    have hl : (l : K) ∈ P := (hP l).mpr (by simpa [l] using hg)
    refine ⟨ρ l v, line.parabolic_stable l hl v hv, ?_⟩
    change natural.coordinates (ρ l v) = _
    rw [natural.equivariant, naturalDualFour_eq_action]
    change BinaryLinear.NaturalDualFlag.action (linearModel mark.model l) _ = _
    simp only [l, MulEquiv.apply_symm_apply, LinearEquiv.coe_coe]
  have hHcodim : Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) (Vector 4) := by
    change Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) (Fin 4 → ZMod 2)
    simp [hH]
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hWcard]; decide)
  obtain ⟨w, hw, hw0, hfix⟩ := BinaryLinear.NaturalDualFlag.exists_fixed hAH hA hHcodim W
    (by rw [hWcard]; decide) hstable
  obtain ⟨v, hv, rfl⟩ := hw
  have hv0 : v ≠ 0 := by
    intro he
    exact hw0 (by simp [he])
  have hPL : P ≤ L := mark.parabolic ▸ ambientFlagStabilizer_le mark.model mark.flag
  have hvfixed : v ∈ fixedSpace ρ Y := by
    intro y
    let l : L := ⟨y.val, hPL (hY y.property)⟩
    apply natural.coordinates.injective
    change natural.coordinates (ρ (l : K) v) = natural.coordinates v
    rw [natural.equivariant, naturalDualFour_eq_action]
    exact hfix (linearModel mark.model l) ((hP l).mp (hY y.property))
  exact hv0 (Submodule.disjoint_def.mp line.fixed_disjoint v hv hvfixed)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.NaturalDualExclusion
