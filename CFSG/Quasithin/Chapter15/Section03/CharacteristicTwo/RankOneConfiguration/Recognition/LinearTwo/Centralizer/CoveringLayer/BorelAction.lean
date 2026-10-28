module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.CoveringLayer.Module
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Full Borel action on the covering module

The dual of a cover embeds into the universal dual cover, the module of crossed
homomorphisms. A Borel-fixed crossed homomorphism vanishes on the Borel: its
values there are fixed in the dual natural module, where a nonidentity diagonal
has no fixed vector. The diagonal/Weyl relation then kills its Weyl value, and
upper and lower transvections generate SL₂. Duality now gives [U,B] = U.

This is a direct cohomological route to the covering-layer consequence of
Aschbacher–Smith I.2.3(3), printed p.413, used in 15.3.30, pp.1131–1132.
It uses the actual cover constructed in `CoveringLayer.Module`, including its
central kernel, and requires no additional I.2 premise.
-/

public section

open Matrix Matrix.SpecialLinearGroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.CoveringLayer
variable {F : Type*} [Field F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
private abbrev natural := blockNaturalBinary (F := F)
private abbrev upper (t : F) : SpecialLinearGroup (Fin 2) F := transvection zero_ne_one t
private abbrev lower (t : F) : SpecialLinearGroup (Fin 2) F := transvection one_ne_zero t
private def swap : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two, CharTwo.neg_eq]⟩

private theorem diagonal_swap (a : F) (ha : a ≠ 0) :
    diag2 a ha * swap = swap * diag2 a⁻¹ (inv_ne_zero ha) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [coe_mul]; simp [diag2_coe', swap, Matrix.mul_apply, Fin.sum_univ_two])

private theorem swap_upper (t : F) : swap * upper t = lower t * swap (F := F) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [coe_mul]; simp [swap, upper, lower, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two])

private theorem diagonal_dual_fixed (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (v : Module.Dual (ZMod 2) (Fin 2 → F))
    (hv : (natural (F := F)).dual (diag2 a ha) v = v) : v = 0 := by
  have has : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hai : a⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (inv_ne_one.mpr ha1)
  apply LinearMap.ext
  intro w
  let x : Fin 2 → F := ![w 0 / (a⁻¹ - 1), w 1 / (a - 1)]
  have hx : natural (diag2 a ha)⁻¹ x - x = w := by
    ext i
    fin_cases i <;>
      simp [natural, blockNaturalBinary, restrictScalars, specialLinearNatural_apply, x,
        diag2_coe', adjugate_fin_two]
    · field_simp
    · field_simp
  have h := LinearMap.congr_fun hv x
  change v (natural (diag2 a ha)⁻¹ x) = v x at h
  have hz : v (natural (diag2 a ha)⁻¹ x - x) = 0 := by rw [map_sub, h, sub_self]
  simpa only [hx, LinearMap.zero_apply] using hz

private theorem cocycle_zero_of_borel (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (f : cocycles (natural (F := F)).dual)
    (hf : ∀ b ∈ rankOneBorel F, f.val b = 0) : f = 0 := by
  have hs : f.val swap = 0 := by
    apply diagonal_dual_fixed a ha ha1
    have h := congrArg f.val (diagonal_swap a ha)
    rw [f.property, f.property] at h
    simpa only [hf _ (diag_mem_rankOneBorel a ha),
      hf _ (diag_mem_rankOneBorel a⁻¹ (inv_ne_zero ha)), map_zero, add_zero, zero_add] using h
  have hl (t : F) : f.val (lower t) = 0 := by
    have h := congrArg f.val (swap_upper t)
    rw [f.property, f.property] at h
    simpa only [hs, hf _ (upper_mem_rankOneBorel t), map_zero,
      add_zero, zero_add] using h.symm
  apply Subtype.ext
  funext g
  apply Matrix.SL2.transvection_induction (fun g => f.val g = 0) ?_ ?_ g
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hf _ (upper_mem_rankOneBorel t)
    · exact hl t
    · exact (hij rfl).elim
  · intro g h hg hh
    rw [f.property, hg, hh, map_zero, add_zero]

private theorem universal_borel_fixed_eq_bot (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    fixed (k := ZMod 2) (W := cocycles (natural (F := F)).dual) ((universalAction (natural (F := F)).dual).comp (rankOneBorel F).subtype) = ⊥ := by
  apply bot_unique
  intro f hf
  apply cocycle_zero_of_borel a ha ha1 f
  intro b hb
  have hp : principal (natural (F := F)).dual (f.val b) = 0 := by
    have h := hf ⟨b, hb⟩
    change f + principal (natural (F := F)).dual (f.val b) = f at h
    exact add_eq_left.mp h
  apply diagonal_dual_fixed a ha ha1
  have h : f.val b ∈ (principal (natural (F := F)).dual).ker := hp
  rw [ker_principal] at h
  exact h _

private theorem cover_borel_full {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (p : σ.IntertwiningMap (natural (F := F))) (hp : IsCover p)
    (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    Coinvariants.ker (σ.comp (rankOneBorel F).subtype) = ⊤ := by
  obtain ⟨d, hd, _⟩ := exists_dualCoverEmbedding (dualIntertwining p)
    (LinearMap.dualMap_injective_of_surjective hp.1) (cover_dual_isDualCover p hp)
  apply (fixed_dual_eq_bot_iff _).mp
  apply bot_unique
  intro w hw
  have h : d w ∈ fixed (k := ZMod 2) (W := cocycles (natural (F := F)).dual) ((universalAction (natural (F := F)).dual).comp (rankOneBorel F).subtype) := by
    intro b
    change universalAction (natural (F := F)).dual (b : SpecialLinearGroup (Fin 2) F) (d w) = d w
    rw [← d.isIntertwining]
    exact congrArg d (hw b)
  rw [universal_borel_fixed_eq_bot a ha ha1] at h
  exact hd (h.trans (map_zero d).symm)


variable {L : Type*} [Group L]

/-- The matrix Borel generates the full actual block cover by commutators. -/
theorem blockCoverAction_borel_full [Group.IsPerfect L]
    [IsElementaryAbelian 2 (ChapterC.blockU L)] [Finite F]
    (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
    (hF : Nat.card F = 4) :
    Coinvariants.ker ((blockCoverAction hshort model).comp (rankOneBorel F).subtype) = ⊤ := by
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  exact cover_borel_full (blockCoverAction hshort model)
    (blockCoverProjection hshort model) (blockCoverProjection_isCover hshort model)
    a a.ne_zero (by simpa using ha)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.CoveringLayer

end
