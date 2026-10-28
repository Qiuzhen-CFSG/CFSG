module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Model

/-!
# Lifting one conjugated binary flag

The image of any two-subgroup lies in a conjugate of the standard Borel,
by Sylow conjugacy in SL₃(2). Only the flag changes; the given projection
is fixed throughout. A homomorphism with two-group kernel pulls that
Borel back to an actual Sylow two-subgroup. The two parabolic preimages
generate the ambient group when the projection is surjective.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.827--828.
-/

public section

open Subgroup Matrix.PSL3Two
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93

variable {M : Type*} [Group M]

/-- The whole inverse image of the marked Borel is a Sylow subgroup. -/
noncomputable def liftedBorelSylow (π : M →* SL) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (g : SL) : Sylow 2 M :=
  (modelBorelSylow g).comapOfKerIsPGroup π hk (by
    rw [π.range_eq_top_of_surjective hπ]
    exact le_top)

theorem coe_liftedBorelSylow (π : M →* SL) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (g : SL) :
    (liftedBorelSylow π hπ hk g : Subgroup M) = (modelBorel g).comap π := by
  change (modelBorelSylow g : Subgroup SL).comap π = _
  rw [coe_modelBorelSylow]

/-- Sylow conjugacy changes the flag and leaves the specified projection fixed. -/
theorem exists_flag_of_two_subgroup (R : Subgroup M) (hR : IsPGroup 2 R)
    (π : M →* SL) : ∃ g : SL, R ≤ (modelBorel g).comap π := by
  obtain ⟨S, hS⟩ := (hR.map π).exists_le_sylow
  let B : Sylow 2 SL := Sylow.ofCard borelSL (by
    rw [card_borelSL, card_SL]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL B S
  have hB : modelBorel g = (S : Subgroup SL) := by
    rw [modelBorel_eq_map]
    change ((g • B : Sylow 2 SL) : Subgroup SL) = (S : Subgroup SL)
    rw [hg]
  refine ⟨g, ?_⟩
  rw [hB]
  exact map_le_iff_le_comap.mp hS

theorem parabolic_generation (π : M →* SL) (hπ : Function.Surjective π) (g : SL) :
    parabolic π g false ⊔ parabolic π g true = ⊤ := by
  unfold parabolic
  rw [comap_sup_eq π _ _ hπ, modelParabolic_generation, comap_top]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
