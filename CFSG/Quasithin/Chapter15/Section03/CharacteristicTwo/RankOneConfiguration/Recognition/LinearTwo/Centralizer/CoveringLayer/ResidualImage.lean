module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.BlockAction
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# The Borel residual has the full matrix image

Over the four-element field the diagonal torus has order three. Its normal
closure contains the upper root group, so the matrix Borel is its own
prime-to-three residual. The residual of the full block Borel has index prime
to three, since it contains a Sylow three-subgroup. Its image must therefore
be the entire matrix Borel.

This is the residual-surjectivity step in Aschbacher–Smith 15.3.30,
printed pp.1131–1132. The elementary argument is also used independently in
`Centralizer.Displacement`; no automorphism conclusion is used here.
-/

public section

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped Matrix commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.CoveringLayer
variable {L F : Type*} [Group L] [Field F]

private theorem residual_index_coprime {H : Type*} [Group H] [Finite H] :
    Nat.Coprime 3 (primeToResidual 3 H).index := by
  let P : Sylow 3 H := Classical.choice inferInstance
  have hP : (P : Subgroup H) ≤ primeToResidual 3 H := by
    intro x hx
    obtain ⟨n, hn⟩ := P.2 ⟨x, hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)
  exact (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index).coprime_dvd_right
    (index_dvd_of_le hP)

/-- The torus has order three, and its normal closure contains every upper
transvection, so the prime-to-three residual is the entire matrix Borel. -/
private theorem borel_residual [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    primeToResidual 3 (rankOneBorel F) = ⊤ := by
  classical
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b, hb⟩ := exists_ne (1 : Fˣ)
  have hb1 : (b : F) ≠ 1 := by simpa using hb
  have hbsq : (b : F) ^ 2 ≠ 1 := by
    intro he
    exact hb1 (CharTwo.sq_injective (by simpa using he))
  let N := primeToResidual 3 (rankOneBorel F)
  have hdiag (c : Fˣ) : borelDiagonalHom c ∈ N := by
    apply mem_primeToResidual_of_pow (n := 1)
    have hc : c ^ 3 = 1 := hcard ▸ pow_card_eq_one'
    simpa using congrArg (borelDiagonalHom (F := F)) hc
  have hu (t : F) : (⟨Matrix.SpecialLinearGroup.transvection zero_ne_one t, upper_mem_rankOneBorel t⟩ :
      rankOneBorel F) ∈ N := by
    let v : rankOneBorel F :=
      ⟨Matrix.SpecialLinearGroup.transvection zero_ne_one (t / ((b : F)^2 - 1)), upper_mem_rankOneBorel _⟩
    have hc : ⁅borelDiagonalHom b, v⁆ ∈ N := by
      simpa only [commutatorElement_def, mul_assoc] using
        N.mul_mem (hdiag b) ((inferInstance : N.Normal).conj_mem _ (N.inv_mem (hdiag b)) v)
    have he : ⁅borelDiagonalHom b, v⁆ =
        ⟨Matrix.SpecialLinearGroup.transvection zero_ne_one t, upper_mem_rankOneBorel t⟩ := by
      apply Subtype.ext
      exact commutator_diag2_transvection (b : F) b.ne_zero _ t
        (div_mul_cancel₀ t (sub_ne_zero_of_ne hbsq)).symm
    exact he ▸ hc
  apply top_unique
  intro g _
  obtain ⟨t, c, hc, he⟩ := rankOneBorel_factor g
  have hg : g = ⟨Matrix.SpecialLinearGroup.transvection zero_ne_one t, upper_mem_rankOneBorel t⟩ *
      borelDiagonalHom (Units.mk0 c hc) := Subtype.ext he
  rw [hg]
  exact N.mul_mem (hu t) (hdiag _)

private theorem residual_borel_lift
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) [Finite L] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (g : rankOneBorel F) :
    ∃ l ∈ blockBorelResidual model, blockLinearMap model l = g := by
  let f : blockBorel model →* rankOneBorel F :=
    { toFun l := ⟨blockLinearMap model l, l.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' l m := Subtype.ext (map_mul (blockLinearMap model) (l : L) (m : L)) }
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨l, hl⟩ := blockLinearMap_surjective model g
    exact ⟨⟨l, show blockLinearMap model l ∈ rankOneBorel F from hl.symm ▸ g.property⟩,
      Subtype.ext hl⟩
  let N := (primeToResidual 3 (blockBorel model)).map f
  have : N.Normal := Subgroup.Normal.map inferInstance f hf
  have hN : primeToResidual 3 (rankOneBorel F) ≤ N :=
    primeToResidual_le N (residual_index_coprime.coprime_dvd_right
      ((primeToResidual 3 (blockBorel model)).index_map_dvd hf))
  have hg : g ∈ N := hN (by rw [borel_residual hF]; trivial)
  obtain ⟨l, hl, he⟩ := hg
  exact ⟨l, mem_map_of_mem _ hl, congrArg Subtype.val he⟩


/-- The intrinsic residual of the full preimage surjects onto the matrix Borel. -/
theorem blockBorelResidual_image [Finite L] [Finite F] [CharP F 2]
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
    (hF : Nat.card F = 4) :
    (blockBorelResidual model).map (blockLinearMap model) = rankOneBorel F := by
  apply le_antisymm
  · rintro g ⟨l, ⟨b, _, rfl⟩, rfl⟩
    exact b.property
  · intro g hg
    exact residual_borel_lift model hF ⟨g, hg⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.CoveringLayer

end
