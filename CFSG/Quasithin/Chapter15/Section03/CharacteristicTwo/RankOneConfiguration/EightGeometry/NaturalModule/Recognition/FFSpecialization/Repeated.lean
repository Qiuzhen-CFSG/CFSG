module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.ModelCases
public import Theory.SpecificGroups.BinaryLinear.NestedRadicals


/-!
# Excluding repeated natural summands at a marked middle parabolic

Choose the one-dimensional member A of the flag of types {1,3}. Its
unipotent radical lies in the flag stabilizer and is a two-group, so it
fixes a nonzero vector of the moving line. In every natural coordinate,
that vector lies in A. The entire flag stabilizer fixes a binary line
pointwise, contradicting the moving line's disjointness from Y-fixed
vectors. The argument works for any number of natural summands.

The component isomorphism must be the one in the parabolic marking. A
classification using a different isomorphism must first transport the
flag; equality of abstract group types does not suffice.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1)(iv)
and the first paragraph of the proof of 15.3.32, printed pp.99 and 1132.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
open Chapter2.ComponentRefinement.LieType.Binary

private theorem fixes_binary_line {A : Space 4} (hA : Module.finrank (ZMod 2) A = 1)
    {g : BinaryLinear.GL (Vector 4)} (hg : g ∈ BinaryLinear.parabolic A)
    {v : Vector 4} (hv : v ∈ A) : g v = v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hA hv hv0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ (hg v).mpr hv)
  have hc0 : c ≠ 0 := by
    intro hz
    exact hv0 (g.map_eq_zero_iff.mp (by simpa [hz] using hc.symm))
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) K V} {L P S Y : Subgroup K}

/-- The moving line excludes every number of repeated natural summands in
coordinates whose model describes the same marked middle parabolic. -/
theorem RepeatedNatural.not_movingLine {r : ℕ} (h : RepeatedNatural ρ L r)
    (mark : Models.MiddleNodeMarking L P) (hm : h.model = mark.model)
    (line : Models.MovingLine ρ P S Y) (hY : Y ≤ P) : False := by
  classical
  obtain ⟨A, hAF, hAd⟩ := Finset.mem_image.mp
    (show 1 ∈ mark.flag.types by rw [mark.middle]; simp)
  have hAW (W : Space 4) (hW : W ∈ mark.flag.spaces) : A ≤ W := by
    rcases mark.flag.chain A hAF W hW with hle | hle
    · exact hle
    · have hd : Module.finrank (ZMod 2) W ∈ ({1, 3} : Finset ℕ) := by
        rw [← mark.middle]
        exact Finset.mem_image.mpr ⟨W, hW, rfl⟩
      have hd' := Submodule.finrank_mono hle
      have he : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) A := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        omega
      exact (Submodule.eq_of_le_of_finrank_eq hle he).ge
  have hmem (l : L) : (l : K) ∈ P ↔
      ∀ W ∈ mark.flag.spaces, linearModel mark.model l ∈ BinaryLinear.parabolic W := by
    conv_lhs => rw [mark.parabolic]
    change L.subtype l ∈ (flagStabilizer mark.model mark.flag).map L.subtype ↔ _
    rw [Subgroup.mem_map_iff_mem (Subtype.val_injective), mem_flagStabilizer]
    rfl
  let Q := BinaryLinear.radical A
  have hQ : IsPGroup 2 Q := BinaryLinear.radical_two A
  have hQP (g : Q) : ((linearModel mark.model).symm g.val : K) ∈ P := by
    apply (hmem _).mpr
    intro W hW
    rw [MulEquiv.apply_symm_apply]
    exact BinaryLinear.radical_le_nested_parabolic (hAW W hW) g.property
  let actor : Q →* L := (linearModel mark.model).symm.toMonoidHom.comp Q.subtype
  let : MulAction Q line.space := {
    smul g v := ⟨ρ (actor g) v.val, line.parabolic_stable _ (hQP g) _ v.property⟩
    one_smul v := Subtype.ext (by
      change ρ (actor 1 : K) v.val = v.val
      simp)
    mul_smul g g' v := Subtype.ext (by
      change ρ (actor (g * g') : K) v.val = ρ (actor g : K) (ρ (actor g' : K) v.val)
      rw [map_mul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]) }
  have : Finite line.space := Nat.finite_of_card_ne_zero (by rw [line.card]; decide)
  have hz : (0 : line.space) ∈ MulAction.fixedPoints Q line.space := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    exact (ρ (actor g)).map_zero
  obtain ⟨v, hv, hv0⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    line.space (by rw [line.card]; decide) hz
  have hvA (i : Fin r) : h.coordinates v.val i ∈ A := by
    apply (BinaryLinear.mem_iff_fixed_radical (mark.flag.proper A hAF).1 _).mpr
    intro g hg
    have he : ρ (actor ⟨g, hg⟩) v.val = v.val :=
      congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hv) ⟨g, hg⟩)
    have he' := congrArg (fun w => h.coordinates w i) he
    rw [h.equivariant, hm] at he'
    change linearModel mark.model ((linearModel mark.model).symm g)
      (h.coordinates v.val i) = h.coordinates v.val i at he'
    simpa only [MulEquiv.apply_symm_apply] using he'
  have hvfix : v.val ∈ fixedSpace ρ Y := by
    intro y
    have hPL : P ≤ L := mark.parabolic ▸ ambientFlagStabilizer_le mark.model mark.flag
    let l : L := ⟨y.val, hPL (hY y.property)⟩
    apply h.coordinates.injective
    funext i
    change h.coordinates (ρ (l : K) v.val) i = _
    rw [h.equivariant, hm]
    exact fixes_binary_line hAd ((hmem l).mp (hY y.property) A hAF) (hvA i)
  have he : v.val = 0 := Submodule.disjoint_def.mp line.fixed_disjoint v.val v.property hvfix
  exact hv0 (Subtype.ext he.symm)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
