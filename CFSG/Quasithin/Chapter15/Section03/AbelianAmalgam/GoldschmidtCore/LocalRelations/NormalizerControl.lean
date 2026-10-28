module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Basic
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.CharacteristicNormalizerClosure

/-!
# Normalizer control and Thompson normality for the terminal amalgam

The control in 15.3.67(2) is the characteristic-normalizer closure of
`Baum(T_E)`. Its nontrivial characteristic Thompson subgroup gives the
bound for `N_G(J(T_E))`, while characteristicity of the Baumann subgroup
gives the bound for `N_G(T_E)`. The core identity `O₂(M)=R` and
`J(T_E)≤R≤T_E` make `J(T_E)=J(R)` normal in the first local group.

These implications take the genuine earlier controls explicitly. They
neither assert the local quotient calculations nor assemble 15.3.68.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.67(2) and the proof of 15.3.68, printed pp.1153–1155.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem thompson_le (D : Subgroup G) : elementaryAbelianMaxJ D ≤ D :=
  sSup_le fun _ hA => hA.1

omit [Finite G] in
private theorem thompson_le_baumann (D : Subgroup G) :
    elementaryAbelianMaxJ D ≤ ChapterB.baumann D := by
  refine le_inf (thompson_le D) ?_
  intro j hj
  apply mem_centralizer_iff.mpr
  intro w hw
  obtain ⟨wJ, hwJ, rfl⟩ := hw
  obtain ⟨wZ, _, rfl⟩ := hwJ
  exact congrArg Subtype.val ((mem_center_iff.mp wZ.property) ⟨j, hj⟩).symm

private theorem thompson_eq_of_intermediate (D R : Subgroup G)
    (hJR : elementaryAbelianMaxJ D ≤ R) (hRD : R ≤ D) :
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ D := by
  have hs := elementaryAbelianMaxOrder_le_and_j_le_of_eq R D hRD
  have hl := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le D R hJR
  have he := le_antisymm hs.1 hl.1
  exact le_antisymm (hs.2 he) (hl.2 he.symm)

private theorem thompson_ne_bot_of_elementary (D A : Subgroup G)
    (hAD : A ≤ D) [IsElementaryAbelian 2 A] (hA : A ≠ ⊥) :
    elementaryAbelianMaxJ D ≠ ⊥ := by
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty D
  intro h
  have hb : B = ⊥ := le_bot_iff.mp (h ▸ le_sSup hB)
  have hc := hB.2.2 A hAD inferInstance
  rw [hb, Subgroup.card_bot] at hc
  have ha : Nat.card A = 1 := le_antisymm hc Nat.card_pos
  exact hA (card_eq_one.mp ha)

/-- The characteristic-normalizer closure from 15.3.67(2) controls both
normalizers. The Thompson subgroup is characteristic in the Baumann subgroup
because both have the same maximum elementary subgroups. -/
theorem lineT_normalizer_bounds (T E M : Subgroup G)
    [IsElementaryAbelian 2 E] (hE : E ≠ ⊥) (hED : E ≤ lineT T E)
    (hcontrol : (ChapterB.baumann (lineT T E)).characteristicNormalizerClosure ≤ M) :
    normalizer (lineT T E : Set G) ≤ M ∧
      normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M := by
  let D := lineT T E
  let B := ChapterB.baumann D
  have hj : elementaryAbelianMaxJ D ≠ ⊥ :=
    thompson_ne_bot_of_elementary D E hED hE
  have hb : B ≠ ⊥ := fun h => hj (le_bot_iff.mp (h ▸ thompson_le_baumann D))
  have he : elementaryAbelianMaxJ B = elementaryAbelianMaxJ D :=
    thompson_eq_of_intermediate D B (thompson_le_baumann D) inf_le_left
  let C : Subgroup B := elementaryAbelianMaxJ ⊤
  let : C.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have hm : C.map B.subtype = elementaryAbelianMaxJ D := by
    rw [show C = elementaryAbelianMaxJ ⊤ from rfl,
      ← elementaryAbelianMaxJ_map_injective B.subtype B.subtype_injective,
      ← MonoidHom.range_eq_map, subtype_range, he]
  have hc : C ≠ ⊥ := by
    intro h
    apply hj
    rw [← hm, h, Subgroup.map_bot]
  refine ⟨(normalizer_le_normalizer_baumann D).trans
    ((normalizer_le_characteristicNormalizerClosure_self B hb).trans hcontrol), ?_⟩
  rw [← hm]
  exact (normalizer_le_characteristicNormalizerClosure B C hc).trans hcontrol

omit [Finite G] in
private theorem normalizer_le_normalizer_thompson (R : Subgroup G) :
    normalizer (R : Set G) ≤ normalizer (elementaryAbelianMaxJ R : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  exact (elementaryAbelianMaxJ_map_equiv (MulAut.conj x) R).symm.trans
    (congrArg elementaryAbelianMaxJ hx)

/-- The earlier identity `O₂(YT)=R`, together with `M=YT` and `J(T_E)≤R`,
makes `J(T_E)` normal in the first local group. All normality is relative. -/
theorem firstAmalgam_thompson_normal (M Y T V E F : Subgroup G)
    (hYM : Y ≤ M) (hTM : T ≤ M)
    (hcore : Stellmacher.twoCoreAmbient M = T ⊓ centralizer (V : Set G))
    (hEV : E ≤ V)
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ T ⊓ centralizer (V : Set G)) :
    ((elementaryAbelianMaxJ (lineT T E)).subgroupOf
      (firstAmalgamGroup Y T E F)).Normal := by
  let R := T ⊓ centralizer (V : Set G)
  have hRD : R ≤ lineT T E := le_inf inf_le_left
    (inf_le_right.trans ((centralizer_le hEV).trans (Subgroup.centralizer_le_normalizer _)))
  have he := thompson_eq_of_intermediate (lineT T E) R hJ hRD
  have hMN : M ≤ normalizer (R : Set G) := by
    change M ≤ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)
    rw [← hcore]
    exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hG : firstAmalgamGroup Y T E F ≤ M :=
    sup_le ((lineY_le Y F).trans inf_le_left |>.trans hYM) (inf_le_left.trans hTM)
  apply (normal_subgroupOf_iff_le_normalizer
    ((thompson_le _).trans (show lineT T E ≤ firstAmalgamGroup Y T E F from le_sup_right))).mpr
  rw [← he]
  exact hG.trans (hMN.trans (normalizer_le_normalizer_thompson R))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
