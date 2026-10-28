module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.BaumannControl
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.NormalizerControl

/-!
# Assembling the Thompson control and the escaping Thompson factor

The actual maximum-elementary family of `T_E`, once shown to centralize `V`,
gives the Thompson and Baumann equalities. The control of `Baum(C_T(V))`
proved from the earlier ordering maximality then gives both ambient
normalizer bounds and promotes `T_E` to Sylow in `G_E`.

The relative Frattini argument now gives the literal product `G_E=I M_E`.
Escape of the selected line forces `I` and its image modulo `Q_E` to survive.
The family containment is a remaining geometric obligation, explicitly
retained here. These conditional deductions do not prove that containment.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
and fifth paragraphs of the proof of 15.3.67, printed p.1153.
-/

public section
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterA.Section05To06
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
variable {G : Type*} [Group G] [Finite G]

/-- All control conclusions from the specific maximum-family calculation. -/
theorem line_control_of_maximum_family (T : Sylow 2 G) (M E : Subgroup G)
    [IsElementaryAbelian 2 (localModule T M)]
    (hM : IsOrderingMaximal T M) (hVT : localModule T M ≤ (T : Subgroup G))
    (hEV : E ≤ localModule T M) (hE : E ≠ ⊥)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E)
    (hfamily : ∀ A ∈ elementaryAbelianMaxSubgroups (lineT (T : Subgroup G) E),
      A ≤ centralizer (localModule T M : Set G)) :
    elementaryAbelianMaxJ (lineT T E) = elementaryAbelianMaxJ (lineR T (localModule T M)) ∧
      lineB T E = ChapterB.baumann (lineR T (localModule T M)) ∧
      lineB T E ≤ lineR T (localModule T M) ∧
      (lineB T E).characteristicNormalizerClosure ≤ M ∧
      normalizer (lineT T E : Set G) ≤ M ∧
      normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M ∧
      ∃ U : Sylow 2 (lineNormalizer E),
        (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E := by
  have hJ : elementaryAbelianMaxJ (lineT T E) ≤ lineR T (localModule T M) :=
    le_inf ((sSup_le fun _ hA => hA.1).trans inf_le_left) (sSup_le hfamily)
  obtain ⟨hj, hb, hbr⟩ := thompson_baumann_of_centralizing (T : Subgroup G)
    (localModule T M) E hVT hEV hJ
  have hc : (lineB T E).characteristicNormalizerClosure ≤ M := by
    rw [hb]
    exact lineR_baumann_control T M hM
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hEV
  have hED : E ≤ lineT T E := le_inf (hEV.trans hVT) E.le_normalizer
  obtain ⟨hn, hjn⟩ := GoldschmidtCore.LocalRelations.lineT_normalizer_bounds
    (T : Subgroup G) E M hE hED hc
  exact ⟨hj, hb, hbr, hc, hn, hjn,
    lineT_sylow_of_normalizer_control (T : Subgroup G) M E T.isPGroup' P hP hn⟩

/-- The family calculation and the selected escape imply the original Thompson product. -/
theorem lineI_consequences_of_maximum_family (T : Sylow 2 G) (M E : Subgroup G)
    [IsElementaryAbelian 2 (localModule T M)]
    (hM : IsOrderingMaximal T M) (hVT : localModule T M ≤ (T : Subgroup G))
    (hEV : E ≤ localModule T M) (hE : E ≠ ⊥)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E)
    (hfamily : ∀ A ∈ elementaryAbelianMaxSubgroups (lineT (T : Subgroup G) E),
      A ≤ centralizer (localModule T M : Set G))
    (hescape : ¬ lineNormalizer E ≤ M) :
    (lineNormalizer E : Set G) = (lineI E : Set G) * (lineM M E : Set G) ∧
      ¬ lineI E ≤ M ∧
      ((lineI E).subgroupOf (lineNormalizer E)).map
        (QuotientGroup.mk' (pCore 2 (lineNormalizer E))) ≠ ⊥ := by
  obtain ⟨_, _, _, _, _, hjn, U, hU⟩ :=
    line_control_of_maximum_family T M E hM hVT hEV hE P hP hfamily
  have hJ : elementaryAbelianMaxJ (lineT T E) ≤ (T : Subgroup G) ⊓ lineC E :=
    le_inf ((sSup_le fun _ hA => hA.1).trans inf_le_left)
      ((sSup_le hfamily).trans (centralizer_le hEV))
  have hp := lineI_product M (T : Subgroup G) E U hU hJ hjn
  have hi := lineI_escapes M E hescape hp
  exact ⟨hp, hi, lineI_image_ne_bot M (T : Subgroup G) E hM.1.2 U hU hi⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
