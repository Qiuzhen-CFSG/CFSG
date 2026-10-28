module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.CoordinateLifting
public import Theory.SpecificGroups.OrthogonalFourBinary.IndexTwoNormalizer

/-!
# The normalizer of the terminal line Sylow intersection

The compatible orthogonal action sends the ambient Sylow subgroup `T` to a
Sylow subgroup of the full quadratic-isometry group. Its kernel is `C_M(V)`.
From `R = C_G(V) = C_T(V)` and `E ≤ V`, that kernel lies in `T_E`, so the
source index `[T : T_E] = 2` survives in the image. The finite orthogonal
calculation gives the image normalizer exactly; lifting gives `N_M(T_E) = T`.

The finite theorem applies to every index-two subgroup. Thus this step needs
only the index conclusion of 15.3.66, and applies in particular to its actual
specified image `T̄ ∩ Ω₄⁺(V)`. All images use the supplied `NaturalAction`.
The proof of 15.3.66 and the maximal-local Sylow assertion remain with their
owners; neither is assumed as the normalizer conclusion here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.2(1),
15.3.66(1)–(3), 15.3.67(1), and the proof of 15.3.68(3), printed
pp.1121–1122 and 1152–1154.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

/-- Sylow restriction to `M` and surjective transport through the specified action. -/
theorem actionImage_sylow (d : OrthogonalFourBinary.NaturalAction V M)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) :
    ∃ P : Sylow 2 OrthogonalFourBinary.IndexTwoNormalizer.IsometryGroup,
      (P : Subgroup _) = actionImage d (T : Subgroup G) :=
  ⟨(T.subtype hTM).mapSurjective d.onto, rfl⟩

omit [Finite G] in
/-- Since `E ≤ V`, the action kernel is contained in `T_E`; its index is preserved. -/
theorem lineT_actionImage_relIndex (d : OrthogonalFourBinary.NaturalAction V M)
    (T : Subgroup G) (E : Subgroup G) (hTM : T ≤ M)
    (hCT : centralizer (V : Set G) ≤ T) (hEV : E ≤ V) :
    (actionImage d (lineT T E)).relIndex (actionImage d T) = (lineT T E).relIndex T := by
  have hCE : centralizer (V : Set G) ≤ lineT T E :=
    le_inf hCT ((centralizer_le hEV).trans (centralizer_le_normalizer (E : Set G)))
  have hkE : d.action.ker ≤ (lineT T E).subgroupOf M := by
    rw [action_ker d]
    exact fun _ hm => hCE hm
  have hkT : d.action.ker ≤ T.subgroupOf M :=
    hkE.trans (subgroupOf_mono M (show lineT T E ≤ T from inf_le_left))
  rw [actionImage, actionImage, relIndex_map_map,
    sup_of_le_left hkE, sup_of_le_left hkT, relIndex_subgroupOf hTM]

/-- The finite orthogonal normalizer calculation for the actual action image. -/
theorem lineT_actionImage_normalizer_eq
    (d : OrthogonalFourBinary.NaturalAction V M) (T : Sylow 2 G) (E : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hCT : centralizer (V : Set G) ≤ (T : Subgroup G))
    (hEV : E ≤ V) (hi : (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2) :
    normalizer (actionImage d (lineT (T : Subgroup G) E) : Set _) =
      actionImage d (T : Subgroup G) := by
  obtain ⟨P,hP⟩ := actionImage_sylow d T hTM
  have hle : actionImage d (lineT (T : Subgroup G) E) ≤ (P : Subgroup _) := by
    rw [hP]
    exact map_mono (subgroupOf_mono M (show lineT (T : Subgroup G) E ≤ (T : Subgroup G)
      from inf_le_left))
  have hi' : (actionImage d (lineT (T : Subgroup G) E)).relIndex (P : Subgroup _) = 2 := by
    rw [hP, lineT_actionImage_relIndex d (T : Subgroup G) E hTM hCT hEV, hi]
  rw [OrthogonalFourBinary.IndexTwoNormalizer.normalizer_eq P
    (actionImage d (lineT (T : Subgroup G) E)) hle hi', hP]

/-- Lift the computed image normalizer through the actual action kernel. -/
theorem lineT_normalizer_eq_of_centralizer_le
    (d : OrthogonalFourBinary.NaturalAction V M) (T : Sylow 2 G) (E : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hCT : centralizer (V : Set G) ≤ (T : Subgroup G))
    (hEV : E ≤ V) (hi : (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2) :
    M ⊓ normalizer (lineT (T : Subgroup G) E : Set G) = (T : Subgroup G) := by
  have hN := lineT_actionImage_normalizer_eq d T E hTM hCT hEV hi
  apply le_antisymm
  · exact lineT_normalizer_of_action_bound d (T : Subgroup G) E hTM
      (inf_le_right.trans hCT) hN.le
  · exact le_inf hTM
      ((normal_subgroupOf_iff_le_normalizer (show lineT (T : Subgroup G) E ≤
        (T : Subgroup G) from inf_le_left)).mp (normal_of_index_eq_two hi))

/-- The source setup, with the actual ambient and relative centralizers retained. -/
theorem lineT_normalizer_eq
    (d : OrthogonalFourBinary.NaturalAction V M) (T : Sylow 2 G) (R E : Subgroup G)
    (hM : M = normalizer (V : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hEV : E ≤ V)
    (hR : R = centralizer (V : Set G))
    (hRT : R = (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hi : (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2) :
    M ⊓ normalizer (lineT (T : Subgroup G) E : Set G) = (T : Subgroup G) := by
  have hTM : (T : Subgroup G) ≤ M := by rwa [hM]
  apply lineT_normalizer_eq_of_centralizer_le d T E hTM _ hEV hi
  rw [← hR, hRT]
  exact inf_le_left

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
