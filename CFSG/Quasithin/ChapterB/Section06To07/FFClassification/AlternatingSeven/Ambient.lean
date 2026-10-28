module
public import Theory.SpecificGroups.AlternatingSeven.InvariantParabolicPair
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.IntrinsicParabolics

/-!
# A normal A₇ supplement excludes minimal parabolicity

Transport the intrinsic proper generating pair through the actual marking of
the normal subgroup. Both subgroups contain the original Sylow intersection
and are normalized by the original Sylow. Their proper Sylow supplements
contradict its unique maximal overgroup. No module hypothesis is needed.

Source: Aschbacher–Smith B.6.9, printed p.116.
-/


public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem not_minimalParabolic_of_alternatingSeven_supplement
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (e : L ≃* alternatingGroup (Fin 7)) (hgen : L ⊔ (T : Subgroup G) = ⊤) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  obtain ⟨P,Q,hPQ,hP,hQ,hSP,hSQ,hinv⟩ :=
    AlternatingSeven.InvariantParabolicPair.exists_intrinsic_pair
  exact not_minimalParabolic_of_intrinsic_parabolics T L e hgen
    AlternatingSeven.DihedralLocals.fixedSylow P Q hPQ hP hQ hSP hSQ hinv
end CFSG.Quasithin.ChapterB
