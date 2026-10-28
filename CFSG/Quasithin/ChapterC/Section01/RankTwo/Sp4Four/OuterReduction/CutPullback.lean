module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.GraphCut
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.CharacteristicCut
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Pulling the source graph cut back to the actual replacement

The distinguished graph vertices have literal residual and two-core images.
Injectivity of the original group embedding reflects their centralizer cut.
Applying characteristic minimality then identifies the intrinsic star
centralizer with the whole radical. No ambient quotient or central attachment
is replaced.

Source: MS93 (3.4), p.869, and Section 7, p.933.
-/

public section

open Subgroup Representation Representation.OneCohomology
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {G : Type*} [Group G] [Finite G]

theorem centralizer_cut_of_graph_cut
    (A T Zstar : Subgroup G) (hp : IsPGroup 2 T)
    (hQT : pCore 2 G ≤ T) (hres : pResidual 2 G = A)
    (hcut : (Ltilde T (alpha T) ⊔ (Q T (beta T) ⊓
      centralizer (Zstar.map (embedM T) : Set (FreeAmalgam T)))) ⊓ Q T (alpha T) ≤
        Q T (beta T) ⊓ centralizer (Zstar.map (embedM T) : Set (FreeAmalgam T))) :
    (A ⊔ (T ⊓ centralizer (Zstar : Set G))) ⊓ pCore 2 G ≤
      T ⊓ centralizer (Zstar : Set G) := by
  apply (map_le_map_iff_of_injective (embedM_injective T)).mp
  rw [map_inf _ _ _ (embedM_injective T),Subgroup.map_sup,
    ← map_inf_centralizer_of_injective (embedM T) (embedM_injective T)]
  rw [Ltilde_alpha,hres,Q_beta,Q_alpha T hp hQT] at hcut
  exact hcut

theorem starCentralizer_eq_top_of_graph_cut
    (A T : Subgroup G) (hp : IsPGroup 2 T)
    (hQT : pCore 2 G ≤ T) (hres : pResidual 2 G = A)
    (hmin : CharacteristicMinimal A T) (Y : Subgroup T)
    (hcut : (Ltilde T (alpha T) ⊔ (Q T (beta T) ⊓
      centralizer (((starSpan T Y).map T.subtype).map (embedM T) : Set (FreeAmalgam T)))) ⊓
        Q T (alpha T) ≤ Q T (beta T) ⊓
          centralizer (((starSpan T Y).map T.subtype).map (embedM T) : Set (FreeAmalgam T))) :
    starCentralizer T Y = ⊤ :=
  starCentralizer_eq_top_of_minimal A T hmin Y
    (centralizer_cut_of_graph_cut A T _ hp hQT hres hcut)

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
