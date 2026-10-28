module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBorel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalReduction

/-!
# The terminal central line in the Cartan join

The full left Borel is the original point centralizer. When H centralizes
that point, V₁ is a nontrivial central two-subgroup of DH for each subgroup
D of the compatible left Cartan. Local Cartan control therefore forces
the full original Borel to normalize O²(H), without prime selection or a
model comparison.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H A B D : Subgroup G}

/-- The actual terminal central line gives a nontrivial core in every
sub-Cartan join with the original H. -/
theorem original_terminal_cartan_join_core_ne_bot
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G))
    (c : CartanPair T L H A B) (hDA : D ≤ A) :
    (D ⊔ H).pCoreIn 2 ≠ ⊥ := by
  have hVT : V₁ ≤ (T : Subgroup G) :=
    d.flag.one_le_two.trans (d.flag.two_le_V.trans d.flag.V_le_T)
  have hBC : localBorel T L ≤ centralizer (V₁ : Set G) := by
    change ChapterF.Source.borel L (T : Subgroup G) ≤ _
    rw [d.borel_eq_point_centralizer]
    exact inf_le_right
  have hNC : D ⊔ H ≤ centralizer (V₁ : Set G) :=
    sup_le (hDA.trans (c.left_le.trans hBC)) hHC
  have hVcore : V₁ ≤ (D ⊔ H).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hVT)
      ((hVT.trans hH.1.1.2).trans le_sup_right)
      (hNC.trans (Subgroup.centralizer_le_normalizer _))
  intro he
  have hv : V₁ = ⊥ := bot_unique (hVcore.trans_eq he)
  have hc := d.flag.one_card
  rw [hv] at hc
  norm_num at hc

/-- Local Cartan control and the actual terminal line force normalization
by the whole original relative Borel. -/
theorem original_terminal_borel_normalizes_of_local_control
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G))
    (c : CartanPair T L H A B) (hc : CartanLocalControl A H) :
    localBorel T L ≤ normalizer (residual H : Set G) := by
  rw [←c.left_sup_intersection d.normalizes_L]
  exact sup_le (inf_le_left.trans (hH.1.1.2.trans (le_normalizer_residual H)))
    (hc A le_rfl (original_terminal_cartan_join_core_ne_bot d hH hHC c le_rfl))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
