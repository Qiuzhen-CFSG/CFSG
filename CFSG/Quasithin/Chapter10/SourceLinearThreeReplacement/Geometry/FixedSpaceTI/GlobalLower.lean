module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Pair
public import Theory.GroupTheory.FixedSupplementCentralizer

/-!
# The global-centralizer parameter in the nonzero-fixed branch

If the full fixed part is nonzero, the first moved factor has nonzero
L-fixed part: otherwise the crossed, exchanged factors would force every
full fixed vector to be trivial. Its natural quotient has order eight,
so the moved factor has order at least sixteen. Original point-centralizer
control then gives r(G,V) ≥ 4. Only the involution displacement bound on
the actual full automizer remains to obtain s(G,V)>1.

Source: Aschbacher--Smith 10.3.1, printed p.755, using10.2.9(2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (s : SourceLinearThreeSurvivor T D)

include s

/-- Nonzero full fixed space forces a nonzero fixed denominator in the natural section. -/
theorem moved_fixed_ne_bot
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro he
  let W := ⁅D.fullModule,L⁆
  let B := W.map (MulAut.conj s.exchange).toMonoidHom
  let F := D.fullModule ⊓ centralizer (localOrbit T L : Set G)
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hBW : B ≤ normalizer (W : Set G) :=
    (show B ≤ centralizer (W : Set G) from fun b hb w hw =>
      congrArg Subtype.val (mul_comm (⟨w,survivor_moved_le s hw⟩ : D.fullModule)
        ⟨b,survivor_partner_le s hb⟩)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hfixed : D.fullModule ⊓ centralizer (L : Set G) = B := by
    rw [s.generated, sup_comm]
    rw [inf_centralizer_sup_of_centralizing B W L hBW s.crossed, he, sup_bot_eq]
  have hFB : F ≤ B := (inf_le_inf_left _ (centralizer_le (le_componentOrbit L T))).trans_eq hfixed
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (le_inf ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
      ((le_normalizer_componentOrbit L T).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  apply hfix
  apply bot_unique
  intro x hx
  have htx : (MulAut.conj s.exchange) x ∈ F := by
    have hm := mem_normalizer_iff_map_conj_eq.mp (hTF s.exchange_mem)
    rw [← hm]
    exact mem_map_of_mem _ hx
  obtain ⟨w,hw,heq⟩ := hFB htx
  have hwx : w = x := (MulAut.conj s.exchange).injective heq
  exact he.le ⟨hwx ▸ hw, (centralizer_le (le_componentOrbit L T)) hx.2⟩

/-- The actual natural section and original point centralizers give r(G,V) ≥ 4. -/
theorem globalR_ge_four_of_fixed_ne_bot
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    (4 : ℕ∞) ≤ globalR D.fullModule := by
  have hn := (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G).one_lt_card_iff_ne_bot.mpr
    (moved_fixed_ne_bot D s hfix)
  have hc := s.natural.card_section
  simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hc
  norm_num at hc
  have hsize : 16 ≤ Nat.card (⁅D.fullModule,L⁆ : Subgroup G) := by
    change Nat.card (⁅D.fullModule,L⁆ : Subgroup G) =
      8 * Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) at hc
    omega
  have hr := source_fullModule_globalR_lower_of_element_centralizers D
    (survivor_moved_le s) s.pointCentralizers
  have hlog : 4 ≤ Nat.log 2 (Nat.card (⁅D.fullModule,L⁆ : Subgroup G)) := by
    have := Nat.log_mono_right (b := 2) hsize
    norm_num at this
    exact this
  exact le_trans (by exact_mod_cast hlog) hr
/-- The centralizer parameter is already large enough; a lower bound on the
actual automizer's involution displacement completes the source s-bound. -/
theorem globalS_gt_one_of_localM_gt_one
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hm : letI : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
      1 < localM D.fullModule) :
    letI : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
    1 < globalS D.fullModule := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  apply lt_min
  · exact lt_of_lt_of_le (by norm_num) (globalR_ge_four_of_fixed_ne_bot D s hfix)
  · exact_mod_cast hm

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
