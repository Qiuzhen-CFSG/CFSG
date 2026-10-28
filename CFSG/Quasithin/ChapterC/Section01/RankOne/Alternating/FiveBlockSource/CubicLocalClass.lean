module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicBaumannSpan
public import Theory.SpecificGroups.SymmetricTwoResidual
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.Setup

/-!
# The cubic local class from the original omega-center span

For a characteristic-two group with a Sylow two-subgroup of index three,
Thompson movement of the canonical omega-center span constructs the actual
Glauberman--Niles local-class inclusion.  The soluble FF calculation gives the
four-element residual commutator; the Baumann subgroup supplies the Sylow of
the selected residual join.  Thus the universal characteristic pair applies
without an assumed natural-module or local-class certificate.

This is the cubic selection step in C.1.21, used in C.1.23--24, printed
pp. 128--130 of the quasithin manuscript.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem residual_moved_four_of_full_moved_four
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hr : Nat.card (pResidual 2 (G ⧸ centralizer (V : Set G))) = 3)
    (hfull : Nat.card (⁅V,(⊤ : Subgroup G)⁆ : Subgroup G) = 4) :
    Nat.card (⁅V,pResidual 2 G⁆ : Subgroup G) = 4 := by
  let C := centralizer (V : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hker := QuotientGroup.ker_mk' C
  let ρ := NormalElementaryQuotient.representation V q hq hker
  let W := ⁅V,pResidual 2 G⁆
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left V _)
  have he := NormalElementaryQuotient.movedEquiv V q hq hker (pResidual 2 G)
  have hd : 2 ≤ Module.finrank (ZMod 2) (Additive W) := by
    rw [he.finrank_eq]
    apply two_le_finrank_subspaceCommutator_of_card_three ρ _
      (NormalElementaryQuotient.representation_injective V q hq hker)
    rw [map_pResidual_of_surjective 2 q hq]
    exact hr
  have hlo : 4 ≤ Nat.card W := by
    change 4 ≤ Nat.card (Additive W)
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
  have hhi : Nat.card W ≤ 4 := by
    rw [←hfull]
    exact Nat.card_le_card_of_injective (inclusion
      (commutator_mono le_rfl le_top : W ≤ ⁅V,(⊤ : Subgroup G)⁆)) (inclusion_injective _)
  exact le_antisymm hhi hlo

/-- The selected local-class witness is constructed from the actual
index-three Sylow, characteristic two, and original omega-center span. -/
theorem cubic_inLocalClass (T : Sylow 2 G)
    (hi : (T : Subgroup G).index = 3)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G) :
    GlaubermanNiles.InLocalClass (inclusion
      (show baumann (T : Subgroup G) ≤ pResidual 2 G ⊔ baumann (T : Subgroup G) from le_sup_right)) := by
  let B := baumann (T : Subgroup G)
  let N := pResidual 2 G ⊔ B
  let e := inclusion (show B ≤ N from le_sup_right)
  obtain ⟨⟨S,hS,hiS⟩,hfitN,hV,hker,hmove⟩ := cubic_baumann_span T hi U hU hJ hspan hfit
  let : IsElementaryAbelian 2 (GlaubermanNiles.localV e) := hV
  have hgen := pResidual_sup_sylow_eq_top T
  let : N.Normal := baumann_residual_join_normal (T : Subgroup G) (pResidual 2 G) hgen
  have hmapS : (S : Subgroup N).map N.subtype = B := by
    rw [←hS,MonoidHom.map_range,show N.subtype.comp e = B.subtype from rfl,range_subtype]
  have hnot : ¬ (S : Subgroup N).Normal := by
    intro hn
    have hSq : (S : Subgroup N) ≤ pCore 2 N := le_sSup ⟨hn,S.isPGroup'⟩
    have hqG : (pCore 2 N).map N.subtype ≤ pCore 2 G :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map N.subtype⟩
    have hBq : B ≤ pCore 2 G := hmapS ▸ (map_mono hSq).trans hqG
    apply hJ
    exact (elementaryAbelianMaxJ_le_baumann (T : Subgroup G)).trans
      (hBq.trans (le_centralizer_iff.mp hU.le_centralizer_pCore))
  have hmax : IsCoatom (S : Subgroup N) := by
    refine ⟨fun he => by simp [he] at hiS,fun M hSM => ?_⟩
    have hd := index_dvd_of_le hSM.le
    rw [hiS] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact index_eq_one.mp h1
    · have hh := index_strictAnti hSM
      omega
  have hmin : IsMinimalParabolicOver S ⊤ :=
    (isMinimalParabolicOver_top_iff S).mpr
      ⟨⟨S,⟨hmax,le_rfl⟩,fun M hM => (hmax.le_iff_eq hM.1.1).mp hM.2⟩,hnot⟩
  have hproper : pCore 2 N < (S : Subgroup N) := by
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
    intro he
    exact hnot (he ▸ inferInstance)
  obtain ⟨a⟩ := sylow_index_three_core_quotient S hiS hproper
  let b := (QuotientGroup.quotientMulEquivOfEq hker).trans a
  have hr : Nat.card (pResidual 2 (GlaubermanNiles.LocalStar e)) = 3 := by
    rw [←card_map_of_injective (f:=b.toMonoidHom) b.injective,map_pResidual_of_surjective 2 b.toMonoidHom b.surjective,
      Equiv.Perm.twoResidual_eq_alternating]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hc : Nat.card (⁅GlaubermanNiles.localV e,(⊤ : Subgroup N)⁆ : Subgroup N) = 4 := by
    rw [←card_map_of_injective N.subtype_injective,hmove]
    exact (reduced_index_three_baumann T hi U hU hJ).2.2
  exact GlaubermanNiles.inLocalClass_of_cubic_residual e (inclusion_injective _)
    ⟨S,hS,hmin⟩ hfitN hker hr (residual_moved_four_of_full_moved_four _ hr hc)
/-- The canonical omega-center span supplies its own reduced module; no
local-class or natural-module witness is an input. -/
theorem cubic_omega_inLocalClass (T : Sylow 2 G)
    (hi : (T : Subgroup G).index = 3)
    (hfit : generalizedFitting G = pCore 2 G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G)) :
    GlaubermanNiles.InLocalClass (inclusion
      (show baumann (T : Subgroup G) ≤ pResidual 2 G ⊔ baumann (T : Subgroup G) from le_sup_right)) := by
  let U := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  have hU := omegaCenter_normalClosure_reduced T ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  let : IsElementaryAbelian 2 U := hU.elementary
  exact cubic_inLocalClass T hi U hU hJ rfl hfit

/-- Apply the single preselected universal characteristic pair to the
constructed original cubic local class. -/
theorem cubic_omega_characteristicPair (T : Sylow 2 G)
    (hi : (T : Subgroup G).index = 3)
    (hfit : generalizedFitting G = pCore 2 G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) :
    GlaubermanNiles.Alternatives D.first D.second (inclusion
      (show baumann (T : Subgroup G) ≤ pResidual 2 G ⊔ baumann (T : Subgroup G) from le_sup_right)) :=
  hD _ _ (cubic_omega_inLocalClass T hi hfit hJ)

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
