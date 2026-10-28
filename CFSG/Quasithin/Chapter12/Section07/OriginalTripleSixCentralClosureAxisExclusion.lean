module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAxisData
public import CFSG.Quasithin.ChapterG.Section03.CommonAxisCyclicExclusion

/-!
# Excluding the original order-two closure automizer

The original outer branch supplies a fully moved four-group, its literal
cubic residual and the original Sylow in the faithful closure action.
The common-axis source contradicts the original cyclic point fixed by
that residual and Sylow. All ambient subgroups and the full module are
unchanged; no additional module or recognition input is required.

Source: Aschbacher--Smith12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine outer closure branch cannot induce only two automorphisms
of the original six-dimensional module. -/
theorem original_tripleSix_central_closure_automizer_not_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    Nat.card (inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G))))) ≠ 2 := by
  intro hsmall
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_axis_data
    h structural D a z hz hzT hnot houter hsmall
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,_,_,hcore,hcard,hmove,hJ,hcubic,hJN,hTN,x,_,_,hspan,hfixed,
    f,hf,_,hfix,_,_,_⟩ := hrest
  let := he
  let Q := φ.range
  let A₀ := (U.subgroupOf H).map φ
  let J₀ := (J.subgroupOf H).map φ
  let A := A₀.subgroupOf Q
  let JQ := J₀.subgroupOf Q
  have hAQ : A₀ ≤ Q := map_le_range _ _
  have hJQ : J₀ ≤ Q := map_le_range _ _
  have hAm : A.map Q.subtype = A₀ := map_subgroupOf_eq_of_le hAQ
  have hJm : JQ.map Q.subtype = J₀ := map_subgroupOf_eq_of_le hJQ
  have hcardA : Nat.card A = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAQ).toEquiv).trans hcard
  have hmoveA : A = ⁅A,JQ⁆ := by
    apply (map_injective Q.subtype_injective)
    rw [map_commutator,hAm,hJm]
    exact hmove
  let eJ : JQ ≃* J₀ := subgroupOfEquivOfLe hJQ
  have hpJ : IsPPerfect 2 JQ := hJ.of_surjective eJ.symm.toMonoidHom eJ.symm.surjective
  have hcJ : Nat.card (JQ ⧸ pCore 2 JQ) = 3 := by
    let e := QuotientGroup.congr (pCore 2 JQ) (pCore 2 J₀) eJ (pCore_map_iso 2 eJ)
    exact (Nat.card_congr e.toEquiv).trans hcubic
  have hJA : JQ ≤ normalizer (A : Set Q) :=
    (comap_mono hJN).trans (le_normalizer_comap Q.subtype)
  let S := (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)).mapSurjective
    (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hSm : (S : Subgroup Q).map Q.subtype = ((T : Subgroup G).subgroupOf H).map φ := by
    change (((T : Subgroup G).subgroupOf H).map φ.rangeRestrict).map Q.subtype = _
    rw [map_map]
    rfl
  have hSA : (S : Subgroup Q) ≤ normalizer (A : Set Q) := by
    apply le_trans _ (le_normalizer_comap Q.subtype)
    intro s hs
    exact (hTN ((hSm ▸ mem_map_of_mem Q.subtype hs))).1
  have hSJ : (S : Subgroup Q) ≤ normalizer (JQ : Set Q) := by
    apply le_trans _ (le_normalizer_comap Q.subtype)
    intro s hs
    exact (hTN ((hSm ▸ mem_map_of_mem Q.subtype hs))).2
  have haxis : A.map Q.subtype ≤ BinaryTransvectionGroups.axisRootGroup Q f := by
    rw [hAm]
    intro g hg
    refine ⟨hAQ hg,hfix g hg,?_⟩
    intro v
    change f (g v-v) = 0
    by_cases hv : f v = 0
    · rw [hfix g hg v hv,sub_self,map_zero]
    · have hgv : f (g v) ≠ 0 := by
        intro hh
        have hi := hfix g⁻¹ (A₀.inv_mem hg) (g v) hh
        change g.symm (g v) = g v at hi
        have hev : v = g v := (g.symm_apply_apply v).symm.trans hi
        exact hv ((congrArg f hev).trans hh)
      have hbit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
      rw [map_sub,(hbit (f (g v))).resolve_left hgv,(hbit (f v)).resolve_left hv,sub_self]
  have hHC : H ≤ C := (original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot).1
  let := D.elementary
  have hz1 : (z:G) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hzorder : orderOf (z:G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) hz1
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHC)).mp
      ((h.simpleQTKE.involution_centralizer_sqtk hzorder).subgroup (H.subgroupOf C))
  apply ChapterG.Section03.common_axis_cyclic_exclusion hH Q φ.rangeRestrict φ.rangeRestrict_surjective
    hcore f hf A JQ haxis hcardA hmoveA hpJ hcJ S hSA hJA hSJ x hspan
  · intro j hj
    obtain ⟨b,hb,hbj⟩ := hj
    have hh := hfixed b ((show J ≤ J ⊔ (T : Subgroup G) from le_sup_left) hb)
    rw [hbj] at hh
    exact hh
  · intro s hs
    obtain ⟨b,hb,hbs⟩ := hs
    have hh := hfixed b ((show (T : Subgroup G) ≤ J ⊔ (T : Subgroup G) from le_sup_right) hb)
    have he : φ b = s.val := congrArg Subtype.val hbs
    rw [he] at hh
    exact hh

end CFSG.Quasithin.Chapter12.Section07
