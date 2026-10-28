module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.LinearThree.Frattini
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.LinearThree.CubicLengthIndependent

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.LinearThree.Frattini`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Representation.FrattiniAction Representation.BinaryFixedPoints
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The marked original component cannot survive the cubic chief-factor bound on Q/V. -/
theorem Context.linearThree_false (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) : False := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨n,hnJ,hnL,ho,hn,hAQ,hnormal,hfour⟩ :=
    s.exists_cubic_quotient_index_four_without_ms d J j
  let := hnormal
  let X := Q ⧸ V.subgroupOf Q
  let := quotientConjugationAction (zpowers n.val) Q V hAQ (zpowers_le.mpr n.property)
  change (FixedPoints.subgroup (zpowers n.val) X).index = 4 at hfour
  let aOuter : zpowers n.val →* MulAut X := MulDistribMulAction.toMulAut _ _
  have hLQ : L ≤ normalizer (Q : Set G) :=
    le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
        (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
  let := quotientConjugationAction L Q V hLQ s.chosen.normalizes
  let a : L →* MulAut X := MulDistribMulAction.toMulAut _ _
  let c : L := ⟨n.val,hnL⟩
  let z : zpowers n.val := ⟨n.val,mem_zpowers n.val⟩
  have hAL : zpowers n.val ≤ L := zpowers_le.mpr hnL
  have hacts (r : zpowers n.val) : aOuter r = a (inclusion hAL r) := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  have hz : z ≠ 1 := by
    intro he
    have he' : n.val = 1 := congrArg Subtype.val he
    rw [he',orderOf_one] at ho
    contradiction
  have hcard : Nat.card (zpowers n.val) = 3 := by rw [Nat.card_zpowers,ho]
  have hgen : zpowers z = ⊤ := zpowers_eq_top_of_prime_card hcard hz
  have hac : a c ≠ 1 := by
    intro he
    have hoz : aOuter z = 1 := (hacts z).trans he
    have hker : aOuter.ker = ⊤ := top_unique (by
      rw [← hgen]
      exact zpowers_le.mpr hoz)
    have htop : FixedPoints.subgroup (zpowers n.val) X = ⊤ := by
      apply top_unique
      intro x _ r
      have hr : aOuter r = 1 := (show r ∈ aOuter.ker from hker.symm ▸ mem_top r)
      exact DFunLike.congr_fun hr x
    rw [htop,index_top] at hfour
    contradiction
  let f : L →* Atlas.G2.Model K := d.chart.comp
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion s.chosen.normalizes))
  have hf : f.range = commutator (Atlas.G2.Model K) := by
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect s.maximal.1
    rw [show f.range = (inducedAutomizer V L).map d.chart by
      dsimp [f]
      rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range]
      rfl]
    exact component_actor_image s.chosen.normalizes s.actor d.chart d.coordinates d.equivariant
  let q : L →* commutator (Atlas.G2.Model K) :=
    f.codRestrict _ (fun l => hf ▸ (show f l ∈ f.range from ⟨l,rfl⟩))
  have hq : Function.Surjective q := by
    rintro ⟨b,hb⟩
    obtain ⟨l,hl⟩ := (show b ∈ f.range from hf.symm ▸ hb)
    exact ⟨l,Subtype.ext hl⟩
  have hqc : q c = derivedCubic := Subtype.ext hn
  have hqker : q.ker = pCore 2 L := by
    have he : q.ker = f.ker := by
      ext l
      exact Subtype.ext_iff
    exact he.trans (s.component_action_ker d)
  have hQ : IsPGroup 2 Q := pCore_isPGroup.map (L ⊔ (T : Subgroup G)).subtype
  have hX : IsPGroup 2 X := hQ.to_quotient _
  have hcore : L.pCoreIn 2 ≤ Q := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer s.chosen.sylow_normalizes_component)
  have hker : q.ker ≤ ((frattini X).quotientAut.comp a).ker := by
    intro l hl
    have hlQ : l.val ∈ Q := hcore (mem_map_of_mem L.subtype (show l ∈ pCore 2 L from hqker ▸ hl))
    have hi : a l = MulAut.conj (QuotientGroup.mk' (V.subgroupOf Q) ⟨l.val,hlQ⟩) := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H x =>
        change QuotientGroup.mk' (V.subgroupOf Q) ⟨l.val*x.val*l.val⁻¹,_⟩ =
          QuotientGroup.mk' (V.subgroupOf Q) ⟨l.val,hlQ⟩ *
            QuotientGroup.mk' (V.subgroupOf Q) x *
              (QuotientGroup.mk' (V.subgroupOf Q) ⟨l.val,hlQ⟩)⁻¹
        rw [← map_inv,← map_mul,← map_mul]
        rfl
    change (frattini X).quotientAut (a l) = 1
    rw [hi,quotientAut_conj_eq_one hX]
  let : Fact (IsPGroup 2 X) := ⟨hX⟩
  let : IsElementaryAbelian 2 (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
  obtain ⟨ρ,hρ,hd⟩ := exists_nontrivial_quotient_representation hX a q hq hker c
    (by exact (Subgroup.orderOf_mk _ _).trans ho) hac (inclusion hAL) z hgen rfl hacts (Nat.le_of_eq hfour)
  rw [hqc] at hd
  exact UnitaryGeometry.not_single_cubic_factor (MulEquiv.refl _) ρ hρ derivedCubic rfl hd

/-- Discharge the linear-three contract on the same plane and original LocalData. -/
theorem Context.linearThreeExclusion (s : Context T L V) : LinearThreeExclusion T L V :=
  fun d J j _ => s.linearThree_false d J j

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
