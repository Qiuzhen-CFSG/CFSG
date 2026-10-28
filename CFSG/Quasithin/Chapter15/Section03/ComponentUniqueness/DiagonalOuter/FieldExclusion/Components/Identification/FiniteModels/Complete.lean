module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoFour
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Source
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Outer
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Representatives
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M22Table
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M24Table.TwoAKernel
public import Theory.Mathieu.M24.ChapterHStabilizers.PairFixedCentralizers

/-!
# Complete exceptional-model sieve for the selected field component

Transport the actual ordinary PSL₃(2) component through the full model
markings. Full fixed-component rows exclude J₄ and HS; the retained centers
exclude the covering Held rows. Exact centralizer orders exclude Rudvalis.
The actual M₂₄ two-kernel and seven-element fixed points, together with the
M₂₂ pair realization, exclude both remaining Mathieu groups.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137. The earlier
small sporadic sieve leaves only J₂ after these exclusions.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
variable {S : Type*} [Group S] (s : SimpleInput S)
include s

private theorem model_perfect {T : Type*} [Group T] (e : S ≃* T) : Group.IsPerfect T := by
  let : IsSimpleGroup S := s.simple
  let : Group.IsPerfect S := ⟨(inferInstance : (commutator S).Normal).eq_bot_or_eq_top.resolve_left
    (fun h => s.nonabelian ((commutator_eq_bot_iff S).mp h))⟩
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

/-- The full ordinary-component exclusion on the actual J₄ carrier. -/
theorem SimpleInput.not_janko_four : ¬ Nonempty (S ≃* Janko4.Model) := by
  rintro ⟨e⟩
  let : IsSimpleGroup S := s.simple
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Janko4.Model := model_perfect s e
  obtain ⟨a, ha, D, hD, _⟩ := s.fixed_component_of_equiv e
  exact Chapter16.OtherPreliminaries.JankoFour.involution_fixed_no_component a ha D hD

/-- The actual HS fixed components are A₆ or A₈, neither of order 168. -/
theorem SimpleInput.not_higman_sims : ¬ Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) := by
  rintro ⟨e⟩
  let : IsSimpleGroup S := s.simple
  let : IsSimpleGroup Sporadic.LeechRelated.HS.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier := model_perfect s e
  obtain ⟨a, ha, D, hD, ⟨eD⟩⟩ := s.fixed_component_of_equiv e
  have hcard : Nat.card D = 168 := (Nat.card_congr eD.toEquiv).trans Matrix.PSL3Two.card_PSL
  by_cases hi : ∃ g, a = MulAut.conj g
  · obtain ⟨d⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.inner_component_equiv a ha hi D hD
    have hc := Nat.card_congr d.toEquiv
    change Nat.card D = Nat.card (alternatingGroup (Fin 6)) at hc
    rw [hcard, nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
  · obtain ⟨d⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.outer_component_equiv a ha hi D hD
    have hc := Nat.card_congr d.toEquiv
    change Nat.card D = Nat.card (alternatingGroup (Fin 8)) at hc
    rw [hcard, nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc

/-- The two covering Held rows have nontrivial center, and the remaining
marked row has self-centralizing two-core. -/
theorem SimpleInput.not_held : ¬ Nonempty (S ≃* Held.He) := by
  rintro ⟨e⟩
  obtain ⟨a, ha, D, hD, heD⟩ := s.fixed_component_of_equiv e
  by_cases hi : ∃ g, a = MulAut.conj g
  · obtain ⟨g, rfl⟩ := hi
    have hg : orderOf g = 2 := (Held.InvolutionFixedData.orderOf_conj g).symm.trans ha
    rcases Held.InvolutionFixedData.Coverage.innerInvolutionCoverage g hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have hcover := Held.InvolutionFixedData.TwoA.hasPSL3FourNormalOfIndexTwo.of_mulEquiv
        (Held.InvolutionFixedData.innerFixedEquiv (MulAut.conj c) Held.a)
      exact hcover.forget.not_component_equiv (by decide)
        Matrix.PSL3Two.Automorphisms.center_psl_eq_bot hD heD
    · let q := Held.InvolutionFixedData.innerFixedEquiv (MulAut.conj c)
        (Held.TwoLocalCandidates.max5First ^ 4)
      exact held_twoB_no_component (D.map q.symm.toMonoidHom) (hD.map_equiv q.symm)
  · obtain ⟨n, rfl⟩ := Held.Realization.normalizer_surjective a
    have hcover := Held.InvolutionFixedData.outerRow n ha (by
      rintro ⟨g, hg⟩
      exact hi ⟨g, hg.symm⟩)
    exact hcover.not_component_equiv (by decide)
      Matrix.PSL3Two.Automorphisms.center_psl_eq_bot hD heD

/-- Exact orders of both full Rudvalis centralizers suffice; no structural
centralizer product or exceptional covering classification is required. -/
theorem SimpleInput.not_rudvalis : ¬ Nonempty (S ≃* Rudvalis.Model) := by
  rintro ⟨e⟩
  let : IsSimpleGroup S := s.simple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Rudvalis.Model := model_perfect s e
  obtain ⟨a, ha, D, hD, ⟨eD⟩⟩ := s.fixed_component_of_equiv e
  obtain ⟨g, hg⟩ := Chapter1.XiEmbedding.OuterModels.rudvalis_conj_surjective a
  obtain ⟨x, hx, _, hfix⟩ := MulAut.inner_involution_representative
    Subgroup.center_eq_bot_of_simple_perfect a ha ⟨g, hg.symm⟩
  have hd : 168 ∣ Nat.card a.fixedSubgroup := by
    rw [← (Nat.card_congr eD.toEquiv).trans Matrix.PSL3Two.card_PSL]
    exact D.card_subgroup_dvd_card
  rw [hfix] at hd
  rcases Rudvalis.InvolutionCentralizers.centralizer_representatives x hx with
    ⟨_, ⟨d⟩⟩ | ⟨_, ⟨d⟩⟩
  · rw [Nat.card_congr d.toEquiv, Rudvalis.SylowOvergroups.max6_card] at hd
    norm_num at hd
  · rw [Nat.card_congr d.toEquiv, Rudvalis.InvolutionCentralizers.second_centralizer_card] at hd
    norm_num at hd

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification


namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
open Sporadic.Mathieu Sporadic.Mathieu.M24InvolutionCentralizers
open Sporadic.Mathieu.M24ChapterHStabilizers
variable {S : Type*} [Group S] (s : SimpleInput S)
include s

/-- The faithful two-kernel excludes the central class; three fixed points of
seven-elements exclude the fixed-point-free class. -/
theorem SimpleInput.not_m24 : ¬ Nonempty (S ≃* M24) := by
  rintro ⟨e⟩
  obtain ⟨a, ha, D, hD, ⟨eD⟩⟩ := s.fixed_component_of_equiv e
  rcases (M24InvolutionCentralizers.fixedSubgroup_alternative a ha).2 with hq | hq
  all_goals obtain ⟨q⟩ := hq
  · exact Chapter16.OtherPreliminaries.Mathieu.m24_twoA_no_component
      (D.map q.toMonoidHom) (hD.map_equiv q)
  · apply m24_twoB_not_seven
    rw [← Nat.card_congr q.toEquiv]
    have hc : Nat.card D = 168 := (Nat.card_congr eD.toEquiv).trans Matrix.PSL3Two.card_PSL
    exact (show 7 ∣ Nat.card D by rw [hc]; decide).trans D.card_subgroup_dvd_card

/-- The full pair realization reduces outer M₂₂ to actual pointed M₂₄
centralizers; no marked extension or quotient classification is assumed. -/
theorem SimpleInput.not_m22 : ¬ Nonempty (S ≃* M22) := by
  rintro ⟨e⟩
  obtain ⟨a, ha, D, hD, ⟨eD⟩⟩ := s.fixed_component_of_equiv e
  by_cases hi : ∃ g, a = MulAut.conj g
  · obtain ⟨g, rfl⟩ := hi
    have hg : orderOf g = 2 :=
      (MulAut.conj_orderOf_of_center_eq_bot m22_center_eq_bot g).symm.trans ha
    exact Chapter16.OtherPreliminaries.Mathieu.m22_inner_fixedSubgroup_no_components
      g hg ⟨D, hD⟩
  · obtain ⟨x, rfl⟩ := MathieuCode.m22PairStabilizerEquivAut.surjective a
    have hx : orderOf x = 2 :=
      (MathieuCode.m22PairStabilizerEquivAut.orderOf_eq x).symm.trans ha
    have hout : x.val ∉ MathieuCode.m22PointwisePairStabilizer := by
      intro hm
      exact hi ((pair_inner_iff x).mpr hm)
    let q := m22Pair_fixedEquiv x hout
    rcases involution_classes x.val ((Subgroup.orderOf_coe x).trans hx) with hA | hB
    · have hmove : x.val • (0 : Fin 24) ≠ 0 := by
        rw [(outer_pair_iff_swaps x).mp hout |>.1]
        decide
      exact not_isComponent_of_twoCore
        (pointed_twoCore_of_class2A x.val hA 0 hmove)
        (D.map q.toMonoidHom) (hD.map_equiv q)
    · obtain ⟨u⟩ := fixed_equiv_centralizer_of_isConj hB
      have hc : Nat.card D = 168 :=
        (Nat.card_congr eD.toEquiv).trans Matrix.PSL3Two.card_PSL
      have hd : 7 ∣ Nat.card (MathieuCode.m22PairStabilizerEquivAut x).fixedSubgroup :=
        (show 7 ∣ Nat.card D by rw [hc]; decide).trans D.card_subgroup_dvd_card
      rw [Nat.card_congr q.toEquiv] at hd
      have hh := hd.trans (MulAction.stabilizer
        (centralizer ({x.val} : Set M24)) (0 : Fin 24)).card_subgroup_dvd_card
      rw [← MulAut.fixedSubgroup_conj x.val, Nat.card_congr u.toEquiv] at hh
      exact m24_twoB_not_seven hh

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
