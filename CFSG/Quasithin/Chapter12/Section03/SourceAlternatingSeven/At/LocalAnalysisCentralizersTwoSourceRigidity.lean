module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceRigidity
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersSixSourceRigidity
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentAmbientGeneration

/-!
# LocalAnalysisCentralizersTwoSourceRigidity at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersTwoSourceRigidity`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode ChapterA.Section04

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem five_moves_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    ¬ P.five ≤ centralizer ({(P.six : G)} : Set G) := by
  intro hc
  have hperm := (PointCentralizers.source_1237_at P structural escape).2.1
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp
    (show (WeightTwoGeometry.support (E.coordinates P.two).toAdd).card = 2 from P.two_weight)
  obtain ⟨q,hq⟩ := P.exists_five_core_support_swap_at structural hperm i j hij hpair
  have hH : P.five ⊔ (T : Subgroup G) ≤ centralizer ({(P.six : G)} : Set G) :=
    sup_le hc (fun t ht => mem_centralizer_singleton_iff.mpr (P.six_central t ht))
  have hfix : evenRepresentation (Equiv.swap i j) (E.coordinates P.six).toAdd =
      (E.coordinates P.six).toAdd := by
    rw [← hq]
    have he := (E.sourceNormalizerModel_at structural).equivariant
      ⟨q.val,P.five_join_normalizes_module_at structural q.val.property⟩ P.six
    have hh : V.normalizerMonoidHom
        ⟨q.val,P.five_join_normalizes_module_at structural q.val.property⟩ P.six = P.six :=
      Subtype.ext (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hH q.val.property)))
    exact he.symm.trans (congrArg (fun v : V => (E.coordinates v).toAdd) hh)
  obtain ⟨y,hy,c,he⟩ := WeightTwoGeometry.support_swap_fixed_split
    (E.coordinates P.two).toAdd (E.coordinates P.six).toAdd i j hij hpair hfix
  have hf : ∀ a ∈ WeightTwoGeometry.five (E.coordinates P.two).toAdd,
      evenRepresentation a.val (E.coordinates P.six).toAdd = (E.coordinates P.six).toAdd := by
    intro a ha
    obtain ⟨k,hk⟩ := E.pointResidualProjection_surjective P.two P.two_weight ⟨a,ha⟩
    have hea := congrArg (fun b : WeightTwoGeometry.five (E.coordinates P.two).toAdd => b.val) hk
    change S.projection ⟨k,((pointResidual_le L (P.two : G)).trans inf_le_left) k.property⟩ = a at hea
    rw [← hea, ← E.equivariant]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hc k.property))
  have hyf : ∀ a ∈ WeightTwoGeometry.five (E.coordinates P.two).toAdd,
      evenRepresentation a.val y = y := by
    intro a ha
    have ht := (WeightTwoGeometry.mem_stabilizer a (E.coordinates P.two).toAdd).mp
      (show a ∈ WeightTwoGeometry.stabilizer (E.coordinates P.two).toAdd from
        MulAction.fixingSubgroup_le_stabilizer _ _ ha)
    have hh := hf a ha
    rw [he,map_add,map_smul,ht] at hh
    exact add_right_cancel hh
  have hy0 := WeightTwoGeometry.fixed_eq_zero_of_support_zero _ _ P.two_weight hy hyf
  rw [hy0,zero_add] at he
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · have hw := P.six_weight
    rw [he,zero_smul] at hw
    have hz : weight (0 : Word) = 0 := by decide
    exact (by decide : (0 : ℕ) ≠ 6) (hz.symm.trans hw)
  · rw [one_smul] at he
    have hh := congrArg (fun x : EvenWord => weight x.val) he
    rw [P.six_weight,P.two_weight] at hh
    omega

theorem second_seven_le_normalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    {K W : Subgroup G} (SK : Setup T K W) (EK : SK.NaturalCoordinates)
    (hfive : P.five ≤ K) : K ≤ normalizer (L : Set G) := by
  have hsix : ∀ z : W, (z : G) ∈ centralizer (T : Set G) →
      weight (EK.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) :=
    fun z _ hz => EK.source_weight_six_centralizer_at structural z hz
  have hsplit : SK.NaturalOmegaDecomposition :=
    (EK.source_1237_one_of_weight_six_at structural escape hsix).2.2.1
  have hmove := P.five_moves_six_at structural escape
  have hmax := SK.centralVectorMaximality_of_coordinates_omega EK hsplit
  apply le_of_maximal_pointCentralizer
    (hmax P.six P.six_mem_omega (fun h => hmove (hfive.trans h)))
    hfive ((pointResidual_le L (P.two : G)).trans (inf_le_left.trans L.le_normalizer))
    (inf_le_right.trans (E.source_weight_six_centralizer_at structural P.six P.six_weight)) hmove

theorem two_component_eq_of_second_seven_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    {K W : Subgroup G} (SK : Setup T K W)
    (hKH : K ≤ centralizer ({(P.two : G)} : Set G))
    (hK : (K.subgroupOf (centralizer ({(P.two : G)} : Set G))).IsCComponent)
    (hfive : P.five ≤ K) : K = P.five := by
  obtain ⟨EK⟩ := natural K W SK
  exact P.two_container_eq_of_le_normalizer hKH hK hfive
    (P.second_seven_le_normalizer_at structural escape SK EK hfive)

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

