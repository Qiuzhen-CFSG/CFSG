module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersSixSourceRigidity
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentAmbientGeneration

/-!
# The second natural A₇ branch of the weight-two centralizer

The original A₅ residual moves the Sylow-central weight-six vector.
For any second source A₇ containing this residual, 12.3.7 and natural
coordinates make its vector stabilizer maximal. The proved weight-six
centralizer bound puts the second component in the original normalizer;
component uniqueness in the literal local intersection forces equality.

This excludes the second-A₇ branch of 12.3.8, retaining relative normality
and the original residual. The model recognition and moved-module argument
remain with qt-d-1236-1238-point-centralizers before final LocalAnalysis
assembly by qt-d-1231-local-analysis. Source: Aschbacher–Smith, pp.809–810.
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

/-- The A₅ residual moves the central weight-six point. -/
theorem five_moves_six
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    ¬ P.five ≤ centralizer ({(P.six : G)} : Set G) := by
  intro hc
  have hperm := (PointCentralizers.source_1237 P structural escape).2.1
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp
    (show (WeightTwoGeometry.support (E.coordinates P.two).toAdd).card = 2 from P.two_weight)
  obtain ⟨q,hq⟩ := P.exists_five_core_support_swap structural hperm i j hij hpair
  have hH : P.five ⊔ (T : Subgroup G) ≤ centralizer ({(P.six : G)} : Set G) :=
    sup_le hc (fun t ht => mem_centralizer_singleton_iff.mpr (P.six_central t ht))
  have hfix : evenRepresentation (Equiv.swap i j) (E.coordinates P.six).toAdd =
      (E.coordinates P.six).toAdd := by
    rw [← hq]
    have he := (E.sourceNormalizerModel structural).equivariant
      ⟨q.val,P.five_join_normalizes_module structural q.val.property⟩ P.six
    have hh : V.normalizerMonoidHom
        ⟨q.val,P.five_join_normalizes_module structural q.val.property⟩ P.six = P.six :=
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

/-- Any second source A₇ component containing the marked A₅ lies in N(L). -/
theorem second_seven_le_normalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    {K W : Subgroup G} (SK : Setup T K W) (EK : SK.NaturalCoordinates)
    (hfive : P.five ≤ K) : K ≤ normalizer (L : Set G) := by
  have hsix : ∀ z : W, (z : G) ∈ centralizer (T : Set G) →
      weight (EK.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) :=
    fun z _ hz => EK.source_weight_six_centralizer structural z hz
  have hsplit : SK.NaturalOmegaDecomposition :=
    (EK.source_1237_one_of_weight_six structural escape hsix).2.2.1
  have hmove := P.five_moves_six structural escape
  have hmax := SK.centralVectorMaximality_of_coordinates_omega EK hsplit
  apply le_of_maximal_pointCentralizer
    (hmax P.six P.six_mem_omega (fun h => hmove (hfive.trans h)))
    hfive ((pointResidual_le L (P.two : G)).trans (inf_le_left.trans L.le_normalizer))
    (inf_le_right.trans (E.source_weight_six_centralizer structural P.six P.six_weight)) hmove

/-- The original perfect residual is a component in the literal local intersection. -/
theorem two_local_component :
    (P.five.subgroupOf
      (centralizer ({(P.two : G)} : Set G) ⊓ normalizer (L : Set G))).IsCComponent := by
  let B := centralizer ({(P.two : G)} : Set G) ⊓ normalizer (L : Set G)
  have hKB : P.five ≤ B := le_inf ((pointResidual_le L (P.two : G)).trans inf_le_right)
    ((pointResidual_le L (P.two : G)).trans (inf_le_left.trans L.le_normalizer))
  let K := P.five.subgroupOf B
  have hn : B ≤ normalizer (P.five : Set G) := by
    apply le_trans ?_ (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
    apply le_trans ?_ inf_normalizer_le_normalizer_inf
    exact le_inf inf_le_right (inf_le_left.trans le_normalizer)
  let : K.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKB).symm.toMonoidHom)
    (subgroupOfEquivOfLe hKB).symm.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (P.five ⧸ pCore 2 P.five) :=
    IsQuasisimple.of_mulEquiv P.fiveCoreEquiv.symm
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKB) (pCore_map_iso 2 _)).symm
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient (p := 2)
    (inferInstance : K.Normal).isSubnormal (by
      intro N hN hp
      let := hN
      let := hp.isNilpotent
      exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N))

/-- A containing component inside the original normalizer cannot enlarge A₅. -/
theorem two_container_eq_of_le_normalizer
    {K : Subgroup G} (hKH : K ≤ centralizer ({(P.two : G)} : Set G))
    (hK : (K.subgroupOf (centralizer ({(P.two : G)} : Set G))).IsCComponent)
    (hfive : P.five ≤ K) (hKL : K ≤ normalizer (L : Set G)) : K = P.five := by
  let N := centralizer ({(P.two : G)} : Set G) ⊓ normalizer (L : Set G)
  have hKN : K ≤ N := le_inf hKH hKL
  have hcomp : (K.subgroupOf N).IsCComponent := hK.subgroupOf_of_le hKN inf_le_left
  have he := P.two_local_component.eq_of_le hcomp (comap_mono hfive)
  apply le_antisymm ?_ hfive
  intro k hk
  have hh : (⟨k,hKN hk⟩ : N) ∈ P.five.subgroupOf N := by rw [he]; exact hk
  exact hh

/-- The natural A₇ branch of the actual point-component enlargement is impossible. -/
theorem two_component_eq_of_second_seven
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    {K W : Subgroup G} (SK : Setup T K W)
    (hKH : K ≤ centralizer ({(P.two : G)} : Set G))
    (hK : (K.subgroupOf (centralizer ({(P.two : G)} : Set G))).IsCComponent)
    (hfive : P.five ≤ K) : K = P.five := by
  obtain ⟨EK⟩ := natural K W SK
  exact P.two_container_eq_of_le_normalizer hKH hK hfive
    (P.second_seven_le_normalizer structural escape SK EK hfive)

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
