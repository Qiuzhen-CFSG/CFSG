module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.QuotientTransport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.BlockTransport
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.Stabilizers
public import Theory.SpecificGroups.Tits.ConverseLocalCores.First
public import Theory.SpecificGroups.Tits.ConverseLocalCores.Second
public import Theory.SpecificGroups.Tits.ThreeRankLowerBound
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.ComponentRank
public import Theory.GroupTheory.RelativeNormalizerTransport

/-!
# Tits invariant parabolics for E.6.8

Align the component Sylow with the certified Atlas Sylow through the genuine
Parrott–Atlas equivalence. Both concrete parabolics are invariant under its
stabilizer and generate the Tits group. Their characteristic-two property
passes to their joins with Q. The first join is three-free; the second has no
short subnormal subgroup by the checked core commutator obstruction.

The Tits three-rank lower bound and local quasithinness prove that Q normalizes
the component. Passing to the literal (LQ)/O₂(LQ) then gives every field of
BlockFreeQuotientFamily, including relative subnormality in the lifted joins.
No universal Chapter 1 statement or unproved model premise is required here.
The E.6.7 application and final exclusion belong to the parent assembly.

Source: Aschbacher–Smith E.6.8, printed pp.247–248 (PDF pp.258–259), and
Parrott (1972), pp.672,683–684.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- Align the actual intersection with the certified Tits Sylow subgroup. -/
theorem tits_sylow_marking (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hm : Nonempty (L ≃* Tits.ParrottGroup)) :
    ∃ e : L ≃* Tits.Atlas1600Group,
      (Q.subgroupOf L).map e.toMonoidHom = Tits.atlas1600SylowTwoSubgroup := by
  obtain ⟨e⟩ := hm
  obtain ⟨R, hR⟩ := component_sylow_intersection h hU hL
  rw [← hQ] at hR
  have he : (R : Subgroup L) = Q.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hR]
    ext x
    constructor
    · rintro ⟨hl, hq⟩
      exact ⟨⟨x, hl⟩, hq, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
  obtain ⟨f, hf⟩ := Tits.RelativeSylowMarking.exists_sylow_marking
    (e.trans Tits.parrottFiniteImageEquiv) R
  exact ⟨f, he ▸ hf⟩

/-- The two literal Atlas parabolics pulled back to the component. -/
def titsParabolic (e : L ≃* Tits.Atlas1600Group) (i : Fin 2) : Subgroup L :=
  (![Tits.ExceptionalParabolics.first, Tits.ExceptionalParabolics.second] i).map
    e.symm.toMonoidHom

omit [Finite G] in
theorem titsParabolic_generate (e : L ≃* Tits.Atlas1600Group) :
    titsParabolic e 0 ⊔ titsParabolic e 1 = ⊤ := by
  change (Tits.ExceptionalParabolics.first.map e.symm.toMonoidHom) ⊔
    (Tits.ExceptionalParabolics.second.map e.symm.toMonoidHom) = ⊤
  rw [← Subgroup.map_sup, Tits.ExceptionalParabolics.generate,
    map_top_of_surjective _ e.symm.surjective]

omit [Finite G] in
/-- Relative invariance is proved before replacing N_Q(L) by Q. -/
theorem titsParabolic_invariant (e : L ≃* Tits.Atlas1600Group)
    (he : (Q.subgroupOf L).map e.toMonoidHom = Tits.atlas1600SylowTwoSubgroup)
    (i : Fin 2) : componentNormalizer Q L ≤
      normalizer ((titsParabolic e i).map L.subtype : Set G) := by
  fin_cases i
  · exact normalizes_pullback_of_stabilizer_invariant e _ _ he
      Tits.RelativeParabolicNormalizers.first_stabilized
  · exact normalizes_pullback_of_stabilizer_invariant e _ _ he
      Tits.RelativeParabolicNormalizers.second_stabilized

/-- The full source quotient family for Tits, conditional on the separate
component-normalization step of 1.2.1(3). No local model premise remains. -/
theorem tits_family_of_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hm : Nonempty (L ≃* Tits.ParrottGroup))
    (hN : Q ≤ normalizer (L : Set G)) : Nonempty (BlockFreeQuotientFamily Q L) := by
  obtain ⟨e, he⟩ := tits_sylow_marking h hU hL hQ hm
  have hcore := extension_core_le_Q h hU hL hQ hN
  have hQp : IsPGroup 2 Q := by rw [hQ]; exact T.isPGroup'.to_le inf_le_left
  have hinv (i : Fin 2) : Q ≤ normalizer ((titsParabolic e i).map L.subtype : Set G) := by
    simpa only [componentNormalizer_eq hN] using titsParabolic_invariant e he i
  let ep (i : Fin 2) : (titsParabolic e i).map L.subtype ≃*
      (![Tits.ExceptionalParabolics.first, Tits.ExceptionalParabolics.second] i) :=
    ((titsParabolic e i).equivMapOfInjective L.subtype L.subtype_injective).symm.trans
      (e.symm.subgroupMap _).symm
  refine ⟨{
    count := 2
    subgroup := fun i => parabolicImage Q L (titsParabolic e i)
    le_component := fun i => parabolicImage_le _
    invariant := fun i => parabolicImage_invariant _ (titsParabolic_invariant e he i)
    characteristic_two := ?_
    no_blocks := ?_
    generate := ?_ }⟩
  · intro i
    rw [preimage_join_eq _ hcore]
    apply join_characteristicTwo (hinv i) hQp
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 (ep i)).mpr
    fin_cases i
    · exact Tits.ConverseLocalCores.first_core_self_centralizing
    · exact Tits.ConverseLocalCores.second_core_self_centralizing
  · intro i
    rw [preimage_join_eq _ hcore]
    fin_cases i
    · apply noChiZeroBlocks_of_three_free
      apply join_three_free (hinv 0) _ hQp
      rw [Nat.card_congr (ep 0).toEquiv]
      change ¬ 3 ∣ Nat.card Tits.ExceptionalParabolics.first
      rw [Tits.ReeLocalBlockOrders.first_card]
      decide
    · apply noChiZeroBlocks_of_coreSection (coreSectionOfJoin (hinv 1) hQp (ep 1))
      intro B _ hp hsquare
      exact Tits.RelativeSecondBlockLayers.eq_bot_of_core_square B hp hsquare
  · have hgen := congrArg (parabolicImage Q L) (titsParabolic_generate e)
    rw [parabolicImage_sup, parabolicImage_top] at hgen
    rw [← hgen]
    exact sup_le
      (le_iSup (fun i : Fin 2 => parabolicImage Q L (titsParabolic e i)) 0)
      (le_iSup (fun i : Fin 2 => parabolicImage Q L (titsParabolic e i)) 1)


/-- The actual Tits component is normalized by Q, by its odd prime rank. -/
theorem tits_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hm : Nonempty (L ≃* Tits.ParrottGroup)) : Q ≤ normalizer (L : Set G) := by
  obtain ⟨e⟩ := hm
  let f := e.trans Tits.parrottFiniteImageEquiv
  apply normalizes_of_odd_primeRank h hU hL hQ
    (Tits.RelativeSylowMarking.center_eq_bot f) 3 (by decide)
  rw [primeRank_equiv 3 f]
  exact Tits.ThreeRank.rank_two_le

/-- The Tits invariant-parabolic output in E.6.8, with every model and
component-normalization premise discharged. -/
theorem tits_geometry (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hm : Nonempty (L ≃* Tits.ParrottGroup)) :
    Q ≤ normalizer (L : Set G) ∧ Nonempty (BlockFreeQuotientFamily Q L) := by
  have hn := tits_normalizes h hU hL hQ hm
  exact ⟨hn, tits_family_of_normalizes h hU hL hQ hm hn⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
