module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBorel
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
public import CFSG.Quasithin.ChapterF.Section01.SourceIncidence
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The actual A₅–Suzuki pair in the component-uniqueness argument

The A₅ Borel is the centralizer of the marked line in L. An additional
Suzuki component D is normal in the whole line centralizer by the existing
component-orbit argument. Consequently the entire A₅ Borel, including its
cubic Cartan, normalizes D. Since O²(DT)=D, this proves precisely the
Cartan-normalization clause of source5.2.2 on the residual used by13.6.27.
The stronger centralizer hypotheses make its general exceptional-case
analysis unnecessary in this application.

The Suzuki Borel lies in N(L) by13.6.25(3), supplying the reverse
cross-normalization. Uniqueness over LT gives the trivial two-core of the
generated pair; the marked line and ambient even characteristic give
characteristic two of both parabolics. Thus all six genuine F.1.1 clauses
hold on the original groups and Sylow subgroup.

The last theorem connects this construction to component uniqueness.
Excluding an A₅/Suzuki pair remains explicit: the source derives it from
the rank-two amalgam classification in5.2.6. This module proves neither
that exclusion nor the full5.2.3 classification.

Source: Aschbacher–Smith, combined manuscript (1 March2004),5.2.2–6,
printed pp.646–651, and13.6.27, printed p.934.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)

omit [Finite G] in
private theorem component_normalizer {z : G}
    (D : Subgroup (centralizer ({z} : Set G))) [D.Normal] :
    centralizer ({z} : Set G) ≤ normalizer (D.map (centralizer ({z} : Set G)).subtype : Set G) := by
  simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using
    D.le_normalizer_map (centralizer ({z} : Set G)).subtype

omit [Finite G] in
private theorem line_centralizer {z : G} (hz : zpowers z = V₁) :
    centralizer (V₁ : Set G) = centralizer ({z} : Set G) := by
  rw [←hz, zpowers_eq_closure, centralizer_closure]

include d

/-- The original A₅ Borel centralizes the marked line and therefore normalizes
every normal component of its centralizer. This includes its cubic Cartan. -/
theorem source_borel_normalizes_component {z : G} (hz : zpowers z = V₁)
    (D : Subgroup (centralizer ({z} : Set G))) [D.Normal] :
    borel L (T : Subgroup G) ≤ normalizer (D.map (centralizer ({z} : Set G)).subtype : Set G) := by
  rw [d.borel_eq_point_centralizer, line_centralizer hz]
  exact inf_le_right.trans (component_normalizer D)

private theorem pair_char_left (D : Subgroup G)
    (hB : borel D (T : Subgroup G) ≤ normalizer (L : Set G)) :
    generalizedFitting (parabolic ![L,D] (T : Subgroup G) 0) =
      pCore 2 (parabolic ![L,D] (T : Subgroup G) 0) := by
  let P := parabolic ![L,D] (T : Subgroup G) 0
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  have hTP : (T : Subgroup G) ≤ P := le_sup_right.trans le_sup_left
  have hPN : P ≤ normalizer (L : Set G) :=
    sup_le (sup_le L.le_normalizer d.normalizes_L) hB
  have hcore : L.pCoreIn 2 ≤ P.pCoreIn 2 := pCoreIn_mono_of_normalizes hLP hPN
  have hne : P.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact d.chosen.ne_bot (bot_unique
      (d.chosen.le_componentCore.trans (hcore.trans_eq he)))
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (d.hypothesis.qtke.evenCharacteristic T) ⟨hne,hTP⟩))

/-- All six genuine F.1.1 clauses for the original A₅ group and the actual
normal Suzuki component, with the original ambient Sylow subgroup. -/
theorem source_A5_suzuki_pair_F11 {z : G} (hz : zpowers z = V₁)
    (D : Subgroup (centralizer ({z} : Set G))) [D.Normal]
    {m : ℕ} (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hout : ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G)) :
    HypothesisF11 ![L,D.map (centralizer ({z} : Set G)).subtype] (T : Subgroup G) := by
  let A := D.map (centralizer ({z} : Set G)).subtype
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rw [←line_centralizer hz]
    exact d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two _ d.flag.one_card)
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) := hTC.trans (component_normalizer D)
  let eD := D.equivMapOfInjective (centralizer ({z} : Set G)).subtype
    (centralizer ({z} : Set G)).subtype_injective
  let eQ := QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)
  have eA : (A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m := eQ.symm.trans e
  have hz2 : orderOf z = 2 := by
    have hcard := d.flag.one_card
    rw [←hz, Nat.card_zpowers] at hcard
    exact hcard
  have hzT : z ∈ T := d.flag.one_le_two.trans
    (d.flag.two_le_V.trans d.chosen.le_sylow) (hz ▸ mem_zpowers z)
  have hB := (borel_join_le_M T A (normalizer (L : Set G)) z hz2 hzT hTC
    (map_subtype_le D) hTA (suzuki_borelFacts T A hTA eA) h25)
  have hBL : borel A (T : Subgroup G) ≤ normalizer (L : Set G) := le_sup_left.trans hB
  have hBA : borel L (T : Subgroup G) ≤ normalizer (A : Set G) :=
    source_borel_normalizes_component d hz D
  refine ⟨inferInstance,T.isPGroup',?_,?_,?_,?_,?_,?_⟩
  · intro i; fin_cases i
    · exact d.normalizes_L
    · exact hTA
  · intro i; fin_cases i
    · exact d.local_sylow
    · obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ A ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
        (show A ≤ A ⊔ (T : Subgroup G) from le_sup_left) (sup_le A.le_normalizer hTA)
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ A ⊔ (T : Subgroup G) from le_sup_right)] at hS
      exact ⟨S,hS⟩
  · intro i; fin_cases i
    · exact d.quotient_rankOneModel
    · exact IsRankOneModel.suzuki m ⟨eA⟩
  · intro i; fin_cases i
    · exact hBL
    · exact hBA
  · change pCore 2 (L ⊔ A ⊔ (T : Subgroup G) : Subgroup G) = ⊥
    have he : L ⊔ A ⊔ (T : Subgroup G) = (L ⊔ (T : Subgroup G)) ⊔ A := by ac_rfl
    rw [he]
    exact twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup _ _ _
      d.unique_maximal_overgroup hout
  · intro i; fin_cases i
    · exact pair_char_left d A hBL
    · apply d.characteristic_H
      · exact le_sup_right.trans le_sup_left
      · change A ⊔ (T : Subgroup G) ⊔ borel L (T : Subgroup G) ≤ centralizer (V₁ : Set G)
        rw [line_centralizer hz]
        exact sup_le (sup_le (map_subtype_le D) hTC)
          (d.borel_eq_point_centralizer ▸ inf_le_right.trans (line_centralizer hz).le)


omit d in
private theorem component_twoPerfect {X : Type*} [Group X] [Finite X]
    (D : Subgroup X) (hD : D.IsCComponent) : IsPPerfect 2 D := by
  let := hD.perfect
  intro N hN hp
  let := hN
  have hsub : Subsingleton (D ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (D ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The source residual of the Suzuki join is exactly the embedded component. -/
theorem source_residual_eq_component {z : G} (hz : zpowers z = V₁)
    (D : Subgroup (centralizer ({z} : Set G))) (hD : D.IsCComponent) [D.Normal] :
    let A := D.map (centralizer ({z} : Set G)).subtype
    (pResidual 2 (A ⊔ (T : Subgroup G) : Subgroup G)).map
      (A ⊔ (T : Subgroup G)).subtype = A := by
  dsimp only
  let eD := D.equivMapOfInjective (centralizer ({z} : Set G)).subtype
    (centralizer ({z} : Set G)).subtype_injective
  have hp := (component_twoPerfect D hD).of_surjective eD.toMonoidHom eD.surjective
  apply embedded_pResidual_join_pGroup _ _ hp T.isPGroup'
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rw [←line_centralizer hz]
    exact d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two _ d.flag.one_card)
  exact hTC.trans (component_normalizer D)

/-- The A₅ Borel normalizes the literal residual in source5.2.2; no
general Cartan-normalization theorem is required for this centralizer branch. -/
theorem source_borel_normalizes_residual {z : G} (hz : zpowers z = V₁)
    (D : Subgroup (centralizer ({z} : Set G))) (hD : D.IsCComponent) [D.Normal] :
    let A := D.map (centralizer ({z} : Set G)).subtype
    borel L (T : Subgroup G) ≤ normalizer
      ((pResidual 2 (A ⊔ (T : Subgroup G) : Subgroup G)).map
        (A ⊔ (T : Subgroup G)).subtype : Set G) := by
  dsimp only
  rw [source_residual_eq_component d hz D hD]
  exact source_borel_normalizes_component d hz D



/-- The actual13.6.27 catalogue and orbit argument supply both Suzuki
coordinates and the genuine F.1.1 pair for each additional component. -/
theorem centralizer_other_component_F11
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    {z : G} (hz : zpowers z = V₁)
    {K D : Subgroup (centralizer ({z} : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K)
    (hD : D.IsCComponent) (hne : D ≠ K) (hthree : Nat.Coprime 3 (Nat.card D))
    (hout : ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G)) :
    let A := D.map (centralizer ({z} : Set G)).subtype
    (∃ m : ℕ, 1 ≤ m ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
      HypothesisF11 ![L,A] (T : Subgroup G) ∧
      borel L (T : Subgroup G) ≤ normalizer
        ((pResidual 2 (A ⊔ (T : Subgroup G) : Subgroup G)).map
          (A ⊔ (T : Subgroup G)).subtype : Set G) := by
  dsimp only
  have hz2 : orderOf z = 2 := by
    have hcard := d.flag.one_card
    rwa [←hz,Nat.card_zpowers] at hcard
  obtain ⟨hn,m,hm,⟨e⟩⟩ := centralizer_other_component_normal_suzuki
    d.hypothesis.qtke hA36 T z hz2 hK hc hD hne hthree
  let := hn
  let eD := D.equivMapOfInjective (centralizer ({z} : Set G)).subtype
    (centralizer ({z} : Set G)).subtype_injective
  let eQ := QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)
  exact ⟨⟨m,hm,⟨eQ.symm.trans e⟩⟩,source_A5_suzuki_pair_F11 d hz D e hout h25,
    source_borel_normalizes_residual d hz D hD⟩

/-- Component uniqueness now needs only the A₅/Suzuki specialization of
the genuine rank-two pair exclusion, instead of the full earlier5.2.3.
The exclusion remains an explicit source obligation. -/
theorem component_unique_of_no_suzuki_pair
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    {z : G} (hz : zpowers z = V₁)
    {K : Subgroup (centralizer ({z} : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K)
    (hthree : ∀ D : Subgroup (centralizer ({z} : Set G)),
      D.IsCComponent → D ≠ K → Nat.Coprime 3 (Nat.card D))
    (hout : ∀ D : Subgroup (centralizer ({z} : Set G)),
      D.IsCComponent → ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G))
    (hExclude : ∀ A : Subgroup G, ∀ m : ℕ, 1 ≤ m →
      Nonempty ((A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
      ¬ HypothesisF11 ![L,A] (T : Subgroup G)) :
    ∀ D : Subgroup (centralizer ({z} : Set G)), D.IsCComponent → D = K := by
  intro D hD
  by_contra hne
  obtain ⟨⟨m,hm,e⟩,hF,_⟩ := centralizer_other_component_F11 d hA36 hz hK hc
    hD hne (hthree D hD hne) (hout D hD) h25
  exact hExclude _ m hm e hF


end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
