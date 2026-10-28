module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryPlacement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryNestedQuotients
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import Theory.SpecificGroups.Triality.ElementaryNine

public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Held.SylowOrderBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
public import Theory.SpecificGroups.Janko3.Model.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Restricting the point component above the original binary-triality section

The original binary-triality quotient survives as the two-core quotient of
its actual image in every containing component quotient. Its full order,
211341312, therefore divides the containing quotient order. Its three-rank
two excludes the noncentral-Fitting alternatives and gives quasisimplicity.
The checked carrier orders exclude every sporadic model (including J₄),
J₁, A₅ through A₈, and the binary linear groups in dimensions four and five.

For the original Cartan escape, a rank-two containing quotient is itself
binary triality by the preceding sieve. Equality of quotient orders then
lifts to equality of the original local components, using the full Sylow
and local C-component minimality. Thus a strict point-component enlargement
has no characteristic-two rank-two quotient. This does not infer strictness
of images merely from strictness of the original subgroups.

The final application keeps the original cubic, minus torus, inverter,
omega-point, two-core quotient section, residual and both Hall conditions.
The degree-two binary branch and the remaining containing models are still
open; no LocalCartanWitness or complete local Cartan sieve is asserted.

Source: Aschbacher--Smith A.3.12, 1.2.4 and 5.1.12--13,
printed pp.47--48,505,635--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem triality_card {Q : Type*} [Group Q]
    (hm : Triality.Standard.IsTrialityGroupAt 2 Q) : Nat.card Q = 211341312 := by
  have hm' : Triality.Standard.IsTrialityGroupAt (2^1) Q := by simpa using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Q 1 Nat.zero_lt_one).mp hm'
  rw [Nat.card_congr e.toEquiv, Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
    Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel]
  norm_num [Triality.Standard.binaryParameters_q]

private theorem triality_three_rank {Q : Type*} [Group Q] [Finite Q]
    (hm : Triality.Standard.IsTrialityGroupAt 2 Q) : 2 ≤ primeRank 3 Q := by
  have hm' : Triality.Standard.IsTrialityGroupAt (2^1) Q := by simpa using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Q 1 Nat.zero_lt_one).mp hm'
  rw [primeRank_equiv 3 e]
  obtain ⟨E,hE,hEc⟩ := Triality.Standard.exists_elementaryAbelian_three_card_nine 1 Nat.zero_lt_one
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hEc

private noncomputable def section_image_equiv {X J : Subgroup G} (hXJ : X ≤ J) :
    (X ⧸ pCore 2 X) ≃*
      (((X.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) ⧸
        pCore 2 ((X.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)))) := by
  let e := subgroupOfEquivOfLe hXJ
  let q := QuotientGroup.mk' (pCore 2 J)
  have hk : IsPGroup 2 (q.subgroupMap (X.subgroupOf J)).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
    ((q.subgroupMap (X.subgroupOf J)).quotientPCoreEquivOfSurjective
      (q.subgroupMap_surjective _) hk)

/-- The full original binary-triality quotient survives as a section of every
containing two-core quotient. In particular its full order divides that quotient. -/
private theorem triality_overcomponent_order {X J : Subgroup G} (hXJ : X ≤ J)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X)) :
    211341312 ∣ Nat.card (J ⧸ pCore 2 J) := by
  let I := (X.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
  have hc : Nat.card (I ⧸ pCore 2 I) = 211341312 :=
    (Nat.card_congr (section_image_equiv hXJ).symm.toEquiv).trans (triality_card hm)
  rw [←hc]
  exact (card_quotient_dvd_card (pCore 2 I)).trans I.card_subgroup_dvd_card

/-- Three-rank two survives the actual section and excludes the noncentral
Fitting alternatives for the containing component. -/
private theorem triality_overcomponent_quasisimple
    {P X J : Subgroup G} (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hP : P ∈ Chapter1.H G) (hJP : J ≤ P)
    (hJ : (J.subgroupOf P).IsCComponent) (hXJ : X ≤ J)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X)) :
    IsQuasisimple (J ⧸ pCore 2 J) := by
  have hrX : 2 ≤ primeRank 3 X := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 X) pCore_isPGroup]
    exact triality_three_rank hm
  have hrJ := hrX.trans (primeRank_mono 3 hXJ)
  have hr : 2 ≤ primeRank 3 (J.subgroupOf P) := by
    rwa [primeRank_equiv 3 (subgroupOfEquivOfLe hJP)]
  let q := QuotientGroup.mk' (pCore 2 P)
  let := pCore_isNilpotent (p := 2) (G := P)
  let e := cComponentTwoCoreQuotientEquiv hJ
  have hrbar : 2 ≤ primeRank 3 ((J.subgroupOf P).map q) := by
    rw [←primeRank_equiv 3 e,primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
      (pCore 2 (J.subgroupOf P)) pCore_isPGroup]
    exact hr
  let := ChapterA.Section03.cComponent_quasisimple_of_three_rank
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hP)
    (pCore_quotient_pCore_eq_bot 2) (hJ.map_quotient _) hrbar
  let a := subgroupOfEquivOfLe hJP
  exact IsQuasisimple.of_mulEquiv
    (e.symm.trans (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)))

private theorem rankTwo_transport {Q R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (hm : RankTwoTheoremC R) : RankTwoTheoremC Q := by
  cases hm with
  | linear n hn hm => exact .linear n hn (hm.of_mulEquiv e)
  | symplectic n hn hm => exact .symplectic n hn (hm.of_mulEquiv e)
  | g2 n hn hm => exact .g2 n hn (hm.of_mulEquiv e)
  | triality n hn hm => exact .triality n hn (hm.of_mulEquiv e)
  | ree m hm he =>
    obtain ⟨d,⟨a⟩⟩ := he
    exact .ree m hm ⟨d,⟨e.trans a⟩⟩
  | symplectic_derived he => exact .symplectic_derived ⟨e.trans he.some⟩
  | g2_derived he => exact .g2_derived ⟨e.trans he.some⟩
  | tits he => exact .tits ⟨e.trans he.some⟩

/-- On the original escaping input, no strict local enlargement of the
binary-triality component can have a characteristic-two rank-two quotient.
The order comparison lifts to the original groups by local minimality. -/
theorem original_triality_rankTwo_overcomponent_eq
    {T : Sylow 2 G} {L W H A B K X J P : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hP : P ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ P ≤ normalizer (residual H : Set G))
    (hX : X ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKX : K ≤ X) (hXJ : X ≤ J) (hJP : J ≤ P)
    (hJc : (J.subgroupOf P).IsCComponent)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X))
    (hmodel : RankTwoTheoremC (J ⧸ pCore 2 J)) : X = J := by
  let e := subgroupOfEquivOfLe hJP
  let a := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hKJ : K ≤ (J.subgroupOf P).map P.subtype := by
    rw [map_subgroupOf_eq_of_le hJP]
    exact hKX.trans hXJ
  have hj := LocalSieve.rankTwo_container_binaryTriality h hH hgen c hKH hK horbit
    hP hescape (J.subgroupOf P) hJc hKJ (rankTwo_transport a hmodel)
  have hc : Nat.card (J ⧸ pCore 2 J) = Nat.card (X ⧸ pCore 2 X) := by
    rw [←Nat.card_congr a.toEquiv,triality_card hj,triality_card hm]
  exact ChapterA.Section03.SourceEmbeddings.BinaryNested.local_eq_of_twoCore_card_le
    T hX.1 hJ.1 hXJ hc.le

private theorem sporadic_order_not_dvd (name : ClassificationModels.SporadicName) :
    ¬ 211341312 ∣ Nat.card name.Carrier := by
  cases name with
  | m11 =>
    change ¬ 211341312 ∣ Nat.card Sporadic.Mathieu.M11
    rw [Sporadic.Mathieu.m11_order]
    decide
  | m12 =>
    change ¬ 211341312 ∣ Nat.card Sporadic.Mathieu.M12
    rw [Sporadic.Mathieu.m12_order]
    decide
  | m22 =>
    change ¬ 211341312 ∣ Nat.card Sporadic.Mathieu.M22
    rw [Sporadic.Mathieu.m22_order]
    decide
  | m23 =>
    change ¬ 211341312 ∣ Nat.card Sporadic.Mathieu.M23
    rw [Sporadic.Mathieu.m23_order]
    decide
  | m24 =>
    change ¬ 211341312 ∣ Nat.card Sporadic.Mathieu.M24
    rw [Sporadic.Mathieu.m24_order]
    decide
  | j2 => norm_num [ClassificationModels.SporadicName.Carrier,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
  | j3 => norm_num [ClassificationModels.SporadicName.Carrier,Sporadic.Janko3.model_card]
  | j4 => norm_num [ClassificationModels.SporadicName.Carrier,Janko4.Cardinality.model_card]
  | hs =>
    intro hd
    have hh := hd.trans Sporadic.LeechRelated.HS.card_carrier_dvd
    norm_num at hh
  | he =>
    intro hd
    exact Held.not_two_pow_twelve_dvd_card ((by decide : 2^12 ∣ 211341312).trans hd)
  | ru => norm_num [ClassificationModels.SporadicName.Carrier,Rudvalis.model_card]

/-- All actual sporadic carriers, including J₄, and the additional J₁ carrier
are excluded above the same binary-triality section by their checked orders. -/
private theorem triality_overcomponent_not_sporadic {X J : Subgroup G} (hXJ : X ≤ J)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X)) :
    ¬ (ClassificationModels.IsSporadicModel (J ⧸ pCore 2 J) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Janko1.Model)) := by
  have hd := triality_overcomponent_order hXJ hm
  intro hbad
  rcases hbad with hbad | hbad
  · obtain ⟨name,⟨e⟩⟩ := hbad
    exact sporadic_order_not_dvd name (by rwa [←Nat.card_congr e.toEquiv])
  · rw [Nat.card_congr hbad.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd

/-- No alternating carrier from the source Theorem C list contains this
literal two-core section. -/
private theorem triality_overcomponent_not_small_alternating {X J : Subgroup G}
    (hXJ : X ≤ J) (hm : Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X))
    {d : ℕ} (hlo : 5 ≤ d) (hd : d ≤ 8) : ¬ IsAlternating (J ⧸ pCore 2 J) d := by
  rintro ⟨e⟩
  have hc := triality_overcomponent_order hXJ hm
  interval_cases d <;>
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hc <;>
    norm_num at hc

private theorem triality_overcomponent_not_binary_linear {X J : Subgroup G}
    (hXJ : X ≤ J) (hm : Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X))
    {d : ℕ} (hd : d = 4 ∨ d = 5) :
    ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) d 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  have hc := triality_overcomponent_order hXJ hm
  rw [Nat.card_congr e.toEquiv] at hc
  rcases hd with rfl | rfl
  · have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF] at hcard
    norm_num [Fin.prod_univ_succ] at hcard
    rw [hcard] at hc
    norm_num at hc
  · have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [hF] at hcard
    norm_num [Fin.prod_univ_succ] at hcard
    rw [hcard] at hc
    norm_num at hc

/-- The original point-component construction now excludes every strict rank-two
Lie enlargement, every sporadic quotient (including J₄), J₁, the small
alternating quotients and the two binary linear catalogue entries. Its full two-core quotient is quasisimple and contains
the original triality section. The degree-two binary branch remains separate. -/
theorem original_minus_torus_point_component_restrictions
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    n % 4 = 2 ∧
      ∃ (D E J : Subgroup G) (t z : G),
        D ≤ A ∧ D ≤ C.map Y.subtype ∧ Nat.card D = 3 ∧
        ¬ D ≤ normalizer (residual H : Set G) ∧
        t ∈ (T : Subgroup G) ⊓ C.map Y.subtype ∧ t ∉ L ∧
        (∀ d ∈ D, t*d*t⁻¹=d⁻¹) ∧
        E ≤ A ∧ D ≤ E ∧ Nat.card E = 2^(n/2)+1 ∧
        (∀ x : G, x ∈ E ↔ x ∈ A ∧ x^(2^(n/2)+1)=1) ∧
        z ∈ omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 ∧
        E ≤ centralizer ({z} : Set G) ∧
        (∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G)) ∧
        C.map Y.subtype ≤ J ∧ residual H ≤ J ∧ J ≤ centralizer ({z} : Set G) ∧
        (J.subgroupOf (centralizer ({z} : Set G))).IsCComponent ∧
        (J.subgroupOf (centralizer ({z} : Set G))).Normal ∧
        J ∈ Chapter1.L G (T : Subgroup G) ∧ E ≤ J ∧
        Nat.card ((E.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 2^(n/2)+1 ∧
        Nonempty ((C ⧸ pCore 2 C) ≃*
          (((C.map Y.subtype).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ⧸
            pCore 2 (((C.map Y.subtype).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))))) ∧
        (n = 2 ∨ (C.map Y.subtype < J ∧
          ¬ RankTwoTheoremC (J ⧸ pCore 2 J))) ∧
        centralizer ({z} : Set G) ∈ Chapter1.HOver G (H : Set G) ∧
        ¬ A ⊓ centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) ∧
        IsQuasisimple (J ⧸ pCore 2 J) ∧
        211341312 ∣ Nat.card (J ⧸ pCore 2 J) ∧
        ¬ (ClassificationModels.IsSporadicModel (J ⧸ pCore 2 J) ∨
          Nonempty ((J ⧸ pCore 2 J) ≃* Janko1.Model)) ∧
        (∀ d : ℕ, 5 ≤ d → d ≤ 8 → ¬ IsAlternating (J ⧸ pCore 2 J) d) ∧
        (∀ d : ℕ, d = 4 ∨ d = 5 → ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) d 2) := by
  obtain ⟨hn,D,E,J,t,z,hDA,hDC,hDc,hDn,ht,htL,hi,hEA,hDE,hEc,hroot,hz,hz1,hEz,hinv,
    hXJ,hRJ,hJz,hJc,hJn,hJ,hEJ,hEbar,hsection,hcases,hP,hescapeP⟩ :=
    original_minus_torus_point_component h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  let X := C.map Y.subtype
  let b := C.equivMapOfInjective Y.subtype Y.subtype_injective
  have hmX : Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X) :=
    hm.of_mulEquiv (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm
  have hcomp : (X.subgroupOf Y).IsCComponent := by
    change (C.map Y.subtype |>.comap Y.subtype).IsCComponent
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hC
  have hX : X ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hcomp.subgroupOf_of_le le_sup_left
      (sup_le (map_subtype_le C) (hH.1.1.2.trans hY.2)),
      ⟨T.subtype le_sup_right,?_⟩,?_⟩
    · simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
    · intro he
      exact hY.1 (bot_unique
        ((pCoreIn_le_pCoreIn_of_sylow T le_sup_right
          (sup_le (map_subtype_le C) (hH.1.1.2.trans hY.2))).trans_eq he))
  refine ⟨hn,D,E,J,t,z,hDA,hDC,hDc,hDn,ht,htL,hi,hEA,hDE,hEc,hroot,hz,hz1,hEz,hinv,
    hXJ,hRJ,hJz,hJc,hJn,hJ,hEJ,hEbar,hsection,?_,hP,hescapeP,
    triality_overcomponent_quasisimple h.qtke hP.1 hJz hJc hXJ hmX,
    triality_overcomponent_order hXJ hmX,
    triality_overcomponent_not_sporadic hXJ hmX,
    (fun d hlo hd => triality_overcomponent_not_small_alternating hXJ hmX hlo hd),
    fun d hd => triality_overcomponent_not_binary_linear hXJ hmX hd⟩
  rcases hcases with hn | hstrict
  · exact Or.inl hn
  · refine Or.inr ⟨hstrict,fun hmJ => hstrict.ne ?_⟩
    exact original_triality_rankTwo_overcomponent_eq h hH hgen c hKH hK horbit
      hP hescapeP hX hJ hKC hXJ hJz hJc hmX hmJ

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
