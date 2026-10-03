module

public import Stellmacher.SectionEight.GeneratedContext

public import Stellmacher.SectionEight.EightTwoFourFactorCoreQuotient
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Center orders from the distinguished central four-factors

In the noncentral Section Eight context, suppose both distinguished native
two-cores are elementary and each is the direct product of a supplied normal
four-group and its stabilizer's center. Then both centers have order at most
two. The distance-one hypothesis is retained for the intended (8.2) interface;
once the explicit factors are supplied, no further distance calculation is
needed. Neither the elementary-core theorem nor the four-factor theorem is
used as a dependency.

The actual S3 core-quotient bridge makes each core have index two in the
common Sylow subgroup. The direct-product order formula then makes the two
center orders equal. Both ambient centers lie in the Sylow center, and their
intersection is central in the generated ambient group. It is a two-group,
so the trivial ambient two-core makes this intersection trivial. Native
self-centralization transfers to the ambient cores and makes the Sylow
center proper in each core. Lagrange's theorem bounds twice its order by
the core order, while the disjoint product of the two stabilizer centers
embeds in it. These inequalities give the claimed bound without any
whole-group classification or backward-edge transfer.

Source: Stellmacher (8.2), final paragraph, Journal of Algebra 190 (1997),
printed p.38, `refs/latex/stellmacher-n-group.tex`.

The supplemental theorem uses `SectionEightLocalContext` and its genuine
Section Seven hypotheses. The original public theorem remains a wrapper
through `SectionEightContext.toLocalContext`, preserving the graph and
critical path definitionally. No additional Sylow hypothesis is imposed
on the ambient group of the supplemental theorem.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem bound_core_index_two
    {G : Type u} [Group G] [Finite G] (P W : Subgroup G)
    (hW : IsSylowTwoIn W P)
    (hquot : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))) :
    (twoCoreIn P).relIndex W = 2 := by
  obtain ⟨equiv⟩ := hquot
  obtain ⟨_, T, hT⟩ := hW
  rw [← hT, twoCoreIn, Subgroup.relIndex_map_map_of_injective _ _ P.subtype_injective]
  let projection := QuotientGroup.mk' (pCore 2 P)
  have hker : projection.ker = pCore 2 P := QuotientGroup.ker_mk' _
  rw [← hker, Subgroup.relIndex_ker]
  let image := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 P))
  change Nat.card image = 2
  rw [Sylow.card_eq_multiplicity, Nat.card_congr equiv.toEquiv]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [show 6 = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide)]
  norm_num [Nat.prime_two, Nat.prime_three]

private theorem bound_center_restrict
    {G : Type u} [Group G] (P W : Subgroup G)
    (hWP : W ≤ P) (hZW : CenterAmbient P ≤ W) :
    CenterAmbient P ≤ CenterAmbient W := by
  intro element helement
  refine ⟨⟨element, hZW helement⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro other
  apply Subtype.ext
  exact SevenSix.centerAmbient_le_centralizer P helement other (hWP other.property)

private theorem bound_selfcentralizing_core
    {G : Type u} [Group G] (P : Subgroup G)
    (hcent : Subgroup.centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    P ⊓ Subgroup.centralizer (twoCoreIn P : Set G) ≤ twoCoreIn P := by
  intro element helement
  refine ⟨⟨element, helement.1⟩, hcent ?_, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  apply Subtype.ext
  exact helement.2 other ⟨other, hother, rfl⟩

private theorem bound_sylow_center_proper
    {G : Type u} [Group G] [Finite G] (P W : Subgroup G)
    (hWP : W ≤ P) (hQW : twoCoreIn P ≤ W)
    (hcent : Subgroup.centralizer (pCore 2 P : Set P) ≤ pCore 2 P)
    (hindex : (twoCoreIn P).relIndex W = 2) :
    2 * Nat.card (CenterAmbient W) ≤ Nat.card (twoCoreIn P) := by
  have hZW := Subgroup.map_subtype_le (Subgroup.center W)
  have hZQ : CenterAmbient W ≤ twoCoreIn P :=
    (le_inf (hZW.trans hWP)
      ((SevenSix.centerAmbient_le_centralizer W).trans
        (Subgroup.centralizer_le hQW))).trans (bound_selfcentralizing_core P hcent)
  have hne : CenterAmbient W ≠ twoCoreIn P := by
    intro heq
    have hWQ : W ≤ twoCoreIn P := by
      apply (le_inf hWP ?_).trans (bound_selfcentralizing_core P hcent)
      rw [← heq]
      exact Subgroup.le_centralizer_iff.mp (SevenSix.centerAmbient_le_centralizer W)
    have := Subgroup.relIndex_eq_one.mpr hWQ
    omega
  have hlt : Nat.card (CenterAmbient W) < Nat.card (twoCoreIn P) := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hZQ)
    intro heq
    exact hne (Subgroup.eq_of_le_of_card_ge hZQ heq.ge)
  obtain ⟨factor, hfactor⟩ := Subgroup.card_dvd_of_le hZQ
  have hpos := Nat.card_pos (α := CenterAmbient W)
  have htwo : 2 ≤ factor := by nlinarith
  nlinarith

private theorem bound_disjoint_centers
    {G : Type u} [Group G] [Finite G] (P L : Subgroup G)
    (hgen : P ⊔ L = ⊤) (hcore : pCore 2 G = ⊥)
    (hZQ : CenterAmbient P ≤ twoCoreIn P) :
    Disjoint (CenterAmbient P) (CenterAmbient L) := by
  let intersection := CenterAmbient P ⊓ CenterAmbient L
  have hcentral : intersection ≤ Subgroup.center G := by
    apply Subgroup.centralizer_eq_top_iff_subset.mp
    apply top_unique
    rw [← hgen]
    apply sup_le
    · exact Subgroup.le_centralizer_iff.mp
        (inf_le_left.trans (SevenSix.centerAmbient_le_centralizer P))
    · exact Subgroup.le_centralizer_iff.mp
        (inf_le_right.trans (SevenSix.centerAmbient_le_centralizer L))
  have hnormal : intersection.Normal := by
    constructor
    intro element helement other
    simpa [Subgroup.mem_center_iff.mp (hcentral helement) other, mul_assoc]
      using helement
  have hpower : IsPGroup 2 intersection :=
    (pCore_isPGroup.map P.subtype).of_injective
      (Subgroup.inclusion (inf_le_left.trans hZQ)) (Subgroup.inclusion_injective _)
  apply disjoint_iff.mpr
  apply bot_unique
  rw [← hcore]
  exact le_sSup ⟨hnormal, hpower⟩

public theorem eight_two_distance_one_center_bound_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1)
    (helementary : ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        IsElementaryAbelian 2 (pCore 2 (GAt ctx.Γ d)))
    (hfour : ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        ∃ U : Subgroup (GAt ctx.Γ d), U.Normal ∧
          pCore 2 (GAt ctx.Γ d) = U ⊔ Subgroup.center (GAt ctx.Γ d) ∧
          U ⊓ Subgroup.center (GAt ctx.Γ d) = ⊥ ∧ Nat.card U = 4) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        Nat.card (Subgroup.center (GAt ctx.Γ d)) ≤ 2 := by
  have _ := hlength
  have h7 := ctx.sectionSeven
  have hSylow (d : ctx.Γ.Vertex)
      (hd : d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep) :
      IsSylowTwoIn S (GAt ctx.Γ d) := by
    rcases hd with rfl | rfl
    · exact (SevenSix.edge_sylow_data h7 ctx.Γ ctx.criticalPath).1
    · exact (SevenSix.edge_sylow_data h7 ctx.Γ ctx.criticalPath).2
  have hchar (d : ctx.Γ.Vertex)
      (hd : d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep) :
      Subgroup.centralizer (pCore 2 (GAt ctx.Γ d) : Set (GAt ctx.Γ d)) ≤
        pCore 2 (GAt ctx.Γ d) := by
    rcases hd with rfl | rfl
    · exact (SevenSix.edge_characteristic_data h7 ctx.Γ ctx.criticalPath).1
    · exact (SevenSix.edge_characteristic_data h7 ctx.Γ ctx.criticalPath).2
  have hcoreS (d : ctx.Γ.Vertex)
      (hd : d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep) :
      twoCoreIn (GAt ctx.Γ d) ≤ S := by
    obtain ⟨_, sylow, hsylow⟩ := hSylow d hd
    exact (Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal sylow)).trans_eq hsylow
  have hdata (d : ctx.Γ.Vertex)
      (hd : d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep) :
      CenterAmbient (GAt ctx.Γ d) ≤ twoCoreIn (GAt ctx.Γ d) ∧
      Nat.card (twoCoreIn (GAt ctx.Γ d)) =
        4 * Nat.card (CenterAmbient (GAt ctx.Γ d)) ∧
      (twoCoreIn (GAt ctx.Γ d)).relIndex S = 2 := by
    let _ := helementary d hd
    obtain ⟨factor, hnormal, hQ, hintersection, hcard⟩ := hfour d hd
    let _ := hnormal
    refine ⟨Subgroup.map_mono (hQ ▸ le_sup_right), ?_, ?_⟩
    · rw [twoCoreIn, Subgroup.card_map_of_injective (GAt ctx.Γ d).subtype_injective,
        CenterAmbient, Subgroup.card_map_of_injective (GAt ctx.Γ d).subtype_injective,
        hQ, Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint factor
          (Subgroup.center (GAt ctx.Γ d)) (Subgroup.center_le_normalizer _)
          (disjoint_iff.mpr hintersection), hcard]
    · exact bound_core_index_two _ _ (hSylow d hd)
        (eight_two_actual_core_quotient_of_four_factor_local ctx hcenter d hd factor hQ hcard)
  let left := GAt ctx.Γ ctx.criticalPath.a
  let right := GAt ctx.Γ ctx.criticalPath.firstStep
  have hleft := hdata ctx.criticalPath.a (Or.inl rfl)
  have hright := hdata ctx.criticalPath.firstStep (Or.inr rfl)
  have hleftS := hcoreS ctx.criticalPath.a (Or.inl rfl)
  have hrightS := hcoreS ctx.criticalPath.firstStep (Or.inr rfl)
  have hSleft := (hSylow ctx.criticalPath.a (Or.inl rfl)).1
  have hSright := (hSylow ctx.criticalPath.firstStep (Or.inr rfl)).1
  have hgen : left ⊔ right = ⊤ := by
    rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
    · change ctx.Γ.stabilizer _ ⊔ ctx.Γ.stabilizer _ = ⊤
      rw [hedge.1, hedge.2]
      exact ctx.sectionSeven.generated
    · change ctx.Γ.stabilizer _ ⊔ ctx.Γ.stabilizer _ = ⊤
      rw [hedge.1, hedge.2, sup_comm]
      exact ctx.sectionSeven.generated
  have hleftZ : CenterAmbient left ≤ CenterAmbient S :=
    bound_center_restrict left S hSleft (hleft.1.trans hleftS)
  have hrightZ : CenterAmbient right ≤ CenterAmbient S :=
    bound_center_restrict right S hSright (hright.1.trans hrightS)
  have hdisjoint := bound_disjoint_centers left right hgen h7.twoCore_eq_bot hleft.1
  have hcomm : CenterAmbient left ≤ Subgroup.centralizer (CenterAmbient right : Set G) :=
    (hleftZ.trans (SevenSix.centerAmbient_le_centralizer S)).trans
      (Subgroup.centralizer_le (hright.1.trans hrightS))
  have hproduct : Nat.card (CenterAmbient left) * Nat.card (CenterAmbient right) ≤
      Nat.card (CenterAmbient S) := by
    rw [← Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((Subgroup.le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
      hdisjoint]
    exact Subgroup.card_le_of_le (sup_le hleftZ hrightZ)
  have hsmall := bound_sylow_center_proper left S hSleft hleftS
    (hchar ctx.criticalPath.a (Or.inl rfl)) hleft.2.2
  have hleftIndex : (twoCoreIn left).relIndex S = 2 := hleft.2.2
  have hrightIndex : (twoCoreIn right).relIndex S = 2 := hright.2.2
  have hleftFour : Nat.card (twoCoreIn left) = 4 * Nat.card (CenterAmbient left) := hleft.2.1
  have hrightFour : Nat.card (twoCoreIn right) = 4 * Nat.card (CenterAmbient right) := hright.2.1
  have hleftCard : Nat.card (twoCoreIn left) * 2 = Nat.card S := by
    simpa only [Subgroup.relIndex_bot_left, hleftIndex] using
      (Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (twoCoreIn left) S bot_le hleftS)
  have hrightCard : Nat.card (twoCoreIn right) * 2 = Nat.card S := by
    simpa only [Subgroup.relIndex_bot_left, hrightIndex] using
      (Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (twoCoreIn right) S bot_le hrightS)
  have hequal : Nat.card (CenterAmbient left) = Nat.card (CenterAmbient right) := by
    nlinarith
  have hleftBound : Nat.card (CenterAmbient left) ≤ 2 := by
    have hpos := Nat.card_pos (α := CenterAmbient left)
    nlinarith
  have hrightBound : Nat.card (CenterAmbient right) ≤ 2 := hequal ▸ hleftBound
  intro d hd
  rw [← Subgroup.card_map_of_injective (K := Subgroup.center (GAt ctx.Γ d))
    (GAt ctx.Γ d).subtype_injective]
  rcases hd with rfl | rfl
  · exact hleftBound
  · exact hrightBound

public theorem eight_two_distance_one_center_bound
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1)
    (helementary : ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        IsElementaryAbelian 2 (pCore 2 (GAt ctx.Γ d)))
    (hfour : ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        ∃ U : Subgroup (GAt ctx.Γ d), U.Normal ∧
          pCore 2 (GAt ctx.Γ d) = U ⊔ Subgroup.center (GAt ctx.Γ d) ∧
          U ⊓ Subgroup.center (GAt ctx.Γ d) = ⊥ ∧ Nat.card U = 4) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        Nat.card (Subgroup.center (GAt ctx.Γ d)) ≤ 2 :=
  eight_two_distance_one_center_bound_local ctx.toLocalContext hcenter hlength helementary hfour

end Stellmacher.SectionEight
