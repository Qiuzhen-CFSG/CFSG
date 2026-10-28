module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryCensus.Arithmetic
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryCensus.RankRows
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryCensus.IntersectionRows
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryCensus.OddRow
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryCensus.MarkedActor
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryPSL3Four
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete

/-!
# The three component rows in the secondary centralizer

The original 2.3.9 refinement is screened using the actual secondary Sylow
order, two-rank, two-group intersection with M and residual alternating-four
action. The retained rows are A6, PSL2(7) and PSL2(17). The Bender exclusion
uses the original two noncommuting residual four-groups; every classification
and model-action input is supplied internally by the original source setup.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
variable {G : Type*} [Group G] [Finite G]

theorem secondary_component_three_rows
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)
    (P : Sylow 2 (centralizer ({u}:Set G))) (M : Subgroup G) (z : G)
    (K : Subgroup (centralizer ({u}:Set G)))
    (c : ComponentRefinement.MathieuSourceSetup (centralizer ({u}:Set G))
      (K.map (centralizer ({u}:Set G)).subtype) M P z)
    (hK : IsComponent (centralizer ({u}:Set G)) K)
    (hP : Nat.card P ≤ 128)
    (hrank : primeRank 2 (centralizer ({u}:Set G)) ≤ 4)
    (hM : IsPGroup 2 ((centralizer ({u}:Set G)) ⊓ M : Subgroup G))
    (ho : pPrimeCore 2 (centralizer ({u}:Set G))=⊥)
    (L R : Subgroup (centralizer ({u}:Set G))) (hL : IsPPerfect 2 L)
    (eA : L ≃* alternatingGroup (Fin 4))
    (a : L) (ha : a ∈ pCore 2 L) (hz : z=(a:G)*u)
    (hEP : (pCore 2 L).map L.subtype ≤ (P : Subgroup (centralizer ({u}:Set G))))
    (hRL : R ≤ normalizer (L : Set (centralizer ({u}:Set G))))
    (hri : R.relIndex (P : Subgroup (centralizer ({u}:Set G))) ≤ 2)
    (x : centralizer ({u}:Set G)) (hx : x ∈ P)
    (hnc : ¬ ((pCore 2 L).map L.subtype).map (MulAut.conj x).toMonoidHom ≤
      centralizer (((pCore 2 L).map L.subtype : Subgroup (centralizer ({u}:Set G))) : Set (centralizer ({u}:Set G)))) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (K ≃* PSL(2,ZMod 7)) ∨ Nonempty (K ≃* PSL(2,ZMod 17)) := by
  let H := centralizer ({u}:Set G)
  let A := K.map H.subtype
  let e : K ≃* A := K.equivMapOfInjective H.subtype H.subtype_injective
  let v : H := ⟨u,mem_centralizer_singleton_iff.mpr rfl⟩
  have hv : v ∈ center H := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (mem_centralizer_singleton_iff.mp k.property)
  have hv2 : orderOf v=2 := (orderOf_injective H.subtype H.subtype_injective v).symm.trans hu
  have h115 := c.lemma115_hypotheses hG
  have hnb (hb : ClassificationModels.IsBenderModel K) : False :=
    secondary_bender_component_false hG u hu P M z K c h115 L R hL hK eA a ha hz
      hEP hRL hri ho x hx hnc hb
  obtain ⟨_,href⟩ := c.source_refinement_or_binary_mathieu hG
    (fun X _ _ => ChapterA.Section02.theoremsABC_knownSimple (G := X))
    localC129Input_knownSimple
  rcases href with href | ⟨hc,⟨f⟩,_⟩
  · cases href with
    | bender hm => exact (hnb (hm.of_mulEquiv e)).elim
    | case_b hm =>
      rcases hm with hm | ⟨n,hn,hm⟩ | hm | hm
      · obtain ⟨n,hn,F,hF,hfin,hcard,⟨f⟩⟩ := hm
        exact .inl (symplectic_row_of_sylow_card_le_128 P hP K
          ⟨n,hn,F,hF,hfin,hcard,⟨e.trans f⟩⟩)
      · exact .inr (.inl (binary_linear_three_row_of_rank_le_four K v hv hv2 hrank hn
          (hm.of_mulEquiv e)))
      · exact (c.centralizer_psl_three_four_false hG hu hrank hm).elim
      · exact (triple_alternating_six_row_false H A c.component c.component_le ho hm).elim
    | alternating hm =>
      obtain ⟨_,_,_,_,f,_⟩ := hm
      exact (alternating_seven_intersection_false H A M c.component_le hM f).elim
    | linear_three hm hi =>
      obtain ⟨f⟩ := hm
      obtain ⟨t,ht,_,hi⟩ := hi
      exact (odd_linear_three_intersection_false H A M c.component_le hM f t ht hi).elim
    | linear_two p hp hm _ =>
      have hmK := hm.of_mulEquiv e
      rcases secondary_prime_component_parameter hG u hu P M z h115 L R K hL hK eA a ha hz
        hRL hri hp hmK with hp5 | hp7 | hp17
      · subst p
        obtain ⟨F,_,_,hF,⟨f⟩⟩ := hmK
        have hb : ClassificationModels.IsBenderModel K := .linear 2 (by decide)
          ⟨GaloisField 2 2,inferInstance,inferInstance,GaloisField.card 2 2 (by decide),
            ⟨f.trans (Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hF)⟩⟩
        exact (hnb hb).elim
      · subst p
        let : Fact (Nat.Prime 7) := ⟨hp.1⟩
        obtain ⟨F,_,_,hF,⟨f⟩⟩ := hmK
        let : Fintype F := Fintype.ofFinite F
        let eF : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq (K := F) (K' := ZMod 7) (by
          simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
        exact .inr (.inl ⟨f.trans (GorensteinWalter.psl2RingEquiv eF)⟩)
      · subst p
        let : Fact (Nat.Prime 17) := ⟨hp.1⟩
        obtain ⟨F,_,_,hF,⟨f⟩⟩ := hmK
        let : Fintype F := Fintype.ofFinite F
        let eF : F ≃+* ZMod 17 := FiniteField.ringEquivOfCardEq (K := F) (K' := ZMod 17) (by
          simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
        exact .inr (.inr ⟨f.trans (GorensteinWalter.psl2RingEquiv eF)⟩)
    | sporadic hm =>
      rcases hm with ⟨⟨f⟩,t,ht,_,hi⟩ | ⟨f,_,_⟩ | ⟨f,_,_⟩
      · exact (mathieu_eleven_intersection_false H A M c.component_le hM f t ht hi).elim
      · exact (mathieu_twenty_two_row_false P hP K v hv hv2 (e.trans f)).elim
      · exact (mathieu_twenty_three_row_false P hP K v hv hv2 (e.trans f)).elim
    | case_g hm =>
      obtain ⟨f,_⟩ := hm
      exact (binary_linear_four_row_false K v hv hv2 hrank (e.trans f)).elim
  · let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    have hcK : Nat.card (pCore 2 K)=2 := by
      exact (Nat.card_congr ((e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))).toEquiv).trans hc
    exact (binary_mathieu_row_false_of_sylow_card_le_128 P hP K hcK (q.trans f)).elim

end CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
