module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.NormalizerNatural
public import Theory.Representation.SmallDisplacementParabolics.PairedRecognition

/-!
# The full exchanged partner action and its parabolic contradiction

The two literal component images are disjoint and commute. One acts fully
on the recognized natural three-space, so their conjugacy and the index-two
normalizer give the lower bound for the full wreath-group order. Clifford
invariance and the original exchanger permute the complementary three-spaces.
Faithfulness then identifies the whole action with GL₃(2) wr C₂. The resulting
isomorphism sends the specified exchanger to a nontrivial permutation of the
two coordinates; its exact linear action is retained in the intertwiner.

Apply the existing moving-parabolic theorem to the original chief quotient
and the same nonzero H-fixed source-plane vector. This closes the exchanged
branch without any remaining recognition, transport or parabolic premise.
The final source reduction leaves precisely irreducible restriction to the
literal component normalizer. Its exclusion, general partner-core placement
and critical-pair assembly remain with qt-e-152-critical-pair. The unchanged
earlier source premises are discharged by qt-e-152-chosen-action-contradiction.

Source: Aschbacher–Smith 15.2.12(2)(iii) and 15.2.27(2), printed p.1119;
G.6.4, printed pp.345–346; Clifford theory, Isaacs, Theorem 6.5.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition
open Representation.BinaryOffender Representation.SmallDisplacementParabolics
universe u
variable {G W : Type u} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem subrepresentation_map_self (ρ : Representation (ZMod 2) G W)
    (I : Subgroup G) (C : Subrepresentation (ρ.comp I.subtype)) (g : I) :
    C.toSubmodule.map (ρ (g : G)) = C.toSubmodule := by
  apply le_antisymm
  · rintro w ⟨v,hv,rfl⟩
    exact C.apply_mem_toSubmodule g hv
  · intro w hw
    refine ⟨ρ (g : G)⁻¹ w,C.apply_mem_toSubmodule g⁻¹ hw,?_⟩
    simp

/-- The actual full pair action, not just its constituent types, is the natural wreath action. -/
theorem ExchangedCentralConstituents.paired_model
    {ρ : Representation (ZMod 2) G W} (hf : Function.Injective ρ)
    {I : Subgroup G} [I.Normal] (hi : I.index = 2) {t : G} (ht : t ∉ I) {a : I}
    (E : ExchangedCentralConstituents ρ I t a) (A : Subgroup G)
    (hAI : A ≤ I) (hBI : A.conjBy t ≤ I)
    (hdis : Disjoint A (A.conjBy t)) (hcomm : ⁅A,A.conjBy t⁆ = ⊥)
    (hnat : E.NaturalFactors A (A.conjBy t)) :
    ∃ e : G ≃* PairedActor, ∃ F : W ≃ₗ[ZMod 2] (PairIndex → ThreeSpace),
      (∀ g w i, F (ρ g w) i = (e g).left i (F w ((e g).right⁻¹ * i))) ∧
      (e t).right ≠ 1 := by
  let C := E.constituent
  let D := conjugateSubrepresentation ρ I C t
  obtain ⟨eK,eW,_,_⟩ := hnat.1
  let e0 : C.toSubmodule ≃ₗ[ZMod 2] ThreeSpace :=
    (Submodule.topEquiv (R := ZMod 2) (M := C.toSubmodule)).symm.trans eW
  let e1 : D.toSubmodule ≃ₗ[ZMod 2] ThreeSpace :=
    (conjugateSubrepresentationEquiv ρ I C t).toLinearEquiv.trans e0
  have hperm (g : G) :
      (C.toSubmodule.map (ρ g) = C.toSubmodule ∧ D.toSubmodule.map (ρ g) = D.toSubmodule) ∨
      (C.toSubmodule.map (ρ g) = D.toSubmodule ∧ D.toSubmodule.map (ρ g) = C.toSubmodule) := by
    by_cases hg : g ∈ I
    · exact Or.inl ⟨subrepresentation_map_self ρ I C ⟨g,hg⟩,
        subrepresentation_map_self ρ I D ⟨g,hg⟩⟩
    right
    have hk : t⁻¹ * g ∈ I := (I.mul_mem_iff_of_index_two hi).mpr
      (iff_of_false (fun hh => ht (I.inv_mem_iff.mp hh)) hg)
    have hmul (U : Submodule (ZMod 2) W) :
        U.map (ρ g) = (U.map (ρ (t⁻¹*g))).map (ρ t) := by
      rw [←Submodule.map_comp]
      change U.map (ρ g) = U.map (ρ t * ρ (t⁻¹*g))
      rw [←map_mul,mul_inv_cancel_left]
    rw [hmul,hmul,subrepresentation_map_self ρ I C ⟨_,hk⟩,
      subrepresentation_map_self ρ I D ⟨_,hk⟩]
    exact E.exchange
  let LinearThree := BinaryLinear.OuterCyclic.LinearGroup 3
  let : Finite LinearThree := Finite.of_injective
    (fun g : LinearThree => (g : ThreeSpace → ThreeSpace)) DFunLike.coe_injective
  have hsize : Nat.card (actionImage C.toRepresentation) = Nat.card LinearThree :=
    Nat.card_congr (Subgroup.topEquiv.symm.trans eK).toEquiv
  have hfull (B : Subgroup G) (hBI : B ≤ I)
      (hb : (B.subgroupOf I).map (actionHom C.toRepresentation) = ⊤) :
      Nat.card LinearThree ≤ Nat.card B := by
    let f := (actionHom C.toRepresentation).comp (B.subgroupOf I).subtype
    have hf : Function.Surjective f := by
      apply MonoidHom.range_eq_top.mp
      rw [MonoidHom.range_comp,Subgroup.range_subtype]
      exact hb
    have hh := Nat.card_le_card_of_surjective f hf
    rw [hsize,Nat.card_congr (subgroupOfEquivOfLe hBI).toEquiv] at hh
    exact hh
  have hBA : Nat.card (A.conjBy t) = Nat.card A :=
    (Nat.card_congr ((MulAut.conj t).subgroupMap A).toEquiv).symm
  have hbound : Nat.card LinearThree ≤ Nat.card A := by
    rcases hnat.2 with hh | hh
    · exact hfull A hAI hh.1
    · simpa only [hBA] using hfull (A.conjBy t) hBI hh.2
  obtain ⟨ep,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A (A.conjBy t)
    hdis (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hprod : Nat.card A * Nat.card A ≤ Nat.card I := by
    have hh := Nat.card_le_card_of_injective
      (inclusion (sup_le hAI hBI)) (inclusion_injective (sup_le hAI hBI))
    rw [←Nat.card_congr ep.toEquiv,Nat.card_prod,hBA] at hh
    exact hh
  have hcard : Nat.card PairedActor ≤ Nat.card G := by
    have hh := I.index_mul_card
    rw [hi] at hh
    rw [RegularWreathProduct.card]
    have hc : Nat.card PairIndex = 2 := by simp [Nat.card_eq_fintype_card]
    rw [hc,pow_two]
    change Nat.card LinearThree * Nat.card LinearThree * 2 ≤ Nat.card G
    have hm := Nat.mul_le_mul_right 2 (le_trans (Nat.mul_self_le_mul_self hbound) hprod)
    omega
  obtain ⟨e,F,hF,hswap⟩ := PairedRecognition.marked_model_of_complementary
    ρ hf C.toSubmodule D.toSubmodule E.complementary e0 e1 hcard hperm
  exact ⟨e,F,hF,hswap t E.exchange.1⟩
end CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition

namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open NoncentralChiefRefinement PartnerChiefRecognition
open Representation.SmallDisplacementParabolics
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exchanged source constituents give the full paired action on the original quotient. -/
theorem source_chosen_exchanged_paired_model
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (C : Subgroup G) (t : G) (hC : C ∈ Chapter1.cComponentsIn Mc)
    (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (C : Set G))
    (he : partnerSpan H Mc = C ⊔ C.conjBy t)
    (hm : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 (2 ^ n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 p)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
    let A := (C.subgroupOf L).map q
    let I := normalizer (A : Set (L ⧸ pCore 2 L))
    ∀ (σ : Representation (ZMod 2) (L ⧸ pCore 2 L) W),
      PartnerChiefQuotientProperties T V L σ →
      ∀ hi : I.index = 2, letI := normal_of_index_eq_two hi
        ∀ (a : I) (_E : ExchangedCentralConstituents σ I (q tL) a),
          ∃ e : (L ⧸ pCore 2 L) ≃* PairedActor,
            ∃ F : W ≃ₗ[ZMod 2] (PairIndex → ThreeSpace),
              (∀ g w i, F (σ g w) i = (e g).left i (F w ((e g).right⁻¹ * i))) ∧
              (e (q tL)).right ≠ 1 := by
  dsimp only
  intro σ hp hi a E
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
  let A := (C.subgroupOf L).map q
  let B := A.conjBy (q tL)
  let I := normalizer (A : Set (L ⧸ pCore 2 L))
  let : I.Normal := normal_of_index_eq_two hi
  obtain ⟨hA,hsA,_,_,htI⟩ := source_chosen_pair_normalizer_data hg C t hC ht htn he hm
  change IsComponent (L ⧸ pCore 2 L) A at hA
  let : IsSimpleGroup A := hsA
  have hB : IsComponent (L ⧸ pCore 2 L) B := hA.map_conj (q tL)
  have hne : A ≠ B := fun hh => htI (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  have hcomm := hA.commutator_eq_bot_of_ne hB hne
  have hAI : A ≤ I := A.le_normalizer
  have hBI : B ≤ I := (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans (_root_.centralizer_le_normalizer A)
  let := hA.2
  have hz : center A = ⊥ :=
    (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp hh))
  have hdis : Disjoint A B := by
    apply disjoint_def.mpr
    intro x hx hy
    have hxz : (⟨x,hx⟩ : A) ∈ center A := mem_center_iff.mpr fun y =>
      Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hcomm y.property) x hy).symm)
    exact congrArg (fun x : A => (x : L ⧸ pCore 2 L)) (mem_bot.mp (hz ▸ hxz))
  exact E.paired_model hp.1 hi htI A hAI hBI hdis hcomm
    (source_chosen_exchanged_constituent_natural_three h hg C t hC ht htn he hm σ hp hi a E)

/-- The constructed paired action feeds the actual moving-parabolic consumer with the same fixed vector. -/
theorem source_chosen_false_of_exchanged_partner_chief
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G))
    (C : Subgroup G) (t : G) (hC : C ∈ Chapter1.cComponentsIn Mc)
    (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (C : Set G))
    (he : partnerSpan H Mc = C ⊔ C.conjBy t)
    (hm : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 (2 ^ n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 p)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
    let A := (C.subgroupOf L).map q
    let I := normalizer (A : Set (L ⧸ pCore 2 L))
    ∀ (σ : Representation (ZMod 2) (L ⧸ pCore 2 L) W),
      PartnerChiefQuotientProperties T V L σ →
      ∀ hi : I.index = 2, letI := normal_of_index_eq_two hi
        ∀ (a : I) (_E : ExchangedCentralConstituents σ I (q tL) a),
          ∀ w : W, w ≠ 0 →
            (∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → σ (q g) w = w) →
            (∀ g ∈ (H.subgroupOf L).map q, σ g w = w) → False := by
  dsimp only
  intro σ hp hi a E w hw hfix hHfix
  obtain ⟨e,F,hF,_⟩ := source_chosen_exchanged_paired_model h hg C t hC ht htn he hm σ hp hi a E
  exact source_chosen_false_of_partner_actionModel h hg hMc hplane σ w hw
    (Or.inr (Or.inr ⟨e,F,hF⟩)) hfix hHfix
/-- A hypothetical noncore source module now forces irreducible restriction to the literal component normalizer. -/
theorem source_chosen_noncore_partner_irreducible_chief
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    ∃ (C : Subgroup G) (t : G) (ht : t ∈ (T : Subgroup G)),
      C ∈ Chapter1.LStar G (T : Subgroup G) ∧ C ∈ Chapter1.cComponentsIn Mc ∧
      t ∉ normalizer (C : Set G) ∧ partnerSpan H Mc = C ⊔ C.conjBy t ∧
      (partnerSpan H Mc : Set G) = (C : Set G) * (C.conjBy t : Set G) ∧
      ((∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 (2 ^ n)) ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 p) ∧
      ∃ (B U : NormalNode L) (hc : B ⋖ U)
        (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
        centralInvolutions T ≤ B.val.map L.subtype ∧
        let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
          (map_le_iff_le_comap.mp hU)
        letI := chief_elementary B U hc hp
        ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Section B U)),
          σ.comp q = binarySectionRepresentation B U ∧
          PartnerChiefQuotientProperties T V L σ ∧
          ∃ a : L, (a : G) ∈ V ∧ orderOf (q a) = 2 ∧
            (∀ s ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q s)) ∧
            Module.finrank (ZMod 2) (LinearMap.range
              (σ (q a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) = 2 ∧
            ∃ w : Additive (Section B U), w ≠ 0 ∧
              (∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → σ (q g) w = w) ∧
              (∀ g ∈ (H.subgroupOf L).map q, σ g w = w) ∧
              let _tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
              let I := normalizer (((C.subgroupOf L).map q : Subgroup (L ⧸ pCore 2 L)) : Set _)
              ∃ hi : I.index = 2, letI := normal_of_index_eq_two hi
                ∃ _haI : q a ∈ I, IsIrreducible (σ.comp I.subtype) := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨C,t,ht,hCL,hC,htn,he,hset,hm,B,U,hc,hU,hB,hσ⟩ :=
    source_chosen_noncore_partner_natural_chief h hg hMc hZ hquotient hres hs hn hplane
  refine ⟨C,t,ht,hCL,hC,htn,he,hset,hm,B,U,hc,hU,hB,?_⟩
  have hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,hσeq,hprop,a,ha,ho,hacent,hr,w,hw,hfix,hHfix,hi,haI,hh⟩ := hσ
  let := normal_of_index_eq_two hi
  refine ⟨σ,hσeq,hprop,a,ha,ho,hacent,hr,w,hw,hfix,hHfix,hi,haI,?_⟩
  rcases hh with hirr | ⟨E,_,_,_⟩
  · exact hirr
  · exact (source_chosen_false_of_exchanged_partner_chief h hg hMc hplane
      C t hC ht htn he hm σ hprop hi ⟨_,haI⟩ E w hw hfix hHfix).elim

end CFSG.Quasithin.Chapter15.Section02
