module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsIdentification
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsKernel

/-!
# TerminalProductLocalFactorsIdentification at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductLocalFactorsIdentification`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem nine_dvd_Le_card_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : 9 ∣ Nat.card P.Le := by
  have hm := card_range_dvd (P.LeBlockAction_at structural C)
  rw [P.LeBlockAction_range_at structural escape C] at hm
  have hc : Nat.card ((alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3))) = 36 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,
      Nat.card_eq_fintype_card,card_alternatingGroup,Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  rw [hc] at hm
  exact dvd_trans (by decide : 9 ∣ 36) hm

theorem Le_quotientCentralizer_not_twoGroup_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ¬ IsPGroup 2 (P.Le ⊓ P.quotientCentralizer : Subgroup G) := by
  let f : P.Le →* MulAut (P.K ⧸ pCore 2 P.K) :=
    P.quotientAction.comp (inclusion (P.Le_le_pointCentralizer.trans C.normalizes))
  have hk : f.ker = P.quotientCentralizer.subgroupOf P.Le := by
    ext x
    constructor
    · intro hx
      exact ⟨inclusion (P.Le_le_pointCentralizer.trans C.normalizes) x,hx,rfl⟩
    · rintro ⟨n,hn,he⟩
      have hn' : n = inclusion (P.Le_le_pointCentralizer.trans C.normalizes) x := Subtype.ext he
      change P.quotientAction (inclusion (P.Le_le_pointCentralizer.trans C.normalizes) x) = 1
      rw [←hn']
      exact hn
  intro hp
  have hkp : IsPGroup 2 f.ker := by
    let j : f.ker →* (P.Le ⊓ P.quotientCentralizer : Subgroup G) :=
      (P.Le.subtype.comp f.ker.subtype).codRestrict _ (fun x =>
        ⟨x.val.property, hk.le x.property⟩)
    exact hp.of_injective j (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : (P.Le ⊓ P.quotientCentralizer : Subgroup G) => (z : G)) h)
  obtain ⟨n,hn⟩ := hkp.exists_card_eq
  have hc : Nat.card P.Le = 2 ^ n * Nat.card f.range := by
    rw [←f.ker.card_mul_index,index_ker,hn]
  have hdiv := P.nine_dvd_Le_card_at structural escape C
  rw [hc] at hdiv
  have hr : 9 ∣ Nat.card f.range := ((by decide : Nat.Coprime 9 2).pow_right n).dvd_of_dvd_mul_left hdiv
  have htarget : Nat.card (MulAut (P.K ⧸ pCore 2 P.K)) = 120 := by
    rw [Nat.card_congr (MulAut.congr C.quotient).toEquiv,
      ←Nat.card_congr Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.toEquiv,
      Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hh := dvd_trans hr f.range.card_subgroup_dvd_card
  rw [htarget] at hh
  norm_num at hh

theorem L2_not_twoGroup_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : ¬ IsPGroup 2 P.L2 := by
  intro hp
  let X := P.Le ⊓ P.quotientCentralizer
  have hp' : IsPGroup 2 (pResidual 2 X) := hp.of_equiv
    ((pResidual 2 X).equivMapOfInjective X.subtype X.subtype_injective).symm
  apply P.Le_quotientCentralizer_not_twoGroup_at structural escape C
  intro x
  obtain ⟨n,hn⟩ := isPGroup_quotient_pResidual 2 (QuotientGroup.mk' (pResidual 2 X) x)
  have hx : x ^ 2 ^ n ∈ pResidual 2 X := (QuotientGroup.eq_one_iff _).mp (by
    change QuotientGroup.mk' (pResidual 2 X) (x ^ 2 ^ n) = 1
    rw [map_pow]; exact hn)
  obtain ⟨m,hm⟩ := hp' ⟨x ^ 2 ^ n,hx⟩
  exact ⟨n + m,by simpa only [pow_add,pow_mul,Subtype.ext_iff,coe_pow,coe_one] using hm⟩

theorem L2_le_secondPointResidual_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.L2 ≤ P.secondPointResidual := by
  let A := P.L2.subgroupOf P.Le
  let B := P.secondPointResidual.subgroupOf P.Le
  have hBL := P.secondPointResidual_le_Le_at structural escape C
  have hAL : IsPPerfect 2 A := P.L2_twoPerfect.of_surjective
    (subgroupOfEquivOfLe P.L2_le_Le).symm.toMonoidHom
    (subgroupOfEquivOfLe P.L2_le_Le).symm.surjective
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    ((P.Le_le_pointNormalizer_at structural C).trans P.secondPointResidual_normalized)
  have hm (X : Subgroup G) (hX : X ≤ P.Le) :
      (X.subgroupOf P.Le).map (P.LeBlockAction_at structural C) =
        (X.subgroupOf P.pointNormalizer).map P.pointBlockAction := by
    rw [LeBlockAction_at,←map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hX hx⟩,hx,Subtype.ext rfl⟩
  have hi : A.map (P.LeBlockAction_at structural C) ≤ B.map (P.LeBlockAction_at structural C) := by
    rw [hm _ P.L2_le_Le,hm _ hBL,P.secondPointResidual_block_image_at structural escape]
    rintro x ⟨n,hn,rfl⟩
    refine ⟨P.L2_first_block_trivial_at structural escape C ⟨n,hn⟩,?_⟩
    have h := mem_map_of_mem P.pointBlockAction
      (show n ∈ P.Le.subgroupOf P.pointNormalizer from P.L2_le_Le hn)
    rw [P.Le_block_image_at structural escape C] at h
    exact h.2
  have hab := isPPerfect_le_of_map_le_of_kernel_normalizes (P.LeBlockAction_at structural C)
    A B hAL (P.LeBlockAction_twoKernel_at structural C) le_normalizer_of_normal hi
  intro x hx
  exact hab (show (⟨x,P.L2_le_Le hx⟩ : P.Le) ∈ A from hx)

theorem secondPointResidual_eq_L2_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.secondPointResidual = P.L2 := by
  have hLR := P.L2_le_secondPointResidual_at structural escape C
  let N := P.L2.subgroupOf P.secondPointResidual
  let f := P.secondResidualProjection_at structural escape
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((P.secondPointResidual_le_Le_at structural escape C).trans (P.Le_normalizes_L2 C))
  let : (N.map f).Normal := Normal.map inferInstance f
    (P.secondResidualProjection_surjective_at structural escape)
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]; decide
  let : IsSimpleGroup (alternatingGroup (Fin 3)) := isSimpleGroup_of_prime_card hcard
  have him : N.map f = ⊤ := by
    rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with hz | ht
    · have hN : N ≤ f.ker := (map_eq_bot_iff N).mp hz
      exact False.elim (P.L2_not_twoGroup_at structural escape C
        (((P.secondResidualProjection_twoKernel_at structural escape C).to_le hN).of_equiv
          (subgroupOfEquivOfLe hLR)))
    · exact ht
  have htop : (⊤ : Subgroup P.secondPointResidual) ≤ N := by
    apply isPPerfect_le_of_map_le_of_kernel_normalizes f ⊤ N
      (P.secondPointResidual_twoPerfect.of_surjective
        (topEquiv : (⊤ : Subgroup P.secondPointResidual) ≃* P.secondPointResidual).symm.toMonoidHom
        (topEquiv : (⊤ : Subgroup P.secondPointResidual) ≃* P.secondPointResidual).symm.surjective)
      (P.secondResidualProjection_twoKernel_at structural escape C) le_normalizer_of_normal
    rw [him]
    exact le_top
  apply le_antisymm ?_ hLR
  intro x hx
  exact htop (show (⟨x,hx⟩ : P.secondPointResidual) ∈ (⊤ : Subgroup P.secondPointResidual) from mem_top _)

theorem Le_eq_L1_sup_L2_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : P.Le = P.L1 ⊔ P.L2 := by
  rw [←P.secondPointResidual_eq_L2_at structural escape C]
  exact P.Le_eq_L1_sup_secondPointResidual_at structural escape C

theorem L2_seed_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ∃ q : (P.L2 ⧸ pCore 2 P.L2) ≃* alternatingGroup (Fin 3),
      Nonempty (Representation.BinaryConjugationSection P.L2 ⁅P.Z,P.L2⁆ ⊥
        ((BinaryPermutation.alternatingCoreRepresentation (Fin 3)).comp
          (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.L2))))) ∧
      ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
        (v : G) ∈ ⁅P.Z,P.L2⁆ :=
  P.second_seed_of_residual_eq_at structural escape C (P.secondPointResidual_eq_L2_at structural escape C)

theorem localFactorAnalysis_of_second_thompson_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (hthompson : ⁅P.L2, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.L2) :
    Nonempty P.LocalFactorAnalysis :=
  P.localFactorAnalysis_of_second_identification_at structural escape C
    (P.secondPointResidual_eq_L2_at structural escape C) hthompson

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

