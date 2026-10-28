module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsKernel

/-!
# Identifying the literal second terminal factor

The original A₄×A₃ image makes nine divide |L_e|. Since Aut(K/O₂(K))
has order 120, the kernel of the literal quotient action cannot be a
two-group, and neither can its two-residual L₂. Its first-block image
is trivial by the preceding module. Two-perfection lifts containment
in the second block residual through the original two-group kernel;
the remaining prime-order quotient and relative normality force equality.

Consequently the literal L₁ and L₂ generate L_e. The final applications
supply the original L₂ quotient marking, its entire natural seed and a
weight-two point, and remove the factor-identification premise from
LocalFactorAnalysis. Thompson generation and ProductAnalysis remain with
qt-d-1231-terminal-product; ComponentAnalysis is discharged by
qt-d-1231-terminal.
Source: Aschbacher--Smith, 12.3.13 and completion of 12.3.1, pp.811--812.
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

/-- The cubic square in the literal local residual is visible in its original
A₄×A₃ block quotient. -/
theorem nine_dvd_Le_card
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : 9 ∣ Nat.card P.Le := by
  have hm := card_range_dvd (P.LeBlockAction structural C)
  rw [P.LeBlockAction_range structural escape C] at hm
  have hc : Nat.card ((alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3))) = 36 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,
      Nat.card_eq_fintype_card,card_alternatingGroup,Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  rw [hc] at hm
  exact dvd_trans (by decide : 9 ∣ 36) hm

/-- The action on K/O₂(K) cannot account for both cubic factors. -/
theorem Le_quotientCentralizer_not_twoGroup
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
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
  have hdiv := P.nine_dvd_Le_card structural escape C
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

theorem L2_not_twoGroup
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : ¬ IsPGroup 2 P.L2 := by
  intro hp
  let X := P.Le ⊓ P.quotientCentralizer
  have hp' : IsPGroup 2 (pResidual 2 X) := hp.of_equiv
    ((pResidual 2 X).equivMapOfInjective X.subtype X.subtype_injective).symm
  apply P.Le_quotientCentralizer_not_twoGroup structural escape C
  intro x
  obtain ⟨n,hn⟩ := isPGroup_quotient_pResidual 2 (QuotientGroup.mk' (pResidual 2 X) x)
  have hx : x ^ 2 ^ n ∈ pResidual 2 X := (QuotientGroup.eq_one_iff _).mp (by
    change QuotientGroup.mk' (pResidual 2 X) (x ^ 2 ^ n) = 1
    rw [map_pow]; exact hn)
  obtain ⟨m,hm⟩ := hp' ⟨x ^ 2 ^ n,hx⟩
  exact ⟨n + m,by simpa only [pow_add,pow_mul,Subtype.ext_iff,coe_pow,coe_one] using hm⟩

theorem L2_le_secondPointResidual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.L2 ≤ P.secondPointResidual := by
  let A := P.L2.subgroupOf P.Le
  let B := P.secondPointResidual.subgroupOf P.Le
  have hBL := P.secondPointResidual_le_Le structural escape C
  have hAL : IsPPerfect 2 A := P.L2_twoPerfect.of_surjective
    (subgroupOfEquivOfLe P.L2_le_Le).symm.toMonoidHom
    (subgroupOfEquivOfLe P.L2_le_Le).symm.surjective
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    ((P.Le_le_pointNormalizer structural C).trans P.secondPointResidual_normalized)
  have hm (X : Subgroup G) (hX : X ≤ P.Le) :
      (X.subgroupOf P.Le).map (P.LeBlockAction structural C) =
        (X.subgroupOf P.pointNormalizer).map P.pointBlockAction := by
    rw [LeBlockAction,←map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hX hx⟩,hx,Subtype.ext rfl⟩
  have hi : A.map (P.LeBlockAction structural C) ≤ B.map (P.LeBlockAction structural C) := by
    rw [hm _ P.L2_le_Le,hm _ hBL,P.secondPointResidual_block_image structural escape]
    rintro x ⟨n,hn,rfl⟩
    refine ⟨P.L2_first_block_trivial structural escape C ⟨n,hn⟩,?_⟩
    have h := mem_map_of_mem P.pointBlockAction
      (show n ∈ P.Le.subgroupOf P.pointNormalizer from P.L2_le_Le hn)
    rw [P.Le_block_image structural escape C] at h
    exact h.2
  have hab := isPPerfect_le_of_map_le_of_kernel_normalizes (P.LeBlockAction structural C)
    A B hAL (P.LeBlockAction_twoKernel structural C) le_normalizer_of_normal hi
  intro x hx
  exact hab (show (⟨x,P.L2_le_Le hx⟩ : P.Le) ∈ A from hx)

/-- The second block residual equals the literal residual centralizing
K/O₂(K); this discharges the last factor-identification premise. -/
theorem secondPointResidual_eq_L2
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.secondPointResidual = P.L2 := by
  have hLR := P.L2_le_secondPointResidual structural escape C
  let N := P.L2.subgroupOf P.secondPointResidual
  let f := P.secondResidualProjection structural escape
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((P.secondPointResidual_le_Le structural escape C).trans (P.Le_normalizes_L2 C))
  let : (N.map f).Normal := Normal.map inferInstance f
    (P.secondResidualProjection_surjective structural escape)
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]; decide
  let : IsSimpleGroup (alternatingGroup (Fin 3)) := isSimpleGroup_of_prime_card hcard
  have him : N.map f = ⊤ := by
    rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with hz | ht
    · have hN : N ≤ f.ker := (map_eq_bot_iff N).mp hz
      exact False.elim (P.L2_not_twoGroup structural escape C
        (((P.secondResidualProjection_twoKernel structural escape C).to_le hN).of_equiv
          (subgroupOfEquivOfLe hLR)))
    · exact ht
  have htop : (⊤ : Subgroup P.secondPointResidual) ≤ N := by
    apply isPPerfect_le_of_map_le_of_kernel_normalizes f ⊤ N
      (P.secondPointResidual_twoPerfect.of_surjective
        (topEquiv : (⊤ : Subgroup P.secondPointResidual) ≃* P.secondPointResidual).symm.toMonoidHom
        (topEquiv : (⊤ : Subgroup P.secondPointResidual) ≃* P.secondPointResidual).symm.surjective)
      (P.secondResidualProjection_twoKernel structural escape C) le_normalizer_of_normal
    rw [him]
    exact le_top
  apply le_antisymm ?_ hLR
  intro x hx
  exact htop (show (⟨x,hx⟩ : P.secondPointResidual) ∈ (⊤ : Subgroup P.secondPointResidual) from mem_top _)

/-- The literal local product required on printed p.812. -/
theorem Le_eq_L1_sup_L2
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : P.Le = P.L1 ⊔ P.L2 := by
  rw [←P.secondPointResidual_eq_L2 structural escape C]
  exact P.Le_eq_L1_sup_secondPointResidual structural escape C

/-- Actual application of the residual identification to the published
quotient, natural-module and original weight-two point requirements. -/
theorem L2_seed
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ∃ q : (P.L2 ⧸ pCore 2 P.L2) ≃* alternatingGroup (Fin 3),
      Nonempty (Representation.BinaryConjugationSection P.L2 ⁅P.Z,P.L2⁆ ⊥
        ((BinaryPermutation.alternatingCoreRepresentation (Fin 3)).comp
          (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.L2))))) ∧
      ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
        (v : G) ∈ ⁅P.Z,P.L2⁆ :=
  P.second_seed_of_residual_eq structural escape C (P.secondPointResidual_eq_L2 structural escape C)

/-- The original local-factor interface now needs only its Thompson identity,
which remains with qt-d-1231-terminal-product. -/
theorem localFactorAnalysis_of_second_thompson
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (hthompson : ⁅P.L2, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.L2) :
    Nonempty P.LocalFactorAnalysis :=
  P.localFactorAnalysis_of_second_identification structural escape C
    (P.secondPointResidual_eq_L2 structural escape C) hthompson

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
