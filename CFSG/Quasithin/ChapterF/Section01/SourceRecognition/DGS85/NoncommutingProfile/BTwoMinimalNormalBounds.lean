module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoMinimalNormalSection
public import Mathlib.GroupTheory.Coset.Card
public import Theory.Representation.SL2.TwoGroupSectionBound
public import Theory.GroupTheory.PResidual.PerfectLift

/-!
# Cardinal bounds for the p.165 beta chief section

The strict core orders give the literal total quotient order
`|Q_beta/Z_beta| = q_alpha² q_beta²` and its nontriviality. For nonbinary
beta, the original enlargement is perfect. Its action on every proper
invariant quotient `Q_beta/N` is nontrivial because `[Q_beta,L_beta]=Q_beta`.
The rank-one degree bound therefore gives `|Q_beta/N| >= q_beta²`, hence
`|N/Z_beta| <= q_alpha²` whenever the denominator is contained in N.

If `|N/Z_beta| < q_beta²`, the same action bound makes the quotient action
trivial. Perfectness removes its remaining displacement in the central
Z_beta layer, proving `N <= Z(L_beta)`. These are the representation and
cardinality steps used on p.165, retaining the full original endpoint,
its actual two-core, the reduced-center inclusion and both quotient maps.
Excluding the resulting small central section and the final equality case
remain subsequent source arguments; irreducibility of Q_beta/Z_beta is not
asserted here.

Source: DGS, *Groups and Graphs* (1985), printed p.165.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

/- The literal quotient-card factorization for a nested normal section. -/
public theorem quotient_card_factorization_of_le
    {G : Type*} [Group G] [Finite G]
    (Z N : Subgroup G) [Z.Normal] [N.Normal] (hZN : Z ≤ N) :
    Nat.card (G ⧸ Z) =
      Nat.card (G ⧸ N) * Nat.card (N ⧸ Z.subgroupOf N) := by
  rw [Nat.card_congr (quotientEquivProdOfLE hZN), Nat.card_prod]

/- If the source lower-bound and total-section cardinal are both sharp, the
   complementary quotient is sharp as well. -/
public theorem quotient_card_eq_of_eq_lower_bound
    {G : Type*} [Group G] [Finite G]
    (Z N : Subgroup G) [Z.Normal] [N.Normal] (hZN : Z ≤ N)
    {q : ℕ}
    (hq : 0 < q)
    (hTotal : Nat.card (G ⧸ Z) = q ^ 4)
    (hLower : q ^ 2 ≤ Nat.card (N ⧸ Z.subgroupOf N))
    (hUpper : Nat.card (N ⧸ Z.subgroupOf N) ≤ q ^ 2) :
    Nat.card (N ⧸ Z.subgroupOf N) = q ^ 2 ∧
      Nat.card (G ⧸ N) = q ^ 2 := by
  have hN : Nat.card (N ⧸ Z.subgroupOf N) = q ^ 2 :=
    Nat.le_antisymm hUpper hLower
  have hfactor := quotient_card_factorization_of_le Z N hZN
  have hprod : Nat.card (G ⧸ N) * q ^ 2 = q ^ 4 := by
    calc
      Nat.card (G ⧸ N) * q ^ 2 =
          Nat.card (G ⧸ N) * Nat.card (N ⧸ Z.subgroupOf N) := by rw [hN]
      _ = Nat.card (G ⧸ Z) := hfactor.symm
      _ = q ^ 4 := hTotal
  have hqpos : 0 < q ^ 2 := Nat.pow_pos hq
  have hquot : Nat.card (G ⧸ N) = q ^ 2 := by
    have hpow : q ^ 4 = q ^ 2 * q ^ 2 := by ring
    rw [hpow] at hprod
    apply Nat.eq_of_mul_eq_mul_right hqpos
    exact hprod
  exact ⟨hN, hquot⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

private def original_beta_linear_quotient
    (h : HypothesisF11 L S) {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (family L true ⧸ pCore 2 (family L true)) ≃* PSL(2,K)) :
    (enlargedEndpoint L S 1 ⧸ pCore 2 (enlargedEndpoint L S 1)) ≃* SL(2,K) := by
  let eA := MulEquiv.subgroupCongr (reduced_enlargedEndpoint_eq_starred_of_linear h 1 e)
  exact (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans
    (((originalStarredQuotientEquiv h true).symm.trans e).trans
      (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL K).symm)

/-- The nonbinary original beta enlargement is perfect, using its actual rank-one quotient and two-residual. -/
theorem original_bTwo_nonbinary_beta_isPerfect
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    Group.IsPerfect (enlargedEndpoint L S 1) := by
  have hp := (pResidual_eq_top_iff 2 _).mp
    (original_bTwo_nonbinary_beta_twoPerfect h hc hne hb hβu ht htne K e hK hD)
  have hfour : 3 < Nat.card (K true) := by
    let : Fintype (K true) := Fintype.ofFinite (K true)
    have heven : Even (Nat.card (K true)) := by
      rw [Nat.card_eq_fintype_card,even_iff_two_dvd]
      exact (CharP.cast_eq_zero_iff (K true) 2 _).mp (FiniteField.cast_card_eq_zero (K true))
    obtain ⟨n,hn⟩ := heven
    omega
  let eA := original_beta_linear_quotient h (e true)
  let : Group.IsPerfect SL(2,K true) := GorensteinWalter.sl2_isPerfect_of_card_gt_three _ hfour
  let : Group.IsPerfect (enlargedEndpoint L S 1 ⧸ pCore 2 (enlargedEndpoint L S 1)) :=
    Group.IsPerfect.ofSurjective (f:=eA.symm.toMonoidHom) eA.symm.surjective
  apply hp.isPerfect_of_surjective_pGroup_kernel
    (QuotientGroup.mk' (pCore 2 (enlargedEndpoint L S 1)))
    (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup

/-- The proper-quotient inequality on p.165, without assuming the selected section is already irreducible. -/
theorem original_bTwo_nonbinary_beta_proper_quotient_bound
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N < (parabolic L S 1).pCoreIn 2)
    (hPN : parabolic L S 1 ≤ normalizer (N : Set G)) :
    Nat.card (K true)^2 ≤ Nat.card ((parabolic L S 1).pCoreIn 2 ⧸
      N.subgroupOf ((parabolic L S 1).pCoreIn 2)) := by
  let A := enlargedEndpoint L S 1
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let := h.finite_parabolic 1
  have hAP : A ≤ parabolic L S 1 :=
    sup_le (starredParabolic_le 1) ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic 1))
  let : Finite A := Finite.of_injective (inclusion hAP) (inclusion_injective _)
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Group.IsPerfect A := original_bTwo_nonbinary_beta_isPerfect h hc hne hb hβu ht htne K e hK hD
  let : (N.subgroupOf Q₁).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNQ.le).mpr ((pCoreIn_le 2 _).trans hPN)
  exact Representation.SL2.quotient_card_lower_of_full_commutator A Q₁ N
    (original_beta_linear_quotient h (e true)) (isPGroup_pCoreIn 2 _) hNQ
    (hAP.trans ((parabolic L S 1).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))) (hAP.trans hPN)
    (original_bTwo_nonbinary_beta_core_commutator h hc hne hb hβu ht htne K e hK hD)

/-- The small-section step of p.165: its whole preimage lies in the original beta enlargement center. -/
theorem original_bTwo_nonbinary_beta_small_section_central
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N ≤ (parabolic L S 1).pCoreIn 2)
    (hZN : (Z F β).map ι ≤ N)
    (hPN : parabolic L S 1 ≤ normalizer (N : Set G))
    (hsmall : Nat.card (N ⧸ ((Z F β).map ι).subgroupOf N) < Nat.card (K true)^2) :
    N ≤ centerIn (enlargedEndpoint L S 1) := by
  let A := enlargedEndpoint L S 1
  let Z₁ := (Z F β).map ι
  let := h.finite_parabolic 1
  have hAP : A ≤ parabolic L S 1 :=
    sup_le (starredParabolic_le 1) ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic 1))
  have hNA : N ≤ A := hNQ.trans ((enlargedEndpoint_core h 1).ge.trans (pCoreIn_le 2 _))
  let : Finite A := Finite.of_injective (inclusion hAP) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion (hNA.trans hAP)) (inclusion_injective _)
  let : Group.IsPerfect A := original_bTwo_nonbinary_beta_isPerfect h hc hne hb hβu ht htne K e hK hD
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hcZ := (reduced_bTwo_middle_central h hc hne hb hab hβu).trans inf_le_right
  change Z F β ≤ centralizer (graphLocalGroup F β : Set (G₀ L S)) at hcZ
  have hZA : Z₁ ≤ centralizer (A : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    have hh := congrArg (map ι) (commutator_eq_bot_iff_le_centralizer.mpr hcZ)
    rwa [map_commutator,Subgroup.map_bot,reduced_graphLocalGroup_image h true] at hh
  let : (Z₁.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hZN).mpr
      (hNA.trans ((le_centralizer_iff.mp hZA).trans (Subgroup.centralizer_le_normalizer _)))
  exact le_inf hNA (Representation.SL2.centralizes_of_quotient_card_lt A N Z₁
    (original_beta_linear_quotient h (e true)) ((isPGroup_pCoreIn 2 _).to_le hNQ)
    (hAP.trans hPN) hZA hsmall)

/-- The strict original beta-center inclusion and the exact order of the literal core quotient. -/
theorem original_bTwo_strict_beta_total_section
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let Z₁ := (Z F β).map ι
    Z₁ < Q₁ ∧ Nat.card (Q₁ ⧸ Z₁.subgroupOf Q₁) =
      Nat.card (K false)^2 * Nat.card (K true)^2 := by
  obtain ⟨_,_,_,_,hZb,_,_,hQb,_,_,hPhi,_⟩ :=
    original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₁ := (Z F β).map ι
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  have hZQ : Z₁ ≤ Q₁ := hPhi.symm.le.trans (map_subtype_le _)
  have hfact := card_eq_card_quotient_mul_card_subgroup (Z₁.subgroupOf Q₁)
  rw [Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv] at hfact
  change Nat.card Q₁ = Nat.card (Q₁ ⧸ Z₁.subgroupOf Q₁) * Nat.card Z₁ at hfact
  change Nat.card Z₁=Nat.card (K false) at hZb
  change Nat.card Q₁=Nat.card (K false)^3*Nat.card (K true)^2 at hQb
  have htotal : Nat.card (Q₁ ⧸ Z₁.subgroupOf Q₁) =
      Nat.card (K false)^2*Nat.card (K true)^2 := by
    apply Nat.mul_right_cancel (Nat.card_pos : 0 < Nat.card (K false))
    calc
      Nat.card (Q₁ ⧸ Z₁.subgroupOf Q₁)*Nat.card (K false) = Nat.card Q₁ := by rw [←hZb,←hfact]
      _ = (Nat.card (K false)^2*Nat.card (K true)^2)*Nat.card (K false) := by rw [hQb]; ring
  refine ⟨lt_of_le_of_ne hZQ ?_,htotal⟩
  intro he
  change Z₁ = Q₁ at he
  rw [he,subgroupOf_self] at htotal
  have hqa : 1 < Nat.card (K false)^2 := one_lt_pow₀ (Finite.one_lt_card) (by decide)
  have hqb : 0 < Nat.card (K true)^2 := Nat.pow_pos Nat.card_pos
  have hgt : 1 < Nat.card (K false)^2*Nat.card (K true)^2 :=
    lt_of_lt_of_le hqa (Nat.le_mul_of_pos_right _ hqb)
  have hone : Nat.card (Q₁ ⧸ (⊤ : Subgroup Q₁)) = 1 := by
    rw [←index_eq_card,index_top]
  rw [hone] at htotal
  omega

/-- Every proper beta-stabilizer invariant section above the marked center has order at most q_alpha squared. -/
theorem original_bTwo_nonbinary_beta_section_upper
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N < (parabolic L S 1).pCoreIn 2)
    (hZN : (Z F β).map ι ≤ N)
    (hPN : parabolic L S 1 ≤ normalizer (N : Set G)) :
    Nat.card (N ⧸ ((Z F β).map ι).subgroupOf N) ≤ Nat.card (K false)^2 := by
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₁ := (Z F β).map ι
  have htotal := (original_bTwo_strict_beta_total_section h hc hne hb hβu ht htne K e hD).2
  have hlower := original_bTwo_nonbinary_beta_proper_quotient_bound h hc hne hb hβu ht htne K e hK hD N hNQ hPN
  have hfact := relIndex_mul_relIndex Z₁ N Q₁ hZN hNQ.le
  have htotali : Z₁.relIndex Q₁ = Nat.card (K false)^2*Nat.card (K true)^2 := by
    simpa only [relIndex,index_eq_card] using htotal
  have hloweri : Nat.card (K true)^2 ≤ N.relIndex Q₁ := by
    simpa only [relIndex,index_eq_card] using hlower
  have hbound : Z₁.relIndex N*Nat.card (K true)^2 ≤ Nat.card (K false)^2*Nat.card (K true)^2 := by
    calc
      Z₁.relIndex N*Nat.card (K true)^2 ≤ Z₁.relIndex N*N.relIndex Q₁ := Nat.mul_le_mul_left _ hloweri
      _ = Nat.card (K false)^2*Nat.card (K true)^2 := hfact.trans htotali
  have hresult := Nat.le_of_mul_le_mul_right hbound (Nat.pow_pos (Nat.card_pos : 0<Nat.card (K true)))
  simpa only [relIndex,index_eq_card] using hresult

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
