module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.Source
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.ResidualEquality.Structure
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.ResidualEquality.Lifting


/-!
# Equality of the two residuals in the five case

Write X = Ξ_p(L), R = O₂(XT), Y = N_L(R)^∞ and L_C = N_L(C)^∞.
Given the genuine source setup, p = 5, case (10) with parameter five,
and the marked extension in K/O₂(K), we prove Y = L_C and that five
is the only odd prime dividing F(L_C/O₂(L_C)).

Normality of X in L_C identifies its image in L_C/O₂(L_C) with
X/O₂(X), hence supplies a nontrivial normal five-subgroup. We apply
the full earlier A.3.6 to the actual image of L_C in (L_C T)/O₂(L_C T).
Its hypotheses follow from the ambient QTKE assumption and the local
C-component witness. The order bound in PSL₃(5), followed by the Sylow
normalizer and perfectness argument, proves equality in the original group.

The universal A.3.6 statement remains an explicit earlier input. No
parabolic recognition, rigidity result or signalizer theorem is used.
Source: Aschbacher–Smith, proof of 1.3.8, printed p.513, with A.3.6,
printed pp.43–45, and 1.2.1(4), printed p.504; combined manuscript of
1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase.ResidualEquality
open Section02 Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

private noncomputable def normalTwoCoreQuotientEquiv {B : Subgroup G} [B.Normal] :
    XiQuotient B ≃* B.map (QuotientGroup.mk' (pCore 2 G)) := by
  let f := (QuotientGroup.mk' (pCore 2 G)).subgroupMap B
  have he : f.ker = pCore 2 B := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 (inferInstance : B.Normal).isSubnormal).symm
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pCore 2 G)).subgroupMap_surjective B))

private theorem fitting_prime_of_normal_xi {p : ℕ} [Fact p.Prime] {X D : Subgroup G}
    (hXD : X ≤ D) [(X.subgroupOf D).Normal]
    (hx : XiOddQuotient p (XiQuotient X)) :
    p ∣ Nat.card (fittingSubgroup (XiQuotient D)) := by
  let B := X.subgroupOf D
  let e : X ≃* B := (subgroupOfEquivOfLe hXD).symm
  let ebar : XiQuotient X ≃* B.map (QuotientGroup.mk' (pCore 2 D)) :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans normalTwoCoreQuotientEquiv
  have hshape := hx.of_mulEquiv ebar
  let f := QuotientGroup.mk' (pCore 2 D)
  have hn : (B.map f).Normal := (inferInstance : B.Normal).map f
    (QuotientGroup.mk'_surjective _)
  have hBF : B.map f ≤ fittingSubgroup (XiQuotient D) :=
    (show B.map f ≤ pCore p (XiQuotient D) from le_sSup ⟨hn, hshape.isPGroup⟩).trans
      (pCore_le_fitting _ p)
  apply (dvd_trans · (card_dvd_of_le hBF))
  rcases hshape with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;>
    exact dvd_pow_self p (by decide)

private theorem source_fitting_five {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G}
    {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K) (hp : p = 5) :
    5 ∣ Nat.card (fittingSubgroup (XiQuotient
      (normalizerResidual L (C.map (radicalCore p L T).subtype)))) := by
  let := h.characteristic
  let : Fact p.Prime := ⟨h.prime⟩
  have hXD := h.contains_xi.trans
    (normalizerResidual_le_of_characteristic L (radicalCore p L T) C)
  let := xi_normal_in_intermediate p (normalizerResidual_le L
    (C.map (radicalCore p L T).subtype))
  exact hp ▸ fitting_prime_of_normal_xi hXD h.xi_shape

private theorem source_local_quotient_sqtk {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G}
    {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K) :
    IsSQTK 𝒦 (XiQuotient
      (normalizerResidual L (C.map (radicalCore p L T).subtype) ⊔ T : Subgroup G)) := by
  let := h.characteristic
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  let H := normalizerResidual L (C.map (radicalCore p L T).subtype) ⊔ (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ N := (t_le_normalizer_radicalCore p L T).trans
    (normalizer_le_normalizer_characteristic_image _ C)
  have hHN : H ≤ N := sup_le (normalizerResidual_le_normalizer L _) hTN
  have hH : IsSQTK 𝒦 H := (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((h.ambient.twoLocal_sqtk (characteristic_normalizer_isTwoLocal p L T C h.nontrivial)).subgroup
      (H.subgroupOf N))
  refine ⟨?_, hH.isKGroup.quotient _⟩
  intro q hq ho
  let : Fact q.Prime := ⟨hq⟩
  exact (primeRank_quotient_le_of_isTwoGroup q ho _ pCore_isPGroup).trans
    (hH.stronglyQuasithin q hq ho)

private theorem fitting_card_dvd {A B : Type*} [Group A] [Group B] [Finite A]
    (e : A ≃* B) : Nat.card (fittingSubgroup A) ∣ Nat.card (fittingSubgroup B) := by
  have hm : (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
    exact le_sSup ⟨(inferInstance : (fittingSubgroup A).Normal).map _ e.surjective,
      Group.nilpotent_of_mulEquiv (e.subgroupMap (fittingSubgroup A))⟩
  rw [Nat.card_congr (e.subgroupMap (fittingSubgroup A)).toEquiv]
  exact card_dvd_of_le hm

private theorem fitting_card_eq {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : Nat.card (fittingSubgroup A) = Nat.card (fittingSubgroup B) :=
  Nat.dvd_antisymm (fitting_card_dvd e) (fitting_card_dvd e.symm)

/-- A.3.6 applied to the genuine local C-component gives the exact quotient
order and odd Fitting support. Its SQTK and quotient hypotheses are proved
from `SourceData`; only the universal earlier theorem is a parameter. -/
theorem quotient_order_and_fitting_support {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ D : Subgroup E,
      D.IsCComponent → A36Conclusion D)
    {p r : ℕ} {L : Subgroup G} {T : Sylow 2 G}
    {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K) (hp : p = 5)
    (hcase : CaseTen (quotientImage (normalizerResidual L (radicalCore p L T))
      (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) 5) :
    Nat.card (XiQuotient (normalizerResidual L (C.map (radicalCore p L T).subtype))) = 3000 ∧
      ∀ q : ℕ, q.Prime → Odd q →
        (q ∣ Nat.card (fittingSubgroup (XiQuotient
          (normalizerResidual L (C.map (radicalCore p L T).subtype)))) ↔ q = 5) := by
  let e := radicalLocalQuotientEquiv h.local_LC
  have hc := proposition_1_2_1_four_earlier_conclusion hA36
    (source_local_quotient_sqtk h) h.local_LC.1
  have hF := fitting_card_eq e
  have h5 : 5 ∣ Nat.card (fittingSubgroup (radicalLocalImage T
      (normalizerResidual L (C.map (radicalCore p L T).subtype)))) :=
    hF ▸ source_fitting_five h hp
  have hd : Nat.card (radicalLocalImage T
      (normalizerResidual L (C.map (radicalCore p L T).subtype))) ∣ 372000 :=
    (Nat.card_congr e.toEquiv) ▸ residual_quotient_card_dvd h hcase
  obtain ⟨horder, hs⟩ := order_and_fitting_support_of_A36 hc h5 hd
  exact ⟨(Nat.card_congr e.toEquiv).trans horder, fun q hq ho => hF.symm ▸ hs q hq ho⟩

/-- The conditional residual deduction on p.513. The prime and marked
extension are supplied by the independent case-(10) deduction. The universal
A.3.6 parameter retains all of its source hypotheses and conclusions. -/
theorem residual_equality_and_fitting_support {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ D : Subgroup E,
      D.IsCComponent → A36Conclusion D)
    {p r : ℕ} {L : Subgroup G} {T : Sylow 2 G}
    {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K) (hp : p = 5)
    (hcase : CaseTen (quotientImage (normalizerResidual L (radicalCore p L T))
      (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) 5)
    (P : Sylow p (XiP p L))
    (hmark : MarkedFiveExtension (quotientImage (normalizerResidual L (radicalCore p L T)) K)
      (quotientImage ((P : Subgroup (XiP p L)).map (XiP p L).subtype) K)) :
    normalizerResidual L (radicalCore p L T) =
      normalizerResidual L (C.map (radicalCore p L T).subtype) ∧
      ∀ q : ℕ, q.Prime → Odd q →
        (q ∣ Nat.card (fittingSubgroup (XiQuotient
          (normalizerResidual L (C.map (radicalCore p L T).subtype)))) ↔ q = 5) := by
  obtain ⟨horder, hs⟩ := quotient_order_and_fitting_support hA36 h hp hcase
  exact ⟨residual_eq_of_quotient_order h P hmark horder, hs⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase.ResidualEquality
