module
public import Theory.GroupTheory.PushingUp.BaumannBinary.ResidualKernel
public import Glauberman.PushingUpSL2DegreeBinary
public import Theory.GroupTheory.RankOneCentralChiefPassage
public import Theory.GroupTheory.SylowElementaryCenterLifting
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# The full Baumann commutator at binary degree greater than one

The residual-centralized kernel constructed in `ResidualKernel` gives the
actual Niles Main Hypothesis quotient, with the same field and quotient
marking. The proved characteristic-two intersection argument makes its
Sylow subgroup have class at most two and elementary center. Characteristic
Sylow exclusion lifts both facts through the kernel. Hence [O₂(G),P] lies
in Ω₁(Z(P)). Normal generation by P extends this bound to [O₂(G),G] inside
the original normal closure V.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 5.5(a),
Theorems 6.9 and 7.2, pp.51,58,60–62; DGS85, *Groups and Graphs*, (6.3),
printed p.120. The degree-one commutator assertion is separate. The literal
DGS (6.4–6.5) application is in `BaumannApplication.Commutator`.
-/

public section
open Subgroup Theory.GroupTheory
open NilesRankOneKernel
open scoped MatrixGroups IsMulCommutative
namespace Theory.GroupTheory.BaumannBinary
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Niles's Main Hypothesis bounds lift through the constructed kernel;
there is no additional automorphism or class-bound premise. -/
theorem sylow_class_two_and_elementary_center (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    (P : Subgroup G).lowerCentralSeries 2 = ⊥ ∧
      omegaCenterIn (P : Subgroup G) = centerIn (P : Subgroup G) := by
  obtain ⟨α,hR⟩ := exists_residual_central_kernel P hc hP q hq hk hn hF
  let N := (invariantNormalKernel (P : Subgroup G) α).map (P : Subgroup G).subtype
  let π := QuotientGroup.mk' N
  let T := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have hNQ : N ≤ pCore 2 G := le_sSup ⟨inferInstance,P.isPGroup'.to_le (map_subtype_le _)⟩
  have hQS : pCore 2 G ≤ (P : Subgroup G) := pCore_isPGroup.le_sylow_of_normal P
  have hu : Order.HasUniqueMaximalOver (P : Subgroup G) ⊤ :=
    hasUniqueMaximalOver_of_surjective q hq (hk ▸ hQS)
      (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2 (P.mapSurjective hq))
  have hf := generalizedFitting_eq_pCore_of_selfCentralizing 2 hc
  obtain ⟨hfN,huN,β,hβ⟩ := invariantKernel_quotient_structure P hu hf α hR
  let e : (G ⧸ pCore 2 G) ≃* SL(2,F) := QuotientGroup.liftEquiv _ hq hk.symm
  let eN := (pCoreQuotientEquivOfKernel N hNQ).trans e
  have hclass := (Glauberman.original_sl2_class_two eN hn hF T β huN hfN hβ).1
  have hRker : pResidual 2 G ≤ centralizer (π.ker : Set G) := by
    simpa only [π,QuotientGroup.ker_mk'] using hR
  have hclassP := lowerCentralSeries_eq_bot_of_image P hP π hRker 2 hclass
  have hclass' : (P : Subgroup G).lowerCentralSeries 2 = ⊥ := by
    rw [←top_subtype_lowerCentralSeries,hclassP,Subgroup.map_bot]
  obtain ⟨g,_,_,_,hnum⟩ := Glauberman.original_sl2_numerical_pair eN hn hF T β hfN hβ
  exact ⟨hclass',omegaCenterIn_eq_centerIn_of_image P hP π hRker hnum.omegaCenters_eq_centers.1⟩

/-- The full core commutator, with the entire group as actor. -/
theorem core_commutator_le_centerClosure (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    ⁅pCore 2 G,(⊤ : Subgroup G)⁆ ≤ centerClosure (P : Subgroup G) := by
  obtain ⟨hclass,hcenter⟩ := sylow_class_two_and_elementary_center P hc hP q hq hk hn hF
  have hcomm : ⁅(P : Subgroup G),(P : Subgroup G)⁆ ≤ centerIn (P : Subgroup G) := by
    apply le_inf (commutator_le_self _ )
    apply commutator_eq_bot_iff_le_centralizer.mp
    simpa only [Subgroup.lowerCentralSeries_succ,Subgroup.lowerCentralSeries_zero] using hclass
  have hlocal : ⁅pCore 2 G,(P : Subgroup G)⁆ ≤ centerClosure (P : Subgroup G) :=
    ((commutator_mono (pCore_isPGroup.le_sylow_of_normal P) le_rfl).trans hcomm).trans
      (hcenter ▸ (show omegaCenterIn (P : Subgroup G) ≤ centerClosure (P : Subgroup G) from
        le_normalClosure))
  have hclosed := commutator_normalClosure_le_of_normal (pCore 2 G) (P : Subgroup G)
    (centerClosure (P : Subgroup G)) hlocal
  have htop : normalClosure ((P : Subgroup G) : Set G) = ⊤ := by
    obtain ⟨g,_,hgen,_⟩ := Matrix.SpecialLinearGroup.exists_residual_generating_sylow_pair q hq hk P
    apply top_unique
    rw [←hgen]
    apply sup_le le_normalClosure
    rintro _ ⟨x,hx,rfl⟩
    exact (inferInstance : (normalClosure ((P : Subgroup G) : Set G)).Normal).conj_mem x
      (le_normalClosure hx) g
  rwa [htop] at hclosed

end Theory.GroupTheory.BaumannBinary
