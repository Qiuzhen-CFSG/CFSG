module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.ExchangedResidual
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Layer
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Residual
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.BinaryParameters

/-!
# The original exchanged closure is the quotient's generalized Fitting subgroup

Both intermediate exchanged models give the literal O^{p′}(Mc) and O^{3′}(Mc).
Construct the solvable Borel extension to fix the binary field parameter,
then discharge the Fitting prime support and Suzuki exclusion from the global
maximal-prime choice. The actual closure image is F*(Mc/O₂(Mc)). No coprime-index,
Fitting-vanishing, layer-exhaustion or Borel-existence premise remains.

The strict model comparison remains explicit and unproved; this is not the
full four-way conclusion of 14.6.14. Its comparison, full quotient recognition,
and parabolic normalizer assembly remain with qt-e-suitable-odd-normalizer.
The earlier primitive and exchanged-factor inputs belong to
qt-e-quintic-recognition and qt-e-14612-singleton. The independent p=3 exclusion
belongs to qt-e-14615-quintic-exclusion and is not used here.

Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))

include hG hempty hM hunique hmany hcard e hab hH

/-- The actual binary exchanged branch has its full residual and layer
identifications. Only the strict model comparison is still an extra input. -/
theorem source_strict_binary_closure_layer
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hne : residualClosure H Mc ≠ residual H)
    (L : Subgroup G) (hLMc : L ≤ Mc) (hL : (L.subgroupOf Mc).IsCComponent)
    (hex : ∃ s ∈ (T : Subgroup G), s ∉ normalizer (L : Set G) ∧
      (residualClosure H Mc : Set G) = (L : Set G) *
        (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G))
    {m : ℕ} (hm : 2 ≤ m) (hcong : Nat.ModEq p (2 ^ m) 1)
    (hbin : ClassicalGroup.IsPSL
      ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 (2 ^ m)) :
    ((p = 3 ∧ m = 2) ∨ (p = 5 ∧ m = 4)) ∧
      residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
      residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
      StrictClosureLayer Mc (residualClosure H Mc) := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hunique.symm ▸ Set.mem_singleton Mc
  have hsq := hG.twoLocal_sqtk hMc.1.1
  have hparam := source_binary_component_field_parameter hG T hunique hH hHMc d.prime hmax
    hprim L hL hm hbin hcong
  have hp : p.Prime := by rcases d.prime with rfl | rfl <;> decide
  have ho : Odd p := by rcases d.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hbin
  have hd : p ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    let P : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := default
    exact hcong.symm.dvd'.trans
      ((binary_psl2_sylow_normalizer_torus_dvd F (by omega : 0 < m) hF P).trans
        (normalizer (P : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))).card_subgroup_dvd_card)
  obtain ⟨hres,hcp⟩ := exchanged_binary_closure_residual_and_centralizer
    (hH.1.2.trans hHMc) hLMc hL hsq.stronglyQuasithin hex F hm hF eF p ho hd
  obtain ⟨hres3,hc3⟩ := exchanged_binary_closure_residual_and_centralizer
    (hH.1.2.trans hHMc) hLMc hL hsq.stronglyQuasithin hex F hm hF eF 3 (by decide)
    (Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide))
  have hbound := source_solvable_overgroup_prime_bound hG T hunique H hH d.prime hmax
  let K := ((residualClosure H Mc).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
  have hKlayer : K ≤ componentLayer (Mc ⧸ pCore 2 Mc) :=
    (source_strict_closure_image_in_layer hG T hempty hM hunique hmany hcard e hab
      H hH a p H0 H1 H2 hprim d hne).2
  have hfit : fittingSubgroup (Mc ⧸ pCore 2 Mc) = ⊥ :=
    fitting_quotient_eq_bot_of_closure_centralizers hHMc (primitiveResidual_isSolvable H hprim)
      hbound K hKlayer hc3 (fun hp5 => hp5 ▸ hcp)
  have hsub : (residualClosure H Mc).subgroupOf Mc = primeToResidual 3 Mc := by
    rw [hres3,subgroupOf,comap_map_eq_self_of_injective Mc.subtype_injective]
  let : ((residualClosure H Mc).subgroupOf Mc).Normal := hsub ▸ inferInstance
  let : K.Normal := (inferInstance : ((residualClosure H Mc).subgroupOf Mc).Normal).map
    (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _)
  exact ⟨hparam,hres,hres3,hfit,closure_eq_generalizedFitting_of_centralizer Mc hsq
    (source_no_suzuki_components hG T hunique hH hHMc d.prime hmax hprim)
    K hKlayer hfit hc3⟩

/-- Both exchanged intermediate models discharge the residual and layer
obligations. The model comparison and final wreath recognition remain separate. -/
theorem source_strict_exchanged_closure_layer
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hne : residualClosure H Mc ≠ residual H)
    (L : Subgroup G) (hLMc : L ≤ Mc) (hL : (L.subgroupOf Mc).IsCComponent)
    (hmodel : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L p) :
    residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
      residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
      StrictClosureLayer Mc (residualClosure H Mc) := by
  obtain ⟨hex,hbin | ⟨hp,hthree⟩⟩ := hmodel
  · obtain ⟨m,hm,_heven,hcong,hbin⟩ := hbin
    exact (source_strict_binary_closure_layer hG T hempty hM hunique hmany hcard e hab H hH a
      p H0 H1 H2 hprim d hmax hne L hLMc hL hex hm hcong hbin).2
  · subst p
    have hHMc : H ≤ Mc :=
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
        (InitialSource.centralizer_le_partner T hunique)
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hunique.symm ▸ Set.mem_singleton Mc
    have hsq := hG.twoLocal_sqtk hMc.1.1
    obtain ⟨hres,hc3⟩ := exchanged_linear_three_closure_residual_and_centralizer
      (hH.1.2.trans hHMc) hLMc hL hsq.stronglyQuasithin hex hthree
    have hbound := source_solvable_overgroup_prime_bound hG T hunique H hH d.prime hmax
    let K := ((residualClosure H Mc).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
    have hKlayer : K ≤ componentLayer (Mc ⧸ pCore 2 Mc) :=
      (source_strict_closure_image_in_layer hG T hempty hM hunique hmany hcard e hab
        H hH a 3 H0 H1 H2 hprim d hne).2
    have hfit : fittingSubgroup (Mc ⧸ pCore 2 Mc) = ⊥ :=
      fitting_quotient_eq_bot_of_closure_centralizers hHMc (primitiveResidual_isSolvable H hprim)
        hbound K hKlayer hc3 (by omega)
    have hsub : (residualClosure H Mc).subgroupOf Mc = primeToResidual 3 Mc := by
      rw [hres,subgroupOf,comap_map_eq_self_of_injective Mc.subtype_injective]
    let : ((residualClosure H Mc).subgroupOf Mc).Normal := hsub ▸ inferInstance
    let : K.Normal := (inferInstance : ((residualClosure H Mc).subgroupOf Mc).Normal).map
      (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _)
    exact ⟨hres,hres,hfit,closure_eq_generalizedFitting_of_centralizer Mc hsq
      (source_no_suzuki_components hG T hunique hH hHMc d.prime hmax hprim)
      K hKlayer hfit hc3⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
