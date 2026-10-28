module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.ExceptionalCorank.Kernel
public import Theory.GroupTheory.Fitting.TwoCorePreimage
public import Theory.GroupTheory.Fitting.PrimeSubgroups

/-!
# The odd-extension action bound from the preceding radical calculation

Put J = KT. In the strict-component cases the proof of 11.4.1(3) supplies
R₁ ≤ O∞(J) and |O∞(J) : O₂,F(J)| ≤ 2, where O₂,F(J) is the inverse image
of F(J/O₂(J)). We retain these two earlier-source facts explicitly.

Every two-subgroup of O₂,F(J) lies in O₂(J): its image is a two-subgroup
of a nilpotent group with trivial two-core. Since K is normal in J,
[O₂(J), K] ≤ O₂(J) ∩ K ≤ O₂(K). Thus the actual action of J on K/O₂(K)
kills O₂(J). The index bound now gives rank at most one for the image of
every elementary subgroup of R₁. The final theorem applies the parent's
kernel-containment and corank-transfer theorem on the literal subgroups.

This route uses the radical calculation preceding 11.5.6, rather than a
bound on the automorphism group of an arbitrary odd-by-SL₂ extension.
Consequently it retains both the natural elementary p² kernel and every
nilpotent odd kernel in the SL₂(5) case, including higher homocyclic
exponents and extraspecial primary factors. No quotient model is replaced,
and normality is only relative to KT. The iterated TwoOddQuotient model
and the flag/component hypotheses are used by the preceding 11.4.1
producer, not asserted to follow from these elementary transfer lemmas.

Source: Aschbacher--Smith, 11.4.1(3), printed p.776 (PDF p.793), and
11.5.6(6), printed pp.780--781 (PDF pp.797--798).
The earlier-source producer is qt-d-1222-shadow-component-triangle under
qt-d-1222-shadow-components; it must retain the displayed Fitting index
as well as the radical containment. Its preceding component/embedding
input belongs to qt-d-1222-natural-relative-components. Their discharge
remains with the original source assembly, not with an arbitrary quotient
identification or the partial ClassicalRefinementCase predicate.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.OddExtension

private theorem two_intersection_fitting_le_core
    {J : Type*} [Group J] [Finite J] (A : Subgroup J) (hA : IsPGroup 2 A) :
    A ⊓ twoFittingCore J ≤ pCore 2 J := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hF : (A ⊓ twoFittingCore J).map q ≤ fittingSubgroup (J ⧸ pCore 2 J) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha.2
  have hc := IsPGroup.le_pCore_of_le_fitting ((hA.to_le inf_le_left).map q) hF
  rw [pCore_quotient_pCore_eq_bot 2] at hc
  intro a ha
  exact (QuotientGroup.eq_one_iff a).mp (mem_bot.mp (hc (mem_map_of_mem q ha)))

private theorem action_rank_of_radical_fitting_index
    {J B : Type*} [Group J] [Group B] [Finite J] [Finite B]
    (f : J →* B) (hf : pCore 2 J ≤ f.ker)
    (hi : (twoFittingCore J).relIndex (solvableRadical J) ≤ 2)
    (A : Subgroup J) [IsElementaryAbelian 2 A] (hA : A ≤ solvableRadical J) :
    Group.rank (A.map f) ≤ 1 := by
  apply (IsElementaryAbelian.rank_map_le_one_iff_card_le_twice_kernel A f).mpr
  have hidx : (twoFittingCore J).relIndex A ≤ 2 :=
    (relIndex_le_of_le_right (H := twoFittingCore J) hA
      (show ((twoFittingCore J).subgroupOf (solvableRadical J)).index ≠ 0 from
        index_ne_zero_of_finite)).trans hi
  have hc : A ⊓ twoFittingCore J ≤ A ⊓ f.ker :=
    le_inf inf_le_left ((two_intersection_fitting_le_core A
      (IsElementaryAbelian.isPGroup 2 A)).trans hf)
  have hcard := card_le_of_le hc
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup J)
    (A ⊓ twoFittingCore J) A bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left] at hprod
  nlinarith

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.OddExtension

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure

/-- The actual normalizer action of a relative overgroup kills its own two-core.
Neither K nor J is assumed normal in the ambient group. -/
theorem twoCore_le_normalizerAction_kernel
    {G : Type*} [Group G] [Finite G] (K J : Subgroup G)
    (hKJ : K ≤ J) (hn : J ≤ normalizer (K : Set G)) :
    pCore 2 J ≤ ((coreQuotientAction K).comp (inclusion hn)).ker := by
  intro r hr
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  change coreQuotientAction K (inclusion hn r) (QuotientGroup.mk' (pCore 2 K) k) = _
  rw [coreQuotientAction_apply_mk]
  change QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom (inclusion hn r) k) =
    QuotientGroup.mk' (pCore 2 K) k
  have hcomm : ⁅(r : G), (k : G)⁆ ∈ K ⊓ J.pCoreIn 2 := by
    refine ⟨?_, ?_⟩
    · exact K.mul_mem ((mem_normalizer_iff.mp (hn r.property) k).mp k.property)
        (K.inv_mem k.property)
    · let kj : J := ⟨k, hKJ k.property⟩
      have hm : ⁅r, kj⁆ ∈ pCore 2 J :=
        (commutator_le_left (pCore 2 J) ⊤) (commutator_mem_commutator hr (mem_top kj))
      exact ⟨⁅r, kj⁆, hm, rfl⟩
  obtain ⟨w, hw, he⟩ := inf_pCoreIn_le_of_le 2 hKJ hcomm
  have hm : K.normalizerMonoidHom (inclusion hn r) k * k⁻¹ ∈ pCore 2 K := by
    have hw' : w = K.normalizerMonoidHom (inclusion hn r) k * k⁻¹ := Subtype.ext he
    exact hw' ▸ hw
  have hq : QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom (inclusion hn r) k) =
      QuotientGroup.mk' (pCore 2 K) k := by
    have hz := (QuotientGroup.eq_one_iff _).mpr hm
    change QuotientGroup.mk' (pCore 2 K)
      (K.normalizerMonoidHom (inclusion hn r) k * k⁻¹) = 1 at hz
    rw [map_mul, map_inv, mul_inv_eq_one] at hz
    exact hz
  exact hq

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The literal R₁ action has elementary image rank at most one from the two
preceding radical facts used in 11.4.1(3). In particular this treats the
odd-kernel branch of 11.5.6(6) without restricting its primary factors.
`hR` and `hi` are earlier-source obligations, not conclusions proved here. -/
theorem radical_action_rank_of_preceding_radical_structure
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hR : E.R₁ ≤ (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)).map
      (E.K ⊔ (T : Subgroup G) : Subgroup G).subtype)
    (hi : (twoFittingCore (E.K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
      (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : A ≤ E.R₁) :
    Group.rank ((A.subgroupOf E.R₁).map (E.radicalCoreAction hT)) ≤ 1 := by
  let J := E.K ⊔ (T : Subgroup G)
  have hn : J ≤ normalizer (E.K : Set G) :=
    sup_le E.K.le_normalizer (hT.trans E.G₁_normalizes_K)
  have hRJ : E.R₁ ≤ J := (pCoreIn_le 2 _).trans
    (sup_le_sup_right (le_conjugateSpanBy E.L₁ E.G₁) _)
  let f : J →* MulAut (E.K ⧸ pCore 2 E.K) :=
    (coreQuotientAction E.K).comp (inclusion hn)
  have hf : pCore 2 J ≤ f.ker := twoCore_le_normalizerAction_kernel E.K J le_sup_left hn
  have hAR : A.subgroupOf J ≤ solvableRadical J := by
    intro a ha
    obtain ⟨r, hr, he⟩ := hR (hA ha)
    exact (Subtype.ext he : r = a) ▸ hr
  let : IsElementaryAbelian 2 (A.subgroupOf J) :=
    IsElementaryAbelian.subgroupOf (hA.trans hRJ)
  have hm : (A.subgroupOf E.R₁).map (inclusion hRJ) = A.subgroupOf J := by
    ext a
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro ha
      exact ⟨⟨a, hA ha⟩, ha, Subtype.ext rfl⟩
  have he : E.radicalCoreAction hT = f.comp (inclusion hRJ) := by
    ext r
    rfl
  rw [he, ← Subgroup.map_map, hm]
  exact OddExtension.action_rank_of_radical_fitting_index f hf hi _ hAR

/-- Apply the odd-extension action calculation to the actual outside-overgroup
corank in 11.5.6(6). The residual is O²(H), and the denominator is O₂(H).
The earlier 11.4.1 radical facts remain with their source producer. -/
theorem elementary_corank_of_preceding_radical_structure
    (H : Subgroup G)
    (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H) (hHG : H ≤ E.G₁)
    (hr : (pResidual 2 H).map H.subtype ≤ E.K)
    (hR : E.R₁ ≤ (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)).map
      (E.K ⊔ (T : Subgroup G) : Subgroup G).subtype)
    (hi : (twoFittingCore (E.K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
      (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : A ≤ E.R₁) :
    ChapterE.subgroupCorank A (A ⊓ H.pCoreIn 2) ≤ 1 := by
  have hT : (T : Subgroup G) ≤ E.G₁ := (le_sup_right.trans hLH).trans hHG
  exact E.elementary_corank_le_one_of_action_rank hT H hLH hHG hr A hA
    (E.radical_action_rank_of_preceding_radical_structure hT hR hi A hA)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
