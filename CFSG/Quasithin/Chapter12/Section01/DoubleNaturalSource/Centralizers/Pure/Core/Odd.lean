module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Action
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Point
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Kernels
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# The odd core of a pure-point centralizer

Transport H.9's two commutator identities through the literal normalizer
quotient to O²(C_L(w)). The moved subgroup is elementary abelian and perfect
under this residual, so A.1.26 makes it centralize O(C_G(w)). Its centralizer
is C_G(W), which lies in M. The odd core therefore lies in C_M(w); inheritance
of characteristic two inside M then forces it to be trivial.

This proves the odd-core step of 12.1.6 from the original chosen-module inputs
and the permitted nonsingular centralizers. It uses neither ambient pure-point
Sylow control nor dimension-four weak closure. Component exclusion remains
with the assembly owner `qt-d-double-natural-pure-fusion`.
Source: Aschbacher--Smith, 12.1.6, printed p.791, using H.9.1 and A.1.26.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
namespace SourceModel
variable (S : B.SourceModel)
open Representation.BinaryOffender

private theorem pointResidual_action_range (w : componentOrbit V (T : Subgroup G)) :
    (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w))).range =
      S.setup.residual (Additive.ofMul w) := by
  rw [← S.pointResidual_image w]
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨l,hl,he⟩ := x.property
    refine ⟨l,hl,?_⟩
    change B.actionProjection (inclusion L.le_normalizer l) =
      B.actionProjection (inclusion (B.pointResidual_le_normalizer w) x)
    congr 1
    exact Subtype.ext he
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,mem_map_of_mem _ hl⟩,rfl⟩

private theorem pointResidual_subspace_commutator
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G))
    (A : Submodule (ZMod 2) (Additive (componentOrbit V (T : Subgroup G)))) :
    (binarySubgroup (subspaceCommutator S.setup.representation A
      (S.setup.residual (Additive.ofMul w)))).map (componentOrbit V (T : Subgroup G)).subtype =
      ⁅(binarySubgroup A).map (componentOrbit V (T : Subgroup G)).subtype, B.pointResidual w⁆ := by
  let W := componentOrbit V (T : Subgroup G)
  let P := (binarySubgroup A).map W.subtype
  have hP : P ≤ W := map_subtype_le _
  have hn : B.pointResidual w ≤ normalizer (W : Set G) :=
    hNM.symm ▸ B.pointResidual_le_normalizer w
  have hm := commutator_image_eq S.setup.representation W P (B.pointResidual w) hn hP
    (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w)))
    (MonoidHom.id W) (fun x v => by
      rw [S.representation_eq]
      rfl) A (by
        rw [Subgroup.map_id]
        exact (comap_map_eq_self_of_injective W.subtype_injective (binarySubgroup A)).symm)
  rw [Subgroup.map_id,S.pointResidual_action_range w] at hm
  rw [← hm, map_subgroupOf_eq_of_le]
  exact (commutator_mono hP le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hn)

/-- The two literal summands have exactly the source commutators with O²(C_L(w)). -/
theorem pure_residual_commutators
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    ⁅B.naturalSummand, B.pointResidual w⁆ = B.naturalSummand ∧
      ⁅B.dualSummand, B.pointResidual w⁆ = S.pureDualHyperplane w hp := by
  have hn : (binarySubgroup S.setup.natural).map
      (componentOrbit V (T : Subgroup G)).subtype = B.naturalSummand := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (B.mem_naturalSummand v).mpr ((S.natural_marking v).mp hv)
    · intro hx
      let v : componentOrbit V (T : Subgroup G) := ⟨x,B.naturalSummand_le hx⟩
      exact ⟨v,(S.natural_marking v).mpr ((B.mem_naturalSummand v).mp hx),rfl⟩
  have hd : (binarySubgroup S.setup.dual).map
      (componentOrbit V (T : Subgroup G)).subtype = B.dualSummand := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (B.mem_dualSummand v).mpr ((S.dual_marking v).mp hv)
    · intro hx
      let v : componentOrbit V (T : Subgroup G) := ⟨x,B.dualSummand_le hx⟩
      exact ⟨v,(S.dual_marking v).mpr ((B.mem_dualSummand v).mp hx),rfl⟩
  have hc := S.setup.pure_commutators ⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ hw
  constructor
  · have he := S.pointResidual_subspace_commutator hNM w S.setup.natural
    rw [hc.1,hn] at he
    exact he.symm
  · have he := S.pointResidual_subspace_commutator hNM w S.setup.dual
    rw [hc.2,hd] at he
    exact he.symm

/-- The literal moved subgroup centralizes the odd core of the full point
centralizer, by the strongly quasithin form of A.1.26. -/
theorem pure_moving_centralizes_oddCore
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hsqt : IsStronglyQuasithin (B.pointCentralizer w)) :
    B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤
      centralizer ((pPrimeCore 2 (B.pointCentralizer w)).map (B.pointCentralizer w).subtype : Set G) := by
  let W := componentOrbit V (T : Subgroup G)
  let H := B.pointCentralizer w
  let X := B.pointResidual w
  let U := ⁅W,X⁆
  have hWH : W ≤ H := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : W) w))
  have hXH : X ≤ H := (B.pointResidual_le w).trans inf_le_right
  have hn : X ≤ normalizer (W : Set G) := hNM.symm ▸ B.pointResidual_le_normalizer w
  have hUW : U ≤ W := le_normalizer_iff_commutator_le_left.mp hn
  have hUH : U ≤ H := hUW.trans hWH
  have hXp : IsPPerfect 2 X := by
    dsimp [X]
    exact (isPPerfect_embedded_pResidual 2 (L ⊓ B.pointCentralizer w)).of_surjective
      (MulEquiv.subgroupCongr (B.pointResidual_eq w).symm).toMonoidHom
      (MulEquiv.subgroupCongr (B.pointResidual_eq w).symm).surjective
  have hXHp : IsPPerfect 2 (X.subgroupOf H) := hXp.of_surjective
    (subgroupOfEquivOfLe hXH).symm.toMonoidHom (subgroupOfEquivOfLe hXH).symm.surjective
  let i : U.subgroupOf H →* W :=
    (inclusion hUW).comp ((subgroupOfEquivOfLe hUH).toMonoidHom)
  let : IsElementaryAbelian 2 (U.subgroupOf H) :=
    IsElementaryAbelian.of_injective i ((inclusion_injective hUW).comp
      (subgroupOfEquivOfLe hUH).injective)
  have hcomm : ⁅U.subgroupOf H,X.subgroupOf H⁆ = U.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hXH]
    exact commutator_isPPerfect_idempotent X W hXp (IsElementaryAbelian.isPGroup 2 W) hn
  have hc := ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hsqt
    (X.subgroupOf H) (U.subgroupOf H) hXHp hcomm
  have hm := congrArg (map H.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hm
  have hu : B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ U := by
    obtain ⟨h₁,h₂⟩ := S.pure_residual_commutators hNM w hw hp
    exact sup_le (h₁.symm.le.trans (commutator_mono B.naturalSummand_le le_rfl))
      (h₂.symm.le.trans (commutator_mono B.dualSummand_le le_rfl))
  exact hu.trans (commutator_eq_bot_iff_le_centralizer.mp hm)

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The odd core vanishes at every natural point, using only the original
chosen-module hypotheses and the permitted nonsingular centralizer input. -/
theorem doubleNatural_pure_oddCore_eq_bot_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
        (B.coordinates w).toAdd.2 = 0 →
        pPrimeCore 2 (centralizer ({(w : G)} : Set G)) = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S hns w hw hp
  let H := B.pointCentralizer w
  let M := normalizer (L : Set G)
  let R := pPrimeCore 2 H
  have hn := D.doubledOrbit_normalizer_eq h B.orbit_eq
  have hw2 : orderOf (w : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
    (fun he => hw (Subtype.ext he))
  have hsqt : IsStronglyQuasithin H :=
    (h.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hw2)).stronglyQuasithin
  have hRC : R.map H.subtype ≤
      centralizer ((B.naturalSummand ⊔ S.pureDualHyperplane w hp : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (S.pure_moving_centralizes_oddCore hn w hw hp hsqt)
  have hRM : R.map H.subtype ≤ M := by
    rw [S.pure_moving_centralizer hn hns (S.summandCentralizers hn) w hw hp] at hRC
    exact hRC.trans ((Subgroup.centralizer_le_normalizer _).trans_eq hn)
  have hMc : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (h.simpleQTKE.evenCharacteristic T M (D.doubledNormalizer_unique h).1
      D.sylow_normalizes_component)
  have hwM : zpowers (w : G) ≤ M := zpowers_le.mpr
    (D.sylow_normalizes_component ((D.doubledOrbit_E322 h).le_sylow w.property))
  have hMHC : M ⊓ H ∈ Chapter1.He G := by
    have hc := pCoreIn_selfCentralizing_centralizer hMc
      (IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using hw2)) hwM
    change (M ⊓ H) ⊓ centralizer ((M ⊓ H).pCoreIn 2 : Set G) ≤ (M ⊓ H).pCoreIn 2
    simpa only [H,DoubledBranch.pointCentralizer,zpowers_eq_closure,centralizer_closure] using hc
  let K := M.subgroupOf H
  have hK : HasCharacteristicTwo K := by
    have hMH : HasCharacteristicTwo (M ⊓ H : Subgroup G) := Chapter1.mem_He_iff.mp hMHC
    have hh := hMH.of_equiv
      (subgroupOfEquivOfLe (H := M ⊓ H) inf_le_right).symm
    exact hh.of_equiv (MulEquiv.subgroupCongr (inf_subgroupOf_right M H))
  have hcop : Nat.Coprime 2 (Nat.card (R.subgroupOf K)) := by
    rw [← inf_subgroupOf_right R K,
      Nat.card_congr (subgroupOfEquivOfLe (H := R ⊓ K) inf_le_right).toEquiv]
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le inf_le_left)
  have hle : R.subgroupOf K ≤ pPrimeCore 2 K := le_sSup ⟨inferInstance,hcop⟩
  rw [pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hK] at hle
  apply le_bot_iff.mp
  intro r hr
  have hrK : r ∈ K := hRM (mem_map_of_mem _ hr)
  have he := mem_bot.mp (hle (show (⟨r,hrK⟩ : K) ∈ R.subgroupOf K from hr))
  exact mem_bot.mpr (congrArg Subtype.val he)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
