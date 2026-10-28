module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsCoreCentralizerIndex
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.Representation.FrattiniAction
public import Theory.GroupAction.QuinticFixedIndex

/-!
# The full original Hermitian module lies in the full Tits core

Characteristic two makes the canonical action of KT/O₂(KT) on the Frattini
quotient of its whole two-core faithful. The original module has fixed index
sixteen on that core, hence fixed codimension at most four on the Frattini
quotient. Every nonidentity Tits involution moves at least ten dimensions.
The elementary image is therefore trivial, with the original kernel retained.

Source application: Aschbacher--Smith 6.1.4, printed pp.665--666, and the
five-local Tits displacement calculation in Guralnick--Malle II, Lemma 8.8.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterK.Exceptional.TitsCubicDisplacement

private theorem tits_involution_fixedCodim_ge_ten
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Tits.ParrottGroup W) (hf : Function.Injective σ)
    (t : Tits.ParrottGroup) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 ≤ fixedCodim σ (zpowers t) := by
  obtain ⟨x,k,hk,hk1,hconj⟩ := ElementaryGeometry.five_commutator_of_coverage
    Tits.InvolutionRootGeometry.binaryInvolutionCoverage t ht ht2
  have hlo := fiveKernel_fixedCodim_ge_twenty σ hf k hk hk1
  have he : fixedCodim σ (zpowers k) =
      fixedCodim σ (zpowers (t*x*t⁻¹*x⁻¹)) := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hconj
    rw [←hg]
    exact (fixedCodim_zpowers_conj σ k g).symm
  rw [he] at hlo
  have hup := fixedCodim_commutator_le_twice σ t x
  omega

private theorem elementary_le_core_of_tits_frattini_index
    {H : Type*} [Group H] [Finite H]
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (N : Subgroup (H ⧸ pCore 2 H)) [N.Normal]
    (e : N ≃* Tits.ParrottGroup)
    (hN : centralizer (N : Set (H ⧸ pCore 2 H)) = ⊥)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hi : (centralizer (A : Set H)).relIndex (pCore 2 H) ≤ 16) :
    A ≤ pCore 2 H := by
  let R := pCore 2 H
  let W := R ⧸ frattini R
  let : Fact (IsPGroup 2 R) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let q := QuotientGroup.mk' R
  let a : H →* MulAut W := (quotientAut (frattini R)).comp MulAut.conjNormal
  have hk : a.ker = R := pCore_frattini_action_kernel 2 hc
  let b := QuotientGroup.lift R a hk.ge
  have hb : Function.Injective b := (QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm
  let j := N.subtype.comp e.symm.toMonoidHom
  let d := b.comp j
  let σ := FrattiniAction.ofAutomorphismHom d
  have hσ : Function.Injective σ := by
    intro x y hxy
    apply e.symm.injective
    apply N.subtype_injective
    apply hb
    ext w
    exact congrArg (fun f : Module.End (ZMod 2) (Additive W) =>
      (f (Additive.ofMul w)).toMul) hxy
  let U := A.map q
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map q
  have hUN : U ≤ N := elementary_le_normal_tits N U e hN inferInstance
  let g : A →* Tits.ParrottGroup :=
    e.toMonoidHom.comp ((inclusion hUN).comp (q.subgroupMap A))
  have hgj (u : A) : j (g u) = q (u : H) := by
    change ((e.symm (e ((inclusion hUN) ((q.subgroupMap A) u))) : N) : H ⧸ R) = _
    rw [e.symm_apply_apply]
    rfl
  let D := g.range
  let τ := σ.comp D.subtype
  let g' := g.rangeRestrict
  let hAR : A ≤ normalizer (R : Set H) := le_normalizer_of_normal
  let := conjMulDistribMulActionOfLeNormalizer A R hAR
  let := BinaryFixedPoints.action (τ.comp g')
  let F : R →* Multiplicative (Additive W) := {
    toFun r := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (frattini R) r))
    map_one' := by change QuotientGroup.mk' (frattini R) 1 = 1; exact map_one _
    map_mul' r s := (QuotientGroup.mk' (frattini R)).map_mul r s }
  have heq (u : A) (r : R) : F (u • r) = u • F r := by
    change QuotientGroup.mk' (frattini R) (MulAut.conjNormal (u : H) r) =
      b (j (g u)) (QuotientGroup.mk' (frattini R) r)
    rw [hgj]
    exact (quotientAut_apply_mk (frattini R) (MulAut.conjNormal (u : H)) r).symm
  have hfix : (FixedPoints.subgroup A R).index ≤ 16 := by
    rw [fixedPoints_conjugation_eq_centralizer A R hAR]
    exact hi
  have hidx : BinaryFixedPoints.fixedIndex (τ.comp g') ≤ 16 :=
    (fixedPoints_index_le_of_surjective_equivariant F
      (QuotientGroup.mk'_surjective (frattini R)) heq).trans hfix
  have ht : BinaryFixedPoints.fixedIndex (τ.comp g') = BinaryFixedPoints.fixedIndex τ :=
    BinaryFixedPoints.fixedIndex_eq_of_equivariant τ g' g.rangeRestrict_surjective
      (MulEquiv.refl _) (by intros; rfl)
  rw [ht,FrattiniAction.fixedIndex_eq_two_pow_fixedCodim σ D] at hidx
  have hcod : fixedCodim σ D ≤ 4 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx
  have hD : D = ⊥ := by
    by_contra hne
    obtain ⟨t,htD,ht1⟩ := D.bot_or_exists_ne_one.resolve_left hne
    obtain ⟨u,hu⟩ := (show ∃ u, g u = t from htD)
    have hu2 : u ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (u : H) u.property)
    have ht2 : t ^ 2 = 1 := by
      rw [←hu,←map_pow,hu2,map_one]
    have hlo := tits_involution_fixedCodim_ge_ten σ hσ t ht1 ht2
    have hspace : fixedSpace σ D ≤ fixedSpace σ (zpowers t) :=
      fun _ hv z => hv ⟨z,(zpowers_le.mpr htD) z.property⟩
    have hdim := Submodule.finrank_mono hspace
    have h₁ := fixedCodim_add_finrank σ D
    have h₂ := fixedCodim_add_finrank σ (zpowers t)
    omega
  intro u hu
  have hg : g (⟨u,hu⟩ : A) = 1 :=
    mem_bot.mp (hD ▸ (show g (⟨u,hu⟩ : A) ∈ D from ⟨⟨u,hu⟩,rfl⟩))
  have hq : q u = 1 := by
    rw [←hgj ⟨u,hu⟩,hg,map_one]
  exact (QuotientGroup.eq_one_iff (N := R) (x := u)).mp hq

attribute [local instance] SL2.BinarySmall.spaceBinaryModule
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The whole original Hermitian module is contained in the whole two-core
of the actual Tits component joined with the original Sylow subgroup. -/
theorem original_hermitian_tits_module_le_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    reducedSubgroup (L ⊔ (T : Subgroup G)) ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := K ⊔ (T : Subgroup G)
  let C := K.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let q := QuotientGroup.mk' (pCore 2 J)
  let N := C.map q
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let A := B.subgroupOf J
  have hBJ : B ≤ J :=
    (h.reduced_enlargement.rankOneInput hout).reduced_le_sylow.trans le_sup_right
  have hTK := original_hermitian_sylow_normalizes_tits_component
    h hout hm hM₁ hCM₁ hK hnot hqK e
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let ec : C ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eqc := QuotientGroup.congr (pCore 2 C) (pCore 2 K) ec (pCore_map_iso 2 ec)
  let := hqK
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv eqc.symm
  have hgen : C ⊔ (P : Subgroup J) = ⊤ := by
    change K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  obtain ⟨f,_,hcN⟩ := Tits.marked_core_quotient C
    (isPGroup_quotient_of_sup_eq_top C (P : Subgroup J) P.isPGroup' hgen)
    ((coreCentralQuotientCongr ec).trans e)
  let : N.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hJM₁ : J ≤ M₁ := sup_le hK.1 hTM₁
  have hcM₁ := h.simpleQTKE.evenCharacteristic T M₁ hM₁ hTM₁
  have hfJ : generalizedFitting J = pCore 2 J :=
    generalizedFitting_eq_pCore_of_sylow_overgroup T J M₁ le_sup_right hJM₁ hcM₁
  have hcJ : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
    rw [←hfJ]
    exact centralizer_generalizedFitting_le J
  let : IsElementaryAbelian 2 B := (h.reduced_enlargement.rankOneInput hout).reduced.2.1
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.comap_of_injective J.subtype J.subtype_injective B
  have hidx : (centralizer (A : Set J)).relIndex (pCore 2 J) ≤ 16 := by
    have hmC : (centralizer (A : Set J)).map J.subtype = J ⊓ centralizer (B : Set G) := by
      rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hBJ]
    have he : (J ⊓ centralizer (B : Set G)).relIndex (J.pCoreIn 2) =
        (centralizer (B : Set G)).relIndex (J.pCoreIn 2) := by
      rw [←inf_relIndex_right (J ⊓ centralizer (B : Set G)) (J.pCoreIn 2),
        inf_right_comm,inf_eq_right.mpr (pCoreIn_le 2 J),inf_relIndex_left]
    have hh := relIndex_map_map_of_injective (centralizer (A : Set J))
      (pCore 2 J) J.subtype_injective
    rw [hmC] at hh
    rw [←hh]
    change (J ⊓ centralizer (B : Set G)).relIndex (J.pCoreIn 2) ≤ 16
    rw [he]
    exact (original_hermitian_tits_core_module_centralizer_index
      h hout hm hM₁ hCM₁ hK hnot hqK e).2.le
  have hAR := elementary_le_core_of_tits_frattini_index hcJ N f hcN A hidx
  have hh := map_mono (f := J.subtype) hAR
  rwa [map_subgroupOf_eq_of_le hBJ] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
