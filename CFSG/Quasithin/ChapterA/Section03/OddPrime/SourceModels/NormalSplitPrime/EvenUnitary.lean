module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ActionBounds
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ProjectiveIndices
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms
public import Theory.SpecificGroups.SU3.BorelCoprimeFieldAction
public import Theory.SpecificGroups.SU3.BinaryCubicRankParity
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.UnitaryField
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.UnitaryMixed
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Binary

/-!
# The full cubic binary unitary branch

For the actual order-three semilinear actor, the mixed-factor calculation
forces a nontrivial field coefficient to have inner unitary factor. Its
pure coefficient actor therefore belongs to the actual action range. The
explicit fixed unitary nine then contradicts SQTK. Thus the original actor
is inner-diagonal, and index three identifies the full star action with PGU₃.
The kernel and split residual identities give the exact source alternative;
the two-core application preserves the original component and quotient maps.

The parameter is the fixed-field order q; all coefficient fields have order
q². Source: Aschbacher–Smith A.3.18, printed pp.51–53; GLS3 §2.5 and §2.7.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
open Matrix BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter

private theorem unitary_inner_le {F : Type*} [Field F] (J : HermitianForm 3 F) :
    MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ J.unitaryConjHom.range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
  exact ⟨⟨u.val, u.property.1⟩, (J.unitaryConjHom_apply _).trans
    (J.unitaryConj_special_is_inner u)⟩

private theorem unitary_action_kernel {F : Type*} [Field F] (J : HermitianForm 3 F) [CharP F 2]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hconj : ∃ t : F, J.conj t ≠ t) :
    J.unitaryConjHom.ker = (unitaryToPGU J).ker := by
  ext u
  constructor
  · intro hu
    have hh : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        Commute (ProjGenLinGroup.mk u.val) x.val := by
      intro x
      have he := congrArg (fun b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => (b x).val) hu
      rw [J.unitaryConjHom_apply] at he
      change (J.unitaryConj u x).val = x.val at he
      rw [J.unitaryConj_apply_val] at he
      exact (mul_inv_eq_iff_eq_mul).mp he
    apply Subtype.ext
    exact ProjGenLinGroup.mk_eq_one.mpr
      (J.projective_centralizer_scalar hJ hconj u.val hh)
  · intro hu
    have he : ProjGenLinGroup.mk u.val = 1 := congrArg Subtype.val hu
    change J.unitaryConjHom u = 1
    rw [J.unitaryConjHom_apply]
    ext x
    change (J.unitaryConj u x).val = x.val
    rw [J.unitaryConj_apply_val, he, one_mul, inv_one, mul_one]

private def pguEquivUnitaryAction {F : Type*} [Field F] (J : HermitianForm 3 F) [CharP F 2]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hconj : ∃ t : F, J.conj t ≠ t) :
    projectiveUnitary J ≃* J.unitaryConjHom.range :=
  (QuotientGroup.quotientKerEquivOfSurjective (unitaryToPGU J)
    (unitaryToPGU_surjective J)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (unitary_action_kernel J hJ hconj).symm).trans
        (QuotientGroup.quotientKerEquivRange J.unitaryConjHom))

private theorem unitary_cubic_mem {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (ho : Odd n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hinner : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ A)
    (hrank : primeRank 3 A ≤ 2)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (haA : a ∈ A) (ha : a ^ 3 = 1) :
    a ∈ J.unitaryConjHom.range := by
  obtain ⟨σ, hσ⟩ := EvenSemilinear.semilinear_coverage J hJ hn hF hconj a
  have hs3 := BorelCoprimeFieldAction.coefficient_pow J hJ hn hF hconj hσ ha
  have hs : σ = 1 := by
    by_contra hs
    have horder : orderOf σ = 3 := orderOf_eq_prime hs3 hs
    obtain ⟨g, he⟩ := UnitaryMixed.inner_field_of_cube_one J hJ hn ho hF hconj a σ horder hσ ha
    have hσA : fieldActorHom J hJ σ ∈ A := by
      have hh := A.mul_mem (A.inv_mem (hinner ⟨g,rfl⟩)) haA
      rwa [he,inv_mul_cancel_left] at hh
    have hb := UnitaryField.actor_rank_three J hJ hn ho hF hconj A hinner σ horder hσA
    omega
  rw [hs] at hσ
  obtain ⟨u, hu⟩ := (HasUnitarySemilinearForm.one_iff J).mp hσ
  exact ⟨u, (J.unitaryConjHom_apply u).trans hu.symm⟩

theorem ordinary_even_unitary_cubic_projective
    {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    (hrank : 1 < primeRank 3 K) (hz : Nat.Coprime 3 (Nat.card (center K)))
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ n))
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    SignedCongruence true (2 ^ n) ∧
      ClassicalGroup.IsPSU (starComponent 3 K) 3 (2 ^ n) ∧
        IsPGUThree (primeToResidual 3 (Star 3 H)) (2 ^ n) := by
  obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [← Nat.card_eq_fintype_card, pow_mul] using hF)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hF hc
  obtain ⟨e₀⟩ := FormTransport.exists_projectiveEquiv J (2 ^ n) hF hfixed
  let J₀ := FormTransport.standardForm J
  let e' := e.trans e₀
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    e'.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  let f := normalAction K e'
  have hb := hH.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hnodd : Odd n := BinaryCubicRankParity.odd_of_rank_two J (by omega) hF hc
    (by rw [central_model_rank hz e]; omega)
  have hmod : 2 ^ n % 3 = 2 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three, if_neg]
    have hh := Nat.odd_iff.mp hnodd
    omega
  have hconj : ∃ t : F, J₀.conj t ≠ t := by
    by_contra hn
    push Not at hn
    let e : F ≃ {x : F // J₀.conj x = x} :=
      { toFun := fun x => ⟨x, hn x⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he := Nat.card_congr e
    change Nat.card F = Nat.card {x : F // J.conj x = x} at he
    rw [hF, hfixed] at he
    have hpow : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
    nlinarith
  have hapow : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hcube : f a ^ 3 = 1 := by rw [← map_pow, hapow, map_one]
  have hi : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀) ≤ f.range := by
    rw [← normalAction_component_image K e']
    exact Subgroup.map_le_range f K
  have hfa : f a ∈ J₀.unitaryConjHom.range :=
    unitary_cubic_mem J₀ rfl hn hnodd hF hc f.range hi
      (normalAction_rank_le_two hz hrank hb e') (f a) ⟨a,rfl⟩ hcube
  have hdiag : f.range ≤ J₀.unitaryConjHom.range := by
    rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup, normalAction_component_image,
      MonoidHom.map_zpowers]
    exact sup_le (unitary_inner_le J₀) (zpowers_le.mpr hfa)
  have hneq : f.range ≠ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := by
    intro he
    have hh : f a ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
      he ▸ (show f a ∈ f.range from ⟨a, rfl⟩)
    have hh' := prime_dvd_of_action_power_inner hz hrank hb e' a ha haK
      (m := 1) (by simpa only [pow_one] using hh)
    norm_num at hh'
  have hs : center (ProjectiveSpecialUnitaryMatrixGroup J₀) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J₀)).Normal).eq_bot_or_eq_top
      with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative (ProjectiveSpecialUnitaryMatrixGroup J₀)
        (center_eq_top_iff.mp h)).elim
  let E₀ := pguEquivUnitaryAction J₀ rfl hconj
  have he : f.range = J₀.unitaryConjHom.range := by
    apply actionImage_eq_of_index_three _ _ _ hi hdiag hneq
    rw [← Nat.card_congr E₀.toEquiv, card_pgu_three_eq_three_mul_psu J₀ (2 ^ n) hF hc hmod]
    congr 1
    exact Nat.card_congr (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hs)).toEquiv
  let E : Star 3 H ≃* projectiveUnitary J₀ :=
    (componentActionStarEquiv hz hrank hb e').trans ((MulEquiv.subgroupCongr he).trans E₀.symm)
  refine ⟨hmod, ?_, ?_⟩
  · exact ⟨F, inferInstance, inferInstance, J₀, hF, hc,
      ⟨(componentStarQuotientEquiv hz hrank hb).symm.trans e'⟩⟩
  · exact ⟨F, inferInstance, inferInstance, J₀, hF, hc,
      ⟨((MulEquiv.subgroupCongr (star_residual_eq_top_of_split hz hrank a ha hgen)).trans
        Subgroup.topEquiv).trans E⟩⟩

/-- The full unitary alternative in the original split extension. Neither
field parity, a two-group center nor inner-diagonal membership is assumed. -/
theorem alternatives_of_even_unitary_cubic_model
    {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : 1 < primeRank 3 K)
    (hz : Nat.Coprime 3 (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) 3 (2 ^ n))
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives 3 K := by
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  let f := QuotientGroup.mk' (pCore 2 H)
  have hc : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hz' : Nat.Coprime 3 (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank 3 (twoCoreComponent K) := by
    rwa [twoCore_rank hK (by decide : Odd 3)]
  have ha' := twoCore_actor Nat.prime_three (by decide) a ha haK
  obtain ⟨hcong, hmodel, hpgl⟩ := ordinary_even_unitary_cubic_projective (twoCore_sqtk hH)
    hr' hz' hn (hm.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK)))
    (f a) ha'.1 ha'.2 (twoCore_join a hgen)
  apply Or.inr ∘ Or.inl
  refine ⟨rfl, true, 2 ^ n, hcong,
    hmodel.of_mulEquiv (starComponentEquiv 3 f (QuotientGroup.mk'_surjective _) hc K),
    Or.inl ?_⟩
  obtain ⟨F, _, _, J, hF, hconj, ⟨eF⟩⟩ := hpgl
  exact ⟨F, inferInstance, inferInstance, J, hF, hconj,
    ⟨(starResidualEquiv 3 f (QuotientGroup.mk'_surjective _) hc).trans eF⟩⟩

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
