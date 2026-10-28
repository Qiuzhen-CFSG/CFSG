module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceAlternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Data.Fintype.Shrink
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import Theory.LinearAlgebra.Hermitian.ProjectivePairTransport

/-!
# Component models from the complete corrected F source list

Every original F.6.18 row is analyzed on its actual carrier and component.
The solvable row has no component, direct products project away from the cubic
factor, and quasisimple generalized Fitting groups identify the component.
Central covers retain their actual center; graph and field extensions retain
the component supplied by the source. Only row one's trivial local cores are
returned for exclusion by the original unequal-core hypothesis.

The added dihedral PSL2 row uses its ambient field model without local S4
marks. Both square-field prime congruences give square residue nine, so the
existing fixed-action sieve applies to both. Finite-field transport to a small
universe preserves actual group equivalences, including both unitary carriers.

Source: Aschbacher--Smith F.6.18, pp.309--310, and 15.4.18, pp.1162--1163.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.FullSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {D : Type u} [Group D] [Finite D]

private theorem linearTwo_model {Q : Type*} [Group Q] {F : Type*} [Field F] [Finite F]
    (hsize : LinearModels.SourceFieldSize (Nat.card F)) (e : Q ≃* PSL(2,F)) :
    IntrinsicComponentModel Q := by
  let a : F ≃+* Shrink.{0} F := (Shrink.ringEquiv.{0,_} F).symm
  have hc : Nat.card (Shrink.{0} F) = Nat.card F := Nat.card_congr a.toEquiv.symm
  exact .linearTwo (hc.symm ▸ hsize) (e.trans (Atlas.fieldEquivPSL 2 a))

private theorem component_eq_fitting {Q : Subgroup D} (hQ : IsComponent D Q)
    (hq : IsQuasisimple (generalizedFitting D)) : Q = generalizedFitting D := by
  let := hq
  exact hQ.eq_of_le ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hq⟩
    (component_le_generalizedFitting D Q hQ)

/-- The corrected ambient dihedral row needs no local S4 marking. -/
theorem dihedral_model {Q : Subgroup D} (hQ : IsComponent D Q) {S : Sylow 2 D}
    (r : FSource.DihedralPSL2Row S) : IntrinsicComponentModel Q := by
  let e : Q ≃* D := (MulEquiv.subgroupCongr
    ((component_eq_fitting hQ r.quasisimple).trans r.component)).trans topEquiv
  exact linearTwo_model (Or.inr (Or.inl ⟨r.field.prime,r.field.degree,
    r.field.prime_isPrime,r.field.degree_pos,r.degree,r.field.card,r.congruence⟩)) (e.trans r.model)

/-- Both defining-prime congruences of the actual quadratic-field row fit the
existing square-field fixed-action sieve. -/
theorem square_field_model {Q : Subgroup D} (hQ : IsComponent D Q) {S : Sylow 2 D}
    (r : FSource.SquareFieldExtensionRow S) : IntrinsicComponentModel Q := by
  let e : Q ≃* generalizedFitting D := MulEquiv.subgroupCongr (component_eq_fitting hQ r.quasisimple)
  have hc : Nat.card r.field.Carrier = r.field.prime ^ 2 := by rw [r.field.card,r.degree]
  have hm : r.field.prime ^ 2 % 16 = 9 := by
    have hr := r.congruence
    have hmod : r.field.prime % 16 = 3 ∨ r.field.prime % 16 = 5 ∨
        r.field.prime % 16 = 11 ∨ r.field.prime % 16 = 13 := by omega
    rw [Nat.pow_mod]
    rcases hmod with h | h | h | h <;> rw [h]
  exact linearTwo_model (Or.inr (Or.inl ⟨r.field.prime,2,
    r.field.prime_isPrime,by decide,by decide,hc,Or.inr (hc ▸ hm)⟩)) (e.trans r.componentEquiv)


open BenderSuzuki.MatrixGroups

private noncomputable def shrinkHermitian {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) : HermitianForm 3 (Shrink.{0} F) where
  conj := ((Shrink.ringEquiv.{0,_} F : Shrink.{0} F ≃+* F).trans J.conj).trans (Shrink.ringEquiv.{0,_} F).symm
  conj_involutive := by
    intro x
    simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
    rw [J.conj_involutive (Shrink.ringEquiv.{0,_} F x), RingEquiv.symm_apply_apply]
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply,h,Ne.symm]
  form_nondegenerate := by simp

private theorem unitary_model {Q : Type*} [Group Q] {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hm : p % 8 = 3)
    (hF : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (he : Nonempty (Q ≃* J.specialSubgroup) ∨
      Nonempty (Q ≃* ProjectiveSpecialUnitaryMatrixGroup J)) : IntrinsicComponentModel Q := by
  let : Fact p.Prime := ⟨hp⟩
  let J' := shrinkHermitian J
  have hF' : Nat.card (Shrink.{0} F) = p ^ 2 :=
    (Nat.card_congr (Shrink.ringEquiv.{0,_} F : Shrink.{0} F ≃+* F).toEquiv).trans hF
  have hc' (x : Shrink.{0} F) : J'.conj x = x ^ p := by
    change (Shrink.ringEquiv.{0,_} F).symm (J.conj (Shrink.ringEquiv.{0,_} F x)) = x ^ p
    rw [hc,map_pow,RingEquiv.symm_apply_apply]
  have hfix : Nat.card {x : F // J.conj x = x} = p := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
      (by simpa using hF) (by simpa using hc)
  have hfix' : Nat.card {x : Shrink.{0} F // J'.conj x = x} = p := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J'.conj p 1 (by decide)
      (by simpa using hF') (by simpa using hc')
  have hs := BenderSuzuki.External.huppert_II_10_13 J' p (by omega) hF' hfix'
  rcases he with he | he
  · obtain ⟨e⟩ := he
    obtain ⟨a⟩ := J.nonempty_specialEquiv_of_card J' p hF hfix hF' hfix'
    exact .unitarySpecial J' p hp hm hF' hfix' hs (e.trans a)
  · obtain ⟨e⟩ := he
    obtain ⟨a,_,ha⟩ := HermitianForm.ProjectivePairTransport.exists_projective_pair_equiv_of_card
      J J' p hF hfix hF' hfix'
    have heq : (ProjectiveSpecialUnitaryMatrixGroup J).map a.toMonoidHom =
        ProjectiveSpecialUnitaryMatrixGroup J' := by
      ext x
      rw [mem_map_equiv]
      simpa only [a.apply_symm_apply] using (ha (a.symm x)).symm
    exact .unitaryProjective J' p hp hm hF' hfix' hs
      (e.trans ((a.subgroupMap _).trans (MulEquiv.subgroupCongr heq)))

private noncomputable def primeFieldEquiv {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hc : Nat.card F = p) : F ≃+* ZMod p := by
  let : Fintype F := Fintype.ofFinite F
  exact FiniteField.ringEquivOfCardEq (by simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)

private theorem degreeThree_model {A : Type u} [Group A] {Q : Type*} [Group Q]
    (e : Q ≃* A) {p : ℕ} (hp : p.Prime) (hm : p % 8 = 3 ∨ p % 8 = 5)
    (h : FSource.DegreeThree p A) : IntrinsicComponentModel Q := by
  let : Fact p.Prime := ⟨hp⟩
  cases h with
  | linear F hc hs f =>
    exact .linearSpecial p (by omega) (e.trans (f.trans (Atlas.fieldEquivSL 3 (primeFieldEquiv hc))))
  | projectiveLinear F hc hs f =>
    exact .linearProjective p (by omega) (e.trans (f.trans (Atlas.fieldEquivPSL 3 (primeFieldEquiv hc))))
  | unitary F J hc hf hs f =>
    exact unitary_model J hp (by omega) hc hf (Or.inl ⟨e.trans f⟩)
  | projectiveUnitary F J hc hf hs f =>
    exact unitary_model J hp (by omega) hc hf (Or.inr ⟨e.trans f⟩)

private theorem pslTwo_quasisimple (F : Type*) [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) : IsQuasisimple PSL(2,F) := by
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hF
  refine { toIsPerfect := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
           simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq (GorensteinWalter.psl2_center_eq_bot F)).trans
    QuotientGroup.quotientBot).isSimpleGroup

private theorem alternating_quasisimple {n : ℕ} (hn : 5 ≤ n) :
    IsQuasisimple (alternatingGroup (Fin n)) := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  refine { toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
           simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)))).trans
      QuotientGroup.quotientBot).isSimpleGroup

private theorem component_equiv_whole {D : Type*} [Group D] [IsQuasisimple D]
    {Q : Subgroup D} (hQ : IsComponent D Q) : Nonempty (Q ≃* D) := by
  let : IsQuasisimple (⊤ : Subgroup D) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have he := hQ.eq_of_le (show IsComponent D ⊤ from ⟨.top, inferInstance⟩) le_top
  exact ⟨(MulEquiv.subgroupCongr he).trans topEquiv⟩

private theorem symmetric_component {n : ℕ} (hn : 5 ≤ n)
    {Q : Subgroup (Equiv.Perm (Fin n))} (hQ : IsComponent _ Q) :
    Nonempty (Q ≃* alternatingGroup (Fin n)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let := alternating_quasisimple hn
  exact ⟨MulEquiv.subgroupCongr
    (hQ.eq_of_index_two_quasisimple alternatingGroup.index_eq_two)⟩

private theorem simple_component_solvable_kernel {D H : Type*} [Group D] [Group H]
    {Q : Subgroup D} (hQ : IsComponent D Q) [IsSimpleGroup Q]
    (f : D →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    IsComponent H (Q.map f) ∧ Nonempty (Q ≃* Q.map f) := by
  let := hQ.2
  have hnot : ¬ Q ≤ f.ker := by
    intro hle
    let : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable Q inferInstance
  have himage : Q.map f ≠ ⊥ := fun he => hnot ((map_eq_bot_iff Q).mp he)
  let g := f.comp Q.subtype
  have hi : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker inferInstance).resolve_right
    intro ht
    apply hnot
    intro x hx
    have hxg : (⟨x, hx⟩ : Q) ∈ g.ker := by rw [ht]; trivial
    exact hxg
  refine ⟨(hQ.map_surjective f hf).resolve_left himage, ⟨?_⟩⟩
  exact MulEquiv.ofBijective (f.subgroupMap Q)
    ⟨fun x y he => hi (congrArg Subtype.val he), f.subgroupMap_surjective Q⟩


omit [Finite D] in
private theorem component_equiv_of_simple
    {M : Type*} [Group M] [IsSimpleGroup M]
    {Q : Subgroup D} (hQ : IsComponent D Q) (e : D ≃* M) : Nonempty (Q ≃* M) := by
  let : IsSimpleGroup D := e.isSimpleGroup
  let := hQ.2
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  have htop : Q = ⊤ :=
    (hQ.1.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left
      ((nontrivial_iff_ne_bot Q).mp inferInstance)
  exact ⟨(MulEquiv.subgroupCongr htop).trans (topEquiv.trans e)⟩

omit [Finite D] in
private theorem triple_symmetric_model {Q : Subgroup D}
    (hQ : IsComponent D Q) [IsSimpleGroup Q] {n : ℕ} (hn : 5 ≤ n)
    (r : FSource.TripleSymmetric D n) : Nonempty (Q ≃* alternatingGroup (Fin n)) := by
  let := r.normal
  let f := r.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' r.kernel)
  have hf : Function.Surjective f := r.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = r.kernel := by
    ext x
    change r.quotientEquiv (QuotientGroup.mk' r.kernel x) = 1 ↔ x ∈ r.kernel
    rw [← map_one r.quotientEquiv, r.quotientEquiv.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsSolvable r.kernel := Group.isSolvable_of_isSolvable_injective
    (f := r.kernelEquiv.toMonoidHom) r.kernelEquiv.injective
  let : Group.IsSolvable f.ker := hk.symm ▸ inferInstance
  obtain ⟨him,⟨e⟩⟩ := simple_component_solvable_kernel hQ f hf
  obtain ⟨a⟩ := symmetric_component hn him
  exact ⟨e.trans a⟩

omit [Finite D] in
private theorem triple_alternating_model {Q : Subgroup D} (hQ : IsComponent D Q)
    {n : ℕ} (hn : 5 ≤ n) (r : FSource.TripleAlternating D n) : IntrinsicComponentModel Q := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  let : IsQuasisimple D := { toIsPerfect := r.perfect, simple := r.quotient.some.isSimpleGroup }
  obtain ⟨eQ⟩ := component_equiv_whole hQ
  apply IntrinsicComponentModel.tripleCover
  rw [Nat.card_congr (centerCongr eQ).toEquiv,Nat.card_congr r.center.some.toEquiv]
  simp [FSource.C]

private theorem product_model {Q : Subgroup D} (hQ : IsComponent D Q) {S : Sylow 2 D}
    (r : FSource.ProductRow S) : IntrinsicComponentModel Q := by
  have hc : Nat.card r.field.Carrier = r.field.prime := by rw [r.field.card,r.degree,pow_one]
  have hm := r.congruence
  let := pslTwo_quasisimple r.field.Carrier (by rw [hc]; omega)
  let := IsQuasisimple.of_mulEquiv r.firstEquiv.symm
  let := hQ.2
  let : Group.IsNilpotent (D ⧸ pResidual 2 D) := (isPGroup_quotient_pResidual 2).isNilpotent
  have hQR : Q ≤ r.first ⊔ r.second := by
    rw [← r.residual]
    exact le_of_isPerfect_of_solvable_quotient Q (pResidual 2 D)
  let eR : ↥(r.first ⊔ r.second) ≃* r.second × r.first := r.product.symm.trans MulEquiv.prodComm
  let : Group.IsSolvable r.second := Group.isSolvable_of_isSolvable_injective
    (f := r.secondEquiv.toMonoidHom) r.secondEquiv.injective
  obtain ⟨P,hP,⟨eP⟩⟩ := IsComponent.equiv_component_of_solvable_prod _
    ((hQ.subgroupOf hQR).map_equiv eR)
  obtain ⟨ePK⟩ := component_equiv_whole hP
  let eQ : Q ≃* r.first := ((subgroupOfEquivOfLe hQR).symm.trans
    (eR.subgroupMap (Q.subgroupOf (r.first ⊔ r.second)))).trans (eP.trans ePK)
  exact linearTwo_model (hc.symm ▸ Or.inl ⟨r.field.prime_isPrime,hm⟩) (eQ.trans r.firstEquiv)

private theorem two_solvable (hm : Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup D, ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty ((D ⧸ N) ≃* FSource.E4)) : Group.IsSolvable D := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨N,_,hN,_,_,⟨e⟩⟩ := hm
    let : Group.IsNilpotent N := hN.isPGroup.isNilpotent
    let : Group.IsSolvable (D ⧸ N) := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,inferInstance⟩

/-- Original source alternatives identify every simple component, except
for row one whose two trivial local cores are retained for its source exclusion. -/
theorem component_model_of_alternative {A B Q : Subgroup D} (hQ : IsComponent D Q)
    [IsSimpleGroup Q] {S : Sylow 2 D} (r : FSource.Alternative A B S) :
    (pCore 2 A = ⊥ ∧ pCore 2 B = ⊥) ∨ IntrinsicComponentModel Q := by
  cases r with
  | one _ hA hB _ => exact Or.inl ⟨hA,hB⟩
  | two hm =>
    let := two_solvable hm
    let := hQ.2
    exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
  | three r _ _ _ => exact Or.inr (product_model hQ r)
  | four F hd hm e ht hq _ _ _ =>
    let a : Q ≃* D := (MulEquiv.subgroupCongr ((component_eq_fitting hQ hq).trans ht)).trans topEquiv
    have hc : Nat.card F.Carrier = F.prime := by rw [F.card,hd,pow_one]
    exact Or.inr (linearTwo_model (hc.symm ▸ Or.inl ⟨F.prime_isPrime,hm⟩) (a.trans e))
  | five F hd hm _ e hq _ _ _ =>
    let a : Q ≃* generalizedFitting D := MulEquiv.subgroupCongr (component_eq_fitting hQ hq)
    have hc : Nat.card F.Carrier = F.prime := by rw [F.card,hd,pow_one]
    exact Or.inr (linearTwo_model (hc.symm ▸ Or.inl ⟨F.prime_isPrime,hm⟩) (a.trans e))
  | six hm ht hq _ _ _ =>
    rcases hm with hm | ⟨F,hd,hm,⟨e⟩⟩
    · exact Or.inr (triple_alternating_model hQ (by decide) hm)
    · let a : Q ≃* D := (MulEquiv.subgroupCongr ((component_eq_fitting hQ hq).trans ht)).trans topEquiv
      exact Or.inr (linearTwo_model (Or.inr (Or.inl ⟨F.prime,F.degree,F.prime_isPrime,
        F.degree_pos,hd,F.card,hm⟩)) (a.trans e))
  | seven hm _ _ _ _ =>
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      let := alternating_quasisimple (by decide : 5 ≤ 7)
      let := IsQuasisimple.of_mulEquiv e.symm
      obtain ⟨a⟩ := component_equiv_whole hQ
      exact Or.inr (.alternatingSeven (a.trans e))
    · exact Or.inr (triple_alternating_model hQ (by decide) hm)
  | eight hm hq _ _ _ =>
    rcases hm with hm | hm
    · obtain ⟨r⟩ := hm
      exact Or.inr (.alternatingSix (triple_symmetric_model hQ (by decide) r).some)
    · obtain ⟨r⟩ := hm
      let a : Q ≃* generalizedFitting D := MulEquiv.subgroupCongr (component_eq_fitting hQ hq)
      have hc : Nat.card r.field.Carrier = r.field.prime ^ 2 := by rw [r.field.card,r.degree]
      exact Or.inr (linearTwo_model (Or.inr (Or.inr ⟨r.field.prime,r.field.prime_isPrime,
        r.congruence,hc⟩)) (a.trans r.componentEquiv))
  | nine hm _ _ _ _ =>
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      obtain ⟨a⟩ := symmetric_component (by decide : 5 ≤ 7) (hQ.map_equiv e)
      exact Or.inr (.alternatingSeven ((e.subgroupMap Q).trans a))
    · obtain ⟨r⟩ := hm
      exact Or.inr (.alternatingSeven (triple_symmetric_model hQ (by decide) r).some)
  | ten p hp hm h ht hq _ _ _ =>
    let a : Q ≃* D := (MulEquiv.subgroupCongr ((component_eq_fitting hQ hq).trans ht)).trans topEquiv
    exact Or.inr (degreeThree_model a hp hm h)
  | eleven r hq _ _ _ =>
    exact Or.inr (degreeThree_model (MulEquiv.subgroupCongr (component_eq_fitting hQ hq))
      r.prime_isPrime r.congruence r.model.model)
  | twelve e hq _ _ _ =>
    let := Sporadic.Mathieu.m12_isSimpleGroup
    exact Or.inr (.mathieuTwelve (component_equiv_of_simple hQ e).some)
  | thirteen _ e hq _ _ _ =>
    exact Or.inr (.mathieuTwelve ((MulEquiv.subgroupCongr (component_eq_fitting hQ hq)).trans e))

/-- The corrected source alternatives retain both added rank-one cases. -/
theorem component_model_of_source_alternative {A B Q : Subgroup D} (hQ : IsComponent D Q)
    [IsSimpleGroup Q] {S : Sylow 2 D} (r : FSource.SourceAlternative A B S) :
    (pCore 2 A = ⊥ ∧ pCore 2 B = ⊥) ∨ IntrinsicComponentModel Q := by
  rcases r with hr | hr
  · rcases hr with hr | hr
    · exact component_model_of_alternative hQ hr
    · exact Or.inr (dihedral_model hQ hr.some)
  · exact Or.inr (square_field_model hQ hr.some)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.FullSource
