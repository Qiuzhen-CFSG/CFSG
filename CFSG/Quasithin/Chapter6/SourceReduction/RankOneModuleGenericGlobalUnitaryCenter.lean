module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryContainment
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuterPointLocal
public import Mathlib.Algebra.CharP.Reduced
public import Theory.GroupTheory.PCoreInRestriction
/-!
# The unitary contained-core branch

The norm of the first point coordinate is a character of the actual
semidirect unitary extension. It is trivial on every two-subgroup in
characteristic two. The unitary equation then shows that these subgroups
centralize the center of the point radical. The literal parabolic maps,
solvable residuals and two-cores transport this calculation to the original
S and Q = O₂(K), preserving both amalgam orientations.

For an overcomponent with Q ≤ R = O₂(J), this gives Z(Q) = Z(R).
If J is maximal, the earlier 1.2.7 uniqueness theorem applies inside
N_G(Z(Q)). Its C-component containing K is unique, so N_G(K) normalizes J.
The proved enlarged-parabolic core identity now gives R ≤ Q. Thus the
entire nonnormal containment branch is impossible, including the degree-two
field-four extension. This uses the ambient earlier uniqueness theorem in
place of the printed Thompson-quotient step; no Thompson identity is assumed.

The companion applies the result to the literal Chapter12 pair. The proper
intersection branch, remaining maximality rows, exhaustive comparison and
ambient completion recognition still require proofs.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`),
with 1.2.7 for the maximal-overcomponent uniqueness in the center normalizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointResidual
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryContainedCenter
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "E" => UnitaryFourOuter.point F σ hσ
local notation "J" => form F σ hσ

private def normCharacter : E →* F where
  toFun g := g.val.left.val.val 0 0 * σ (g.val.left.val.val 0 0)
  map_one' := by simp
  map_mul' g h := by
    have hmul (b : SU F J) (hb : b ∈ pointParabolicSU F J) :
        (g.val.left * b).val.val 0 0 =
          g.val.left.val.val 0 0 * b.val.val 0 0 :=
      (pointScalar F J).map_mul ⟨g.val.left,g.property⟩ ⟨b,hb⟩
    change (g.val.left * UnitaryFourOuter.action F σ hσ g.val.right h.val.left).val.val 0 0 *
        σ ((g.val.left * UnitaryFourOuter.action F σ hσ g.val.right h.val.left).val.val 0 0) = _
    rcases UnitaryFourOuter.c2_cases g.val.right with hc | hc
    · simp only [hc,map_one,MulAut.one_apply,hmul _ h.property,map_mul]
      ring
    · rw [hc,UnitaryFourOuter.action_generator,
        hmul _ ((UnitaryFourOuter.matrixAut_mem_point F σ hσ _).mpr h.property)]
      change (_ * σ _) * σ (_ * σ _) = _
      rw [map_mul,hσ]
      ring

private theorem two_normCharacter (U : Subgroup E) (hU : IsPGroup 2 U)
    (g : E) (hg : g ∈ U) : normCharacter F σ hσ g = 1 := by
  obtain ⟨k,hk⟩ := hU.exists_pow_pow_eq_one ⟨g,hg⟩
  have he : (normCharacter F σ hσ g)^(2^k) = 1 := by
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one] using
      congrArg (normCharacter F σ hσ) (congrArg Subtype.val hk)
  simpa only [Nat.mul_one,pow_one] using
    (ExpChar.pow_prime_pow_mul_eq_one_iff 2 k 1 _).mp (by simpa using he)

private theorem norm_one_centralizes (g : E) (hg : normCharacter F σ hσ g = 1)
    (hnt : ∃ u, σ u ≠ u) (z : radical F σ hσ)
    (hz : z ∈ center (radical F σ hσ)) :
    Commute g.val (SemidirectProduct.inl z.val.val) := by
  obtain ⟨hx,hy⟩ := (mem_center_radical_iff F σ hσ hnt z).mp hz
  let c := coordinatesOfRadical F σ hσ z
  have hc : σ c.z = c.z := by
    have ht := c.trace_eq
    rw [show c.x = 0 from hx,show c.y = 0 from hy] at ht
    exact (eq_neg_of_add_eq_zero_right (by simpa using ht)).trans (CharTwo.neg_eq _)
  have hzmat : z.val.val.val.val = radicalMatrix F σ c :=
    congrArg (fun w : radical F σ hσ => w.val.val.val.val)
      ((radicalCoordinatesEquiv F σ hσ).apply_symm_apply z).symm
  have hfix : UnitaryFourOuter.matrixAut F σ hσ z.val.val = z.val.val := by
    apply Subtype.ext
    apply Units.ext
    change (z.val.val.val.val).map σ = z.val.val.val.val
    rw [hzmat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [radicalMatrix,hx,hy,hc,c]
  have hact : UnitaryFourOuter.action F σ hσ g.val.right z.val.val = z.val.val := by
    rcases UnitaryFourOuter.c2_cases g.val.right with hr | hr
    · simp [hr]
    · rw [hr,UnitaryFourOuter.action_generator,hfix]
  have hgcol := (mem_pointParabolicSU F J g.val.left).mp g.property
  have hu := g.val.left.property.1
  change (J).conjTranspose g.val.left.val.val * gram F * g.val.left.val.val = gram F at hu
  have row (j : Fin 4) := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 j) hu
  have hrow1 := row 1
  have hrow2 := row 2
  have hrow3 := row 3
  simp [form,gram,HermitianForm.conjTranspose,Matrix.mul_apply,Fin.sum_univ_succ,
    hgcol.1,hgcol.2.1,hgcol.2.2] at hrow1 hrow2 hrow3
  have ha : σ (g.val.left.val.val 0 0) ≠ 0 := by
    intro he
    rw [he,zero_mul] at hrow3
    exact zero_ne_one hrow3
  have h31 : g.val.left.val.val 3 1 = 0 := hrow1.resolve_left (fun he => ha (by rw [he,map_zero]))
  have h32 : g.val.left.val.val 3 2 = 0 := hrow2.resolve_left (fun he => ha (by rw [he,map_zero]))
  have h33 : g.val.left.val.val 3 3 = g.val.left.val.val 0 0 := by
    apply mul_left_cancel₀ ha
    exact hrow3.trans (by simpa [normCharacter,mul_comm] using hg.symm)
  apply SemidirectProduct.ext
  · change g.val.left * UnitaryFourOuter.action F σ hσ g.val.right z.val.val =
      z.val.val * UnitaryFourOuter.action F σ hσ 1 g.val.left
    rw [hact,map_one,MulAut.one_apply]
    apply Subtype.ext
    apply Units.ext
    change g.val.left.val.val * z.val.val.val.val = z.val.val.val.val * g.val.left.val.val
    rw [hzmat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [radicalMatrix,c,hx,hy,Matrix.mul_apply,Fin.sum_univ_succ,
        hgcol.1,hgcol.2.1,hgcol.2.2,h31,h32,h33,mul_comm,add_comm]
    all_goals ring
  · simp

private instance extensionFinite : Finite (UnitaryFourOuter.Extension F σ hσ) :=
  Finite.of_injective (fun x => (x.left,x.right))
    (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

omit [CharP F 2] in
private theorem extended_residual [Group.IsPerfect (localSU F J)] :
    solvableResidual E = UnitaryFourOuter.pointVector F σ hσ := by
  let j := UnitaryFourOuter.pointVectorEmbedding F σ hσ
  let D := solvableResidual E
  let parity : E →* UnitaryFourOuter.C2 :=
    SemidirectProduct.rightHom.comp (E).subtype
  have hzero (g : D) : g.val.val.right = 1 :=
    Abelianization.commutator_subset_ker (parity.comp D.subtype)
      Group.IsPerfect.mem_commutator
  let f : D →* pointParabolicSU F J := {
    toFun g := ⟨g.val.val.left,g.val.property⟩
    map_one' := rfl
    map_mul' a b := by
      apply Subtype.ext
      change a.val.val.left * UnitaryFourOuter.action F σ hσ a.val.val.right b.val.val.left = _
      simp only [hzero a,map_one,MulAut.one_apply]
      rfl }
  apply le_antisymm
  · intro g hg
    have hscalar : pointScalarUnits F J (f ⟨g,hg⟩) = 1 :=
      Abelianization.commutator_subset_ker ((pointScalarUnits F J).comp f)
        Group.IsPerfect.mem_commutator
    refine ⟨⟨g.val.left,?_⟩,Subtype.ext (SemidirectProduct.ext rfl (hzero ⟨g,hg⟩).symm)⟩
    have hh : (f ⟨g,hg⟩) ∈ (pointScalarUnits F J).ker := hscalar
    rwa [pointScalarUnits_ker] at hh
  · let : Group.IsPerfect (UnitaryFourOuter.pointVector F σ hσ) :=
      Group.IsPerfect.ofSurjective
        (f := (UnitaryFourOuter.pointVectorEquiv F σ hσ).toMonoidHom)
        (UnitaryFourOuter.pointVectorEquiv F σ hσ).surjective
    exact le_solvableResidual_of_isPerfect _


open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour

private theorem model_core_center (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m)
    (U : Subgroup (UnitaryFourOuter.point (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm))) (hU : IsPGroup 2 U) :
    U ≤ centralizer (centerIn ((solvableResidual
      (UnitaryFourOuter.point (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm))).pCoreIn 2) : Set _) := by
  let F := MatrixField m
  let σ := fieldConj m
  let hσ := fieldConj_involutive m hm
  let j := UnitaryFourOuter.pointVectorEmbedding F σ hσ
  let e := UnitaryFourOuter.pointVectorEquiv F σ hσ
  let : Group.IsPerfect (localSU F (form F σ hσ)) := by
    change Group.IsPerfect (PointLocal.MatrixLocal m hm)
    exact PointLocal.matrixLocal_isPerfect m hm hm'
  have hcore : (UnitaryFourOuter.pointVector F σ hσ).pCoreIn 2 =
      (pCore 2 (localSU F (form F σ hσ))).map j := by
    unfold pCoreIn
    rw [← pCore_map_iso 2 e,Subgroup.map_map]
    rfl
  have hrad : radical F σ hσ = pCore 2 (localSU F (form F σ hσ)) :=
    PointLocal.radical_eq_twoCore m hm
  rw [extended_residual F σ hσ,hcore,centerIn_eq_map_center,
    ←map_embeddedCenter _ j (UnitaryFourOuter.pointVectorEmbedding_injective F σ hσ),
    ←hrad]
  intro g hg z hz
  obtain ⟨_,⟨a,ha,rfl⟩,rfl⟩ := hz
  exact Subtype.ext
    ((norm_one_centralizes F σ hσ g (two_normCharacter F σ hσ U hU g hg)
      (PointLocal.fieldConj_nontrivial m hm) a ha).symm.eq)

private theorem extended_point_core_not_elementary
    (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m)
    {G : Type*} [Group G] [Finite G] {P K : Subgroup G}
    (hr : (solvableResidual P).map P.subtype = K)
    (he : P ≃* Extension.point m hm)
    (hK : IsElementaryAbelian 2 (pCore 2 K)) : False := by
  let M := UnitaryFourOuter.point (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
  let e : P ≃* M := he.trans (Extension.projectIso m hm).left.symm
  let c : solvableResidual P ≃* K :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hr)
  let : Group.IsPerfect (localSU (MatrixField m)
      (form (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))) := by
    change Group.IsPerfect (PointLocal.MatrixLocal m hm)
    exact PointLocal.matrixLocal_isPerfect m hm hm'
  let a : K ≃* PointLocal.MatrixLocal m hm := c.symm.trans
    (e.solvableResidualEquiv.trans ((MulEquiv.subgroupCongr
      (extended_residual (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))).trans
        (UnitaryFourOuter.pointVectorEquiv _ _ _).symm))
  let aq := (a.subgroupMap (pCore 2 K)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 a))
  let : IsElementaryAbelian 2 (pCore 2 (PointLocal.MatrixLocal m hm)) :=
    IsElementaryAbelian.of_injective aq.symm.toMonoidHom aq.symm.injective
  let b := (PointLocal.localEquiv m hm).subgroupMap (pCore 2 (PointLocal.MatrixLocal m hm))
  let bq := b.trans (MulEquiv.subgroupCongr (pCore_map_iso 2 (PointLocal.localEquiv m hm)))
  let : IsElementaryAbelian 2 (pCore 2 (PointLocal.ProjectiveLocal m hm)) :=
    IsElementaryAbelian.of_injective bq.symm.toMonoidHom bq.symm.injective
  exact PointLocal.projectiveTwoCore_commutator_ne_bot m hm
    ((commutator_eq_bot_iff _).mpr inferInstance)

private theorem two_centralizes_of_point_equiv
    {G : Type*} [Group G] [Finite G] {P K U : Subgroup G}
    (hUP : U ≤ P) (hU : IsPGroup 2 U)
    (hr : (solvableResidual P).map P.subtype = K)
    (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m) (he : P ≃* Extension.point m hm) :
    U ≤ centralizer (centerIn (K.pCoreIn 2) : Set G) := by
  let M := UnitaryFourOuter.point (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
  let e : P ≃* M := he.trans (Extension.projectIso m hm).left.symm
  have hKP : K ≤ P := hr ▸ map_subtype_le _
  have hQ : ((K.pCoreIn 2).subgroupOf P).map e.toMonoidHom =
      (solvableResidual M).pCoreIn 2 := by
    rw [←pCoreIn_subgroupOf 2 K P hKP,map_pCoreIn_of_injective 2 _ _ e.injective]
    have hK : K.subgroupOf P = solvableResidual P := by
      apply Subgroup.map_injective P.subtype_injective
      rw [map_subgroupOf_eq_of_le hKP,hr]
    rw [hK,map_solvableResidual_eq e.toMonoidHom e.surjective]
  let V := (U.subgroupOf P).map e.toMonoidHom
  have hv := model_core_center m hm hm' V (hU.comap_subtype.map e.toMonoidHom)
  have hQP : K.pCoreIn 2 ≤ P := (pCoreIn_le 2 K).trans hKP
  intro u hu z hz
  let a : P := ⟨u,hUP hu⟩
  let b : P := ⟨z,hQP hz.1⟩
  have hb : e b ∈ centerIn ((solvableResidual M).pCoreIn 2) := by
    rw [←hQ]
    constructor
    · exact mem_map_of_mem e.toMonoidHom (show b ∈ (K.pCoreIn 2).subgroupOf P from hz.1)
    · rintro _ ⟨q,hq,rfl⟩
      change e q * e b = e b * e q
      rw [←map_mul,←map_mul]
      exact congrArg e (show q*b = b*q from Subtype.ext (hz.2 q.val hq))
  have ha : e a ∈ V := mem_map_of_mem e.toMonoidHom hu
  have heq : e (b*a) = e (a*b) := by simpa only [map_mul] using hv ha _ hb
  exact congrArg Subtype.val (e.injective heq)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryContainedCenter

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm

/-- The original source two-group centralizes the original core center
in either orientation of the degree-two unitary extension. -/
theorem Preparation.unitaryExtension_sourceS_centralizes_right_center
    (hext : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    sourceS L H ≤ centralizer (centerIn ((residual H).pCoreIn 2) : Set G) := by
  have hf := d.unitary_core_structure h hH.1.1.2 hp m hm (.inr hext)
  rcases hext with hh | hh <;> obtain ⟨e⟩ := hh
  · exact (UnitaryContainedCenter.extended_point_core_not_elementary m hm hf.1
      (d.parabolic_residuals h hH.1.1.2 hp 0) e.left hf.2.2.1).elim
  · exact UnitaryContainedCenter.two_centralizes_of_point_equiv
      (le_sup_right.trans le_sup_left) (pCore_isPGroup.map _)
      (d.parabolic_residuals h hH.1.1.2 hp 1) m hm hf.1 e.right

include he
/-- In the containment branch the two centers are equal, with the same
literal ambient embeddings. -/
theorem Preparation.unitary_contained_overcomponent_center_eq
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J)
    (hQR : (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    centerIn (J.pCoreIn 2) = centerIn ((residual H).pCoreIn 2) := by
  apply le_antisymm
  · simpa only [centerIn_eq_map_center] using
      d.unitary_contained_overcomponent_center_le h hH hp m hm he hJ hKJ hQR
  · rcases he with ho | hext
    · have heq := le_antisymm
        (d.unitary_ordinary_overcomponent_core_le h hH hp m hm ho hJ hKJ) hQR
      exact (congrArg centerIn heq).ge
    · have hRS := (d.unitary_overcomponent_core_intersection h hH hp m hm (.inr hext) hJ hKJ).1
      have hc := d.unitaryExtension_sourceS_centralizes_right_center h hH hp m hm hext
      exact le_inf (inf_le_left.trans hQR) ((le_centralizer_iff.mp hc).trans (centralizer_le hRS))

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]

private theorem maximal_normalizes_of_two_local
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J Z : Subgroup G}
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (hZ : Z ≠ ⊥) (hpZ : IsPGroup 2 Z)
    (hNZ : normalizer (K : Set G) ≤ normalizer (Z : Set G))
    (hn : J ≤ normalizer (Z : Set G)) :
    normalizer (K : Set G) ≤ normalizer (J : Set G) := by
  let N := normalizer (Z : Set G)
  have hKN : K ≤ N := K.le_normalizer.trans hNZ
  have hTN : (T : Subgroup G) ≤ N := hTK.trans hNZ
  have hN : N ∈ Chapter1.H G :=
    Chapter1.mem_H_of_isTwoLocal ⟨Z,hZ,hpZ,rfl⟩
  have hj := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hJ).component
    N ⟨hN,sup_le hn hTN⟩
  have hnot : ¬ Group.IsSolvable (K.subgroupOf N) := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable hK
      (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hKN).toMonoidHom)
        (subgroupOfEquivOfLe hKN).surjective)
  have hh := cComponent_le_normalizer_of_unique hj (comap_mono hKJ)
    (fun D hD hKD => Chapter1.Section02.IndexTwo.cComponent_unique_over_nonsolvable
      hnot hD hj hKD (comap_mono hKJ))
    (S := (normalizer (K : Set G)).subgroupOf N)
    (by
      change (normalizer (K : Set G)).subgroupOf N ≤ normalizer (K.subgroupOf N : Set N)
      rw [←subgroupOf_normalizer_eq hKN])
  rw [←subgroupOf_normalizer_eq hn] at hh
  intro x hx
  exact hh (show (⟨x,hNZ hx⟩ : N) ∈ (normalizer (K : Set G)).subgroupOf N from hx)

section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- A maximal unitary overcomponent whose core contains Q has exactly Q
as its core. Center equality permits the earlier 1.2.7 uniqueness theorem
to be applied in N_G(Z(Q)); the enlarged-parabolic core then gives R ≤ Q. -/
theorem Preparation.unitary_maximal_contained_core_eq
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H ≤ J)
    (hQR : (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    J.pCoreIn 2 = (residual H).pCoreIn 2 := by
  let K := residual H
  let Q := K.pCoreIn 2
  let Z := centerIn Q
  let P := ChapterF.Source.parabolic ![L,K] (sourceS L H) 1
  let Y := P ⊔ (T : Subgroup G)
  have hc := d.unitary_core_structure h hH.1.1.2 hp m hm he
  have hZcard : Nat.card Z = 2^m := by
    rw [show Z = (center Q).map Q.subtype from centerIn_eq_map_center Q,
      Nat.card_congr ((center Q).equivMapOfInjective Q.subtype Q.subtype_injective).symm.toEquiv]
    let e := (pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective
    exact (Nat.card_congr (centerCongr e).symm.toEquiv).trans hc.2.2.2.2.2.1
  have hZ : Z ≠ ⊥ := by
    intro hz
    have hc1 : Nat.card Z = 1 := by rw [hz]; simp
    have hh : 1 < 2^m := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hpZ : IsPGroup 2 Z := (isPGroup_pCoreIn 2 K).to_le inf_le_left
  have hNZ : normalizer (K : Set G) ≤ normalizer (Z : Set G) := by
    rw [show Z = (center Q).map Q.subtype from centerIn_eq_map_center Q]
    exact (normalizer_le_normalizer_characteristic_image K (pCore 2 K)).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
  have hz := d.unitary_contained_overcomponent_center_eq h hH hp m hm he hJ.1 hKJ hQR
  have hnZ : J ≤ normalizer (Z : Set G) := by
    change J ≤ normalizer (centerIn Q : Set G)
    rw [←hz,centerIn_eq_map_center]
    exact J.le_normalizer.trans
      ((normalizer_le_normalizer_characteristic_image J (pCore 2 J)).trans
        (normalizer_le_normalizer_characteristic_image (J.pCoreIn 2) (center (J.pCoreIn 2))))
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  have hK := residual_binary_mem_local hH.1.1 hp hf.1 hf.2.2.2.2
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hNJ := maximal_normalizes_of_two_local h.qtke hK hTK hJ hKJ hZ hpZ hNZ hnZ
  have hPK : P ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show K ≤ P from le_sup_left.trans le_sup_left)).mp
        ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  have hRY : J.pCoreIn 2 ≤ Y :=
    (d.unitary_overcomponent_core_intersection h hH hp m hm he hJ.1 hKJ).1.trans
      (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hnR : Y ≤ normalizer (J.pCoreIn 2 : Set G) :=
    ((sup_le hPK hTK).trans hNJ).trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hcore : Y.pCoreIn 2 = Q := d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp
    (he.elim (.unitary m hm) (.unitaryExtension m hm)) 1
  exact le_antisymm
    ((le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) hRY hnR).trans_eq hcore) hQR

/-- The entire contained-core branch of 5.2.8 is excluded, including the
field-four degree-two extension. A nonnormal maximal overcomponent must
have proper intersection with the original core. -/
theorem Preparation.unitary_nonnormal_core_not_le
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H ≤ J)
    (hnorm : ¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G)) :
    ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2 := by
  intro hQR
  apply hnorm
  rw [←d.unitary_maximal_contained_core_eq h hH hp m hm he hJ hKJ hQR]
  exact J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
