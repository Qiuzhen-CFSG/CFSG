module
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PResidual.NormalityLift
public import Mathlib.GroupTheory.IsPerfect

/-!
# A normal symmetric-three factor and perfect residuals

Every automorphism of S₃ is inner and its center is trivial. Thus a normal
copy of S₃ splits off by multiplication with its actual centralizer.
Perfect subgroups lie in that centralizer. Applying this in the quotient
by O₂ preserves the original normal subgroup's intrinsic quotient map.

If a perfect two-perfect subgroup is normalized by a supplement containing
the two-core, its image is normalized by both factors. Normality then lifts
through the normalizing two-group kernel. This is the group-theoretic step
in Aschbacher--Smith, The Classification of Quasithin Groups, 13.8.29(1--2),
combined manuscript of 1 March 2004, printed p.964.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThreeFactor
open NormalSymmetricThreePairRank
variable {A : Type*} [Group A]
local notation "S3" => Equiv.Perm (Fin 3)

/-- Multiplication splits off the given normal symmetric-three subgroup. -/
theorem exists_product (I : Subgroup A) [I.Normal] (eI : I ≃* S3) :
    ∃ e : centralizer (I : Set A) × S3 ≃* A,
      ∀ c s, e (c,s) = (c:A) * (eI.symm s : A) := by
  let C := centralizer (I : Set A)
  have hs : C ⊔ I = ⊤ := by
    apply top_unique
    intro a _
    let α : MulAut S3 := eI.symm.trans ((MulAut.conjNormal a).trans eI)
    obtain ⟨s,hs⟩ := symmetricThree_aut_inner α
    let i := eI.symm s
    have hi (x : I) : a * (x:A) * a⁻¹ = (i:A) * x * (i:A)⁻¹ := by
      change ((MulAut.conjNormal a x : I) : A) = ((i * x * i⁻¹ : I) : A)
      apply congrArg (fun z : I => (z:A))
      apply eI.injective
      have hh := DFunLike.congr_fun hs (eI x)
      simpa [α,i,MulAut.conj_apply] using hh
    have hc : (i:A)⁻¹ * a ∈ C := by
      apply mem_centralizer_iff.mpr
      intro x hx
      have hh := congrArg (fun z : A => (i:A)⁻¹ * z * a) (hi ⟨x,hx⟩)
      simpa [mul_assoc] using hh.symm
    have hh := (C ⊔ I).mul_mem (mem_sup_right i.property) (mem_sup_left hc)
    simpa only [mul_inv_cancel_left] using hh
  have hd : Disjoint C I := by
    apply disjoint_def.mpr
    intro x hxC hxI
    have htriv : eI ⟨x,hxI⟩ = 1 := by
      apply symmetricThree_center_trivial
      intro y
      obtain ⟨z,rfl⟩ := eI.surjective y
      have hh : z * (⟨x,hxI⟩ : I) = ⟨x,hxI⟩ * z :=
        Subtype.ext (hxC z z.property)
      simpa only [map_mul] using congrArg eI hh
    exact congrArg (fun z : I => (z:A)) (eI.injective (htriv.trans eI.map_one.symm))
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C I hd le_rfl
  refine ⟨((MulEquiv.refl C).prodCongr eI.symm).trans
    (e.trans ((MulEquiv.subgroupCongr hs).trans topEquiv)),?_⟩
  exact fun c s => he c (eI.symm s)

/-- Every homomorphism from a perfect group to the concrete S₃ is trivial. -/
theorem perfect_hom_eq_one {P : Type*} [Group P] [Group.IsPerfect P]
    (f : P →* S3) (x : P) : f x = 1 := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable S3 := Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have ht : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict x) 1)

/-- Every perfect subgroup centralizes a normal subgroup isomorphic to S₃. -/
theorem perfect_centralizes (I : Subgroup A) [I.Normal] (eI : I ≃* S3)
    (R : Subgroup A) [Group.IsPerfect R] : R ≤ centralizer (I : Set A) := by
  obtain ⟨e,he⟩ := exists_product I eI
  intro r hr
  let f := (MonoidHom.snd _ S3).comp (e.symm.toMonoidHom.comp R.subtype)
  have hh : (e.symm r).2 = 1 := perfect_hom_eq_one f ⟨r,hr⟩
  have hr' : r = ((e.symm r).1 : A) := by
    have hx := he (e.symm r).1 (e.symm r).2
    rw [e.apply_symm_apply,hh,map_one,OneMemClass.coe_one,mul_one] at hx
    exact hx
  rw [hr']
  exact (e.symm r).1.property

/-- Split off the original normal subgroup modulo the ambient two-core,
retaining its intrinsic quotient map on every representative. -/
theorem exists_core_product [Finite A]
    (I : Subgroup A) [I.Normal] (eI : (I ⧸ pCore 2 I) ≃* S3) :
    let q := QuotientGroup.mk' (pCore 2 A)
    let C := centralizer (I.map q : Set (A ⧸ pCore 2 A))
    ∃ e : C × S3 ≃* (A ⧸ pCore 2 A),
      ∀ i : I, e (1,eI (QuotientGroup.mk' (pCore 2 I) i)) = q i := by
  dsimp only
  let q := QuotientGroup.mk' (pCore 2 A)
  let J := I.map q
  let eJ := (inferInstance : I.Normal).isSubnormal.quotientCoreImageEquiv 2
  let : J.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  obtain ⟨e,he⟩ := exists_product J (eJ.symm.trans eI)
  refine ⟨e,fun i => ?_⟩
  rw [he,OneMemClass.coe_one,one_mul]
  change (((eJ.symm.trans eI).symm (eI (QuotientGroup.mk' (pCore 2 I) i)) : J) : A ⧸ pCore 2 A) = q i
  simp only [MulEquiv.symm_trans_apply, eI.symm_apply_apply]
  rfl

/-- A perfect two-residual normalized by the local supplement becomes normal
in the full group. The two-core must normalize it through that supplement. -/
theorem normal_of_symmetric_supplement [Finite A]
    (I P R : Subgroup A) [I.Normal] [Group.IsPerfect R]
    (eI : (I ⧸ pCore 2 I) ≃* S3) (hIP : I ⊔ P = ⊤)
    (hPR : P ≤ normalizer (R : Set A)) (hQP : pCore 2 A ≤ P)
    (hp : IsPPerfect 2 R) : R.Normal := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let J := I.map q
  let eJ := (inferInstance : I.Normal).isSubnormal.quotientCoreImageEquiv 2
  let : J.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect (R.map q) := Group.IsPerfect.ofSurjective
    (q.subgroupMap_surjective R)
  have hJ : J ≤ normalizer (R.map q : Set (A ⧸ pCore 2 A)) :=
    (le_centralizer_iff.mp (perfect_centralizes J (eJ.symm.trans eI) (R.map q))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hP : P.map q ≤ normalizer (R.map q : Set (A ⧸ pCore 2 A)) :=
    (map_mono hPR).trans (R.le_normalizer_map q)
  let : (R.map q).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    have hh := sup_le hJ hP
    change I.map q ⊔ P.map q ≤ _ at hh
    rw [←Subgroup.map_sup,hIP,map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  apply normal_of_map_normal_of_pPerfect q R hp
  · change IsPGroup 2 (QuotientGroup.mk' (pCore 2 A)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  · simpa only [q,QuotientGroup.ker_mk'] using hQP.trans hPR

end Theory.GroupTheory.NormalSymmetricThreeFactor
