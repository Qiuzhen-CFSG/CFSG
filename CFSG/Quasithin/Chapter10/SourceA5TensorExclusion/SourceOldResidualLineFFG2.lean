module

public import Theory.SpecificGroups.G2.SolvableSylowNormalizer
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.G2CartanExclusion
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFImage

/-!
# The G₂(4) Cartan row in the original nonzero-core line argument

The actual Cartan and Sylow subgroup generate a solvable group. Its
conjugation image on the normal G₂(4) component contains the marked inner
Sylow. Cubic innerness and solvable Sylow control preserve that Sylow,
whose Borel normalizer preserves each proper local parabolic residual.
The final theorem applies this to the literal images under actionMk W,
retaining the original Sylow restriction and local-component marking.

Only the pure standard-Sylow placement lemma is reused from
G2CartanExclusion; none of its later Cartan-normalization hypotheses is
assumed. The source owner supplies solvability of the original Cartan--Sylow
join and uses original generation and properness to exclude this image.
Source: Aschbacher--Smith 9.3.1, printed pp.732--733.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Atlas.G2 Atlas.G2.LieParabolicSetup

namespace CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
open ChapterA.Section03
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The normalizer of a marked Sylow preserves either proper local residual. -/
theorem g2_sylow_normalizer_normalizes_local (hF : Nat.card F = 4)
    (S : Sylow 2 (Model F)) (B : Subgroup (Model F))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤) :
    normalizer (S : Set (Model F)) ≤ normalizer (B : Set (Model F)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) S (sylow (F := F))
  let e := MulAut.conj g
  have hSU : (S : Subgroup (Model F)).map e.toMonoidHom = unipotent := by
    rw [←sylow_coe,←hg,Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
    rfl
  have heS : S.mapSurjective (f := e.toMonoidHom) e.surjective = sylow := by
    apply Sylow.ext
    exact hSU
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have heB : B.map e.toMonoidHom ∈ localCComponents (sylow (F := F)) := by
    rw [←heS]
    exact Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom
  have heP : B.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hp
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [ht,map_top_of_surjective _ e.surjective]
  have hplace := source_g2_local_at_standard_sylow hF _ heB heP
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  change (normalizer ((S : Subgroup (Model F)) : Set (Model F))).map e.toMonoidHom ≤
    (normalizer (B : Set (Model F))).map e.toMonoidHom
  rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq,hSU,
    SylowNormalizer.normalizer_unipotent]
  rcases hplace with he | he
  · rw [he]
    exact borel_normalizes_local₁
  · rw [he]
    exact borel_le_normalizer_local₂

/-- Cubic automorphisms in the actual solvable Sylow join preserve the local subgroup. -/
theorem g2_cubic_local_invariant (hF : Nat.card F = 4)
    (S : Sylow 2 (Model F)) (B : Subgroup (Model F))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (A : Subgroup (MulAut (Model F))) (hA : IsPGroup 3 A)
    (hsol : Group.IsSolvable (A ⊔ (S : Subgroup (Model F)).map MulAut.conj :
      Subgroup (MulAut (Model F)))) :
    ∀ a ∈ A, B.map a.toMonoidHom = B := by
  intro a ha
  obtain ⟨g,hg⟩ := Atlas.G2.four_cubic_automorphisms_inner hF A hA ha
  have hs := Atlas.G2.four_cubic_solvable_join_preserves_sylow hF S A hA hsol a ha
  rw [←hg] at hs ⊢
  exact mem_normalizer_iff_map_conj_eq.mp
    (g2_sylow_normalizer_normalizes_local hF S B hB hp (mem_normalizer_iff_map_conj_eq.mpr hs))

end CFSG.Quasithin.Chapter10.SourceOldResidualLineFF

namespace CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
open ChapterA.Section03
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A solvable Cartan--Sylow join normalizes the old local subgroup in a normal G₂ component. -/
theorem g2_cartan_normalizes_local_in_normal_component {X : Type*} [Group X] [Finite X]
    (J : Subgroup X) [J.Normal] (A P : Subgroup X) (hA : IsPGroup 3 A)
    (hsol : Group.IsSolvable (A ⊔ P : Subgroup X))
    (S : Sylow 2 J) (hSP : (S : Subgroup J) ≤ P.subgroupOf J)
    (B : Subgroup J) (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (e : J ≃* Model F) (hF : Nat.card F = 4) :
    A ≤ normalizer (B.map J.subtype : Set X) := by
  let f : X →* MulAut (Model F) := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let A' := A.map f
  let B' := B.map e.toMonoidHom
  have hinner (j : J) : f j = MulAut.conj (e j) := by
    apply MulEquiv.ext
    intro z
    change e (MulAut.conjNormal (j : X) (e.symm z)) = _
    change e (j * e.symm z * j⁻¹) = _
    simp only [map_mul,map_inv,e.apply_symm_apply,MulAut.conj_apply]
  let : Group.IsSolvable (A ⊔ P : Subgroup X) := hsol
  let D := (A ⊔ P).map f
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (f := f.subgroupMap (A ⊔ P)) (f.subgroupMap_surjective _)
  have hle : A' ⊔ (S' : Subgroup (Model F)).map MulAut.conj ≤ D := by
    refine sup_le (map_mono le_sup_left) ?_
    rintro x ⟨s,⟨j,hj,rfl⟩,rfl⟩
    change MulAut.conj (e j) ∈ D
    rw [←hinner j]
    exact mem_map_of_mem f ((le_sup_right : P ≤ A ⊔ P) (hSP hj))
  have hsol' : Group.IsSolvable
      (A' ⊔ (S' : Subgroup (Model F)).map MulAut.conj : Subgroup (MulAut (Model F))) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hB' : B' ∈ localCComponents S' :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom
  have hp' : B' ≠ ⊤ := by
    intro ht
    apply hp
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact ht
  apply le_normalizer_iff.mpr
  intro x hx b hb
  obtain ⟨j,hj,rfl⟩ := hb
  have he := g2_cubic_local_invariant hF S' B' hB' hp' A' (hA.map f) hsol' (f x)
    (mem_map_of_mem f hx)
  refine ⟨MulAut.conjNormal x j,?_,rfl⟩
  apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
  have hc : e (MulAut.conjNormal x j) = f x (e j) := by
    change _ = e (MulAut.conjNormal x (e.symm (e j)))
    rw [e.symm_apply_apply]
  change e (MulAut.conjNormal x j) ∈ B'
  rw [hc]
  exact he ▸ mem_map_of_mem (f x).toMonoidHom (mem_map_of_mem e.toMonoidHom hj)

end CFSG.Quasithin.Chapter10.SourceOldResidualLineFF

namespace CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
open ChapterA.Section03 Stellmacher ChapterB.InternalThompsonAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The literal action quotient of the original Omega orbit preserves the old residual image in the G₂(4) row. -/
theorem g2_original_image_normalized {X : Type*} [Group X] [Finite X]
    (J K W : Subgroup X) [J.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (P : Sylow 2 X) (hKJ : K ≤ J) (A : Subgroup X) (hA : IsPGroup 3 A)
    (hsol : Group.IsSolvable (A ⊔ (P : Subgroup X) : Subgroup X))
    (R : Sylow 2 J) (hR : (R : Subgroup J) = (P : Subgroup X).subgroupOf J)
    (hB : ((K.map (actionMk W)).subgroupOf (J.map (actionMk W))) ∈
      localCComponents (R.mapSurjective ((actionMk W).subgroupMap_surjective J)))
    (hp : ((K.map (actionMk W)).subgroupOf (J.map (actionMk W))) ≠ ⊤)
    (e : (J.map (actionMk W)) ≃* Model F) (hF : Nat.card F = 4) :
    A.map (actionMk W) ≤ normalizer (K.map (actionMk W) : Set (ActionQuotient W)) := by
  let q := actionMk W
  let I := J.map q
  let S := R.mapSurjective (q.subgroupMap_surjective J)
  let : I.Normal := (inferInstance : J.Normal).map q (QuotientGroup.mk'_surjective _)
  have hSP : (S : Subgroup I) ≤ ((P : Subgroup X).map q).subgroupOf I := by
    rintro s ⟨j,hj,rfl⟩
    change q (j : X) ∈ (P : Subgroup X).map q
    have hjP : j ∈ (P : Subgroup X).subgroupOf J := hR ▸ hj
    exact mem_map_of_mem q hjP
  let : Group.IsSolvable (A ⊔ (P : Subgroup X) : Subgroup X) := hsol
  have hsol' : Group.IsSolvable (A.map q ⊔ (P : Subgroup X).map q :
      Subgroup (ActionQuotient W)) := by
    rw [←Subgroup.map_sup]
    exact Group.isSolvable_of_surjective
      (f := q.subgroupMap (A ⊔ (P : Subgroup X))) (q.subgroupMap_surjective _)
  have hn := g2_cartan_normalizes_local_in_normal_component I (A.map q) ((P : Subgroup X).map q) (hA.map q)
    hsol' S hSP ((K.map q).subgroupOf I) hB hp e hF
  rwa [map_subgroupOf_eq_of_le (map_mono hKJ)] at hn

end CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
