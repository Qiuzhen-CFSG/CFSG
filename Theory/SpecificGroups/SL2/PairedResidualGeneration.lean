module
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration
/-!
# One residual conjugator generating two independent SL₂ factors

A Sylow subgroup of a direct product is the product of its projections.
Choose a residual conjugator in each SL₂ factor by the root-generation
calculation. Their pair belongs to the residual of the product, and the two
conjugate product Sylows generate the entire product. This includes F₂;
there is no assumption that the product is perfect or equals its residual.
Source: Aschbacher–Smith B.6.10 and E.2.3, printed pp.117 and216–217.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
private theorem prod_sup_prod {G H : Type*} [Group G] [Group H]
    (A B : Subgroup G) (C D : Subgroup H) :
    A.prod C ⊔ B.prod D = (A ⊔ B).prod (C ⊔ D) := by
  apply le_antisymm (sup_le (prod_mono le_sup_left le_sup_left)
    (prod_mono le_sup_right le_sup_right))
  rw [prod_le_iff,Subgroup.map_sup,Subgroup.map_sup]
  constructor
  · apply sup_le
    · rintro _ ⟨a,ha,rfl⟩
      exact mem_sup_left ⟨ha,C.one_mem⟩
    · rintro _ ⟨b,hb,rfl⟩
      exact mem_sup_right ⟨hb,D.one_mem⟩
  · apply sup_le
    · rintro _ ⟨c,hc,rfl⟩
      exact mem_sup_left ⟨A.one_mem,hc⟩
    · rintro _ ⟨d,hd,rfl⟩
      exact mem_sup_right ⟨B.one_mem,hd⟩

private theorem prod_map_conj {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) (g : G) (h : H) :
    (A.prod B).map (MulAut.conj (g,h)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).prod (B.map (MulAut.conj h).toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a.1,ha.1,rfl⟩,⟨a.2,ha.2,rfl⟩⟩
  · rintro ⟨⟨a,ha,he⟩,⟨b,hb,hf⟩⟩
    exact ⟨(a,b),⟨ha,hb⟩,Prod.ext he hf⟩

theorem exists_residual_conjugate_product_sylows
    (P Q : Sylow 2 (SL(2,F))) : ∃ g ∈ pResidual 2 (SL(2,F) × SL(2,F)),
    (P : Subgroup (SL(2,F))).prod (Q : Subgroup (SL(2,F))) ⊔
      ((P : Subgroup (SL(2,F))).prod (Q : Subgroup (SL(2,F)))).map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨a,ha,hP⟩ := exists_residual_conjugate_sylow_image_sup_eq_top P
    (MonoidHom.id (SL(2,F))) Function.surjective_id
  obtain ⟨b,hb,hQ⟩ := exists_residual_conjugate_sylow_image_sup_eq_top Q
    (MonoidHom.id (SL(2,F))) Function.surjective_id
  simp only [Subgroup.map_id] at hP hQ
  have hfa : (a,1) ∈ pResidual 2 (SL(2,F) × SL(2,F)) :=
    map_pResidual_le 2 (MonoidHom.inl _ _) (mem_map_of_mem _ ha)
  have hfb : (1,b) ∈ pResidual 2 (SL(2,F) × SL(2,F)) :=
    map_pResidual_le 2 (MonoidHom.inr _ _) (mem_map_of_mem _ hb)
  refine ⟨(a,b),?_,?_⟩
  · simpa only [Prod.mk_mul_mk,mul_one,one_mul] using
      (pResidual 2 (SL(2,F) × SL(2,F))).mul_mem hfa hfb
  · rw [prod_map_conj,prod_sup_prod,hP,hQ,top_prod_top]

omit [CharP F 2] in
private theorem sylow_prod_projection (R : Sylow 2 (SL(2,F) × SL(2,F))) :
    (R : Subgroup _) =
      ((R : Subgroup _).map (MonoidHom.fst (SL(2,F)) (SL(2,F)))).prod
      ((R : Subgroup _).map (MonoidHom.snd (SL(2,F)) (SL(2,F)))) := by
  let P := R.mapSurjective (f := MonoidHom.fst (SL(2,F)) (SL(2,F)))
    (fun a => ⟨(a,1),rfl⟩)
  let Q := R.mapSurjective (f := MonoidHom.snd (SL(2,F)) (SL(2,F)))
    (fun a => ⟨(1,a),rfl⟩)
  have hp : IsPGroup 2 ((P : Subgroup (SL(2,F))).prod (Q : Subgroup (SL(2,F)))) := by
    obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
    obtain ⟨m,hm⟩ := Q.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := n+m)
    rw [Nat.card_congr ((P : Subgroup (SL(2,F))).prodEquiv (Q : Subgroup (SL(2,F)))).toEquiv,
      Nat.card_prod,hn,hm,pow_add]
  exact (R.is_maximal' hp (le_prod_iff.mpr ⟨le_rfl,le_rfl⟩)).symm

theorem exists_residual_conjugate_paired_sylow
    (R : Sylow 2 (SL(2,F) × SL(2,F))) :
    ∃ g ∈ pResidual 2 (SL(2,F) × SL(2,F)),
      (R : Subgroup _) ⊔ (R : Subgroup _).map (MulAut.conj g).toMonoidHom = ⊤ := by
  let P := R.mapSurjective (f := MonoidHom.fst (SL(2,F)) (SL(2,F)))
    (fun a => ⟨(a,1),rfl⟩)
  let Q := R.mapSurjective (f := MonoidHom.snd (SL(2,F)) (SL(2,F)))
    (fun a => ⟨(1,a),rfl⟩)
  rw [sylow_prod_projection]
  exact exists_residual_conjugate_product_sylows P Q
end Matrix.SpecialLinearGroup
