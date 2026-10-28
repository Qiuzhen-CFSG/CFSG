module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Center
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates

/-!
# Both elementary parabolic radicals in symplectic four-space

The point radical is the kernel of the genuine point quotient action, mapped
into Sp₄(F). Its matrices give fixed space point × plane on the paired action,
with codimension 5n and rank 3n. The two radicals are exactly the two elementary
wings in the standard Sylow coordinates; their intersection is its center.
The square formula and the subgroup-union lemma place every elementary
subgroup of this Sylow in one of these wings.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389. Placement in a conjugate of the center, or the complementary
5n bound for arbitrary elementary subgroups, requires further geometry.
-/

@[expose] public section

open scoped Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable def pointRadical : Subgroup (Sp F) :=
  (Theory.SpecificGroups.SymplecticFour.pointRadical (F := F)).map pointLocal.subtype

lemma mem_pointRadical_iff (g : Sp F) : g ∈ pointRadical ↔
    ∃ u v z : F, (pointRadicalElement u v z).val = g := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨_,_,_,congrArg Subtype.val (pointRadical_eq_element x hx).symm⟩
  · rintro ⟨u,v,z,rfl⟩
    exact ⟨pointRadicalElement u v z,pointRadicalElement_mem u v z,rfl⟩

lemma pointRadicalElement_eq_coordinate (u v z : F) :
    (pointRadicalElement u v z).val = (element v z u 0).val := by
  apply Subtype.ext
  change pointRadicalMatrix u v z = (element v z u 0).val.val
  rw [element_matrix]
  simp only [pointRadicalMatrix,mul_zero,add_zero]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma pointRadical_eq_wing : pointRadical (F := F) =
    (wing false).map (unipotent (F := F)).subtype := by
  ext g
  rw [mem_pointRadical_iff]
  constructor
  · rintro ⟨u,v,z,rfl⟩
    exact ⟨element v z u 0,(element_mem_wing _ _ _ _ _).mpr rfl,
      (pointRadicalElement_eq_coordinate u v z).symm⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    have hv : v = 0 := (element_mem_wing false b u w v).mp hx
    subst v
    exact ⟨w,b,u,pointRadicalElement_eq_coordinate w b u⟩

lemma pointRadical_fixedSpace : fixedSpace (graphPair (F := F)) pointRadical =
    ((point F).prod (plane F)).restrictScalars (ZMod 2) := by
  have h4 : rootElement 4 (1:F) ∈ pointRadical := by
    exact (mem_pointRadical_iff _).mpr ⟨1,0,0,by
      apply Subtype.ext
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [pointRadicalElement,pointRadicalMatrix,rootElement,rootMatrix,
          Matrix.fromBlocks,Matrix.single]⟩
  have h6 : rootElement 6 (1:F) ∈ pointRadical := by
    exact (mem_pointRadical_iff _).mpr ⟨0,1,0,by
      apply Subtype.ext
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [pointRadicalElement,pointRadicalMatrix,rootElement,rootMatrix,
          Matrix.fromBlocks,Matrix.single,CharTwo.neg_eq]⟩
  ext v
  constructor
  · intro hv
    have h4v := (root_fixed_iff 4 (one_ne_zero : (1:F) ≠ 0) v).mp (hv ⟨_,h4⟩)
    have h6v := (root_fixed_iff 6 (one_ne_zero : (1:F) ≠ 0) v).mp (hv ⟨_,h6⟩)
    simp only [rootCoordinates, funext_iff, Fin.forall_fin_succ,
      Matrix.cons_val_zero, Pi.zero_apply] at h4v h6v
    change v.1 ∈ point F ∧ v.2 ∈ plane F
    simp only [mem_point_iff,mem_plane,Fin.forall_fin_two]
    tauto
  · intro hv g
    change v.1 ∈ point F ∧ v.2 ∈ plane F at hv
    obtain ⟨hxb,hxcd⟩ := (mem_point_iff _).mp hv.1
    have hxc := hxcd 0
    have hxd := hxcd 1
    have hyc := hv.2 0
    have hyd := hv.2 1
    obtain ⟨u,w,z,hg⟩ := (mem_pointRadical_iff g.val).mp g.property
    change pair graphAut g.val v = v
    rw [← hg]
    change (symplecticNatural 2 _ v.1,symplecticNatural 2 (graphAut _) v.2) = v
    rw [graphAut_apply]
    simp [Prod.ext_iff,funext_iff,Sum.forall,Fin.forall_fin_two,
      symplecticNatural_apply,pointRadicalElement,pointRadicalMatrix,graphEnd,
      graphMatrix,minor,first,second,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
      Fin.sum_univ_two,fromBlocks,one_apply,hxb,hxc,hxd,hyc,hyd]

lemma pointRadical_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n) :
    fixedCodim (graphPair (F := F)) pointRadical = 5*n := by
  have hdim := fixedCodim_add_finrank (graphPair (F := F)) pointRadical
  rw [pointRadical_fixedSpace,finrank_space hF] at hdim
  have hf : Module.finrank (ZMod 2)
      (((point F).prod (plane F)).restrictScalars (ZMod 2)) = 3*n := by
    rw [← Module.finrank_mul_finrank (ZMod 2) F,coefficient_finrank hF]
    have he : ((point F).prod (plane F)) ≃ₗ[F] (point F × plane F) := {
      toFun v := (⟨v.val.1,v.property.1⟩,⟨v.val.2,v.property.2⟩)
      invFun v := ⟨(v.1.val,v.2.val),⟨v.1.property,v.2.property⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    rw [(((point F).prod (plane F)).restrictScalarsEquiv (ZMod 2)).finrank_eq,
      he.finrank_eq,Module.finrank_prod,finrank_point,finrank_plane]
    omega
  rw [hf] at hdim
  omega

lemma card_pointRadical : Nat.card (pointRadical (F := F)) = Nat.card F^3 := by
  have he := (wing (F := F) false).equivMapOfInjective
    (unipotent (F := F)).subtype Subtype.val_injective
  rw [pointRadical_eq_wing, ← Nat.card_congr he.toEquiv,card_wing]

lemma rank_pointRadical {n : ℕ} (hF : Nat.card F = 2^n) :
    rank (pointRadical (F := F)) = 3*n := by
  rw [Representation.BinaryOffender.rank,card_pointRadical,hF,← pow_mul,
    Nat.log_pow (by decide : 1 < 2)]
  omega

lemma pointRadical_elementary : IsElementaryAbelian 2 (pointRadical (F := F)) := by
  rw [pointRadical_eq_wing]
  let _ := wing_elementary (F := F) false
  exact IsElementaryAbelian.map_subtype

/-- Square-one elements of the standard Sylow lie in the union of its two wings. -/
lemma square_one_mem_wing (g : unipotent (F := F)) (hg : g^2 = 1) :
    g ∈ wing false ∨ g ∈ wing true := by
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
  rw [element_square,theta, ← element_zero,element_eq_iff] at hg
  have h := mul_eq_zero.mp hg.2.2.1
  simpa only [element_mem_wing, Bool.false_eq_true, ↓reduceIte, or_comm] using h

/-- Every elementary subgroup of the standard Sylow lies in one whole wing. -/
lemma elementary_le_wing (A : Subgroup (unipotent (F := F)))
    [IsElementaryAbelian 2 A] : A ≤ wing false ∨ A ≤ wing true := by
  apply SubgroupClass.subset_union.mp
  intro g hg
  exact square_one_mem_wing g (elemPow_eq_one_of_isElementaryAbelian g hg)


lemma planeRadical_eq_wing : planeRadical (F := F) =
    (wing true).map (unipotent (F := F)).subtype := by
  ext g
  rw [mem_planeRadical_iff]
  constructor
  · rintro ⟨B,rfl⟩
    refine ⟨element 0 (B.val 0 0) (B.val 1 0) (B.val 1 1),
      (element_mem_wing _ _ _ _ _).mpr rfl, ?_⟩
    apply Subtype.ext
    change (element 0 (B.val 0 0) (B.val 1 0) (B.val 1 1)).val.val =
      fromBlocks 1 B.val 0 1
    rw [element_matrix]
    have hs : B.val 0 1 = B.val 1 0 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) B.property
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.fromBlocks,Matrix.one_apply,hs]
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    have hb : b = 0 := (element_mem_wing true b u w v).mp hx
    subst b
    let B : Plane.symmetricMatrices F := ⟨!![u,w;w,v], by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl⟩
    refine ⟨B,?_⟩
    apply Subtype.ext
    change fromBlocks 1 B.val 0 1 = (element 0 u w v).val.val
    rw [element_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [B,Matrix.fromBlocks,Matrix.one_apply]

lemma sylowCenter_eq_radical_inf : sylowCenter (F := F) =
    pointRadical ⊓ planeRadical := by
  have hc : Subgroup.center (unipotent (F := F)) = wing false ⊓ wing true := by
    ext x
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    simp only [mem_center_iff_coordinates,Subgroup.mem_inf,element_mem_wing,
      Bool.false_eq_true,↓reduceIte,and_comm]
  rw [sylowCenter,hc,pointRadical_eq_wing,planeRadical_eq_wing]
  exact Subgroup.map_inf _ _ _ (unipotent (F := F)).subtype_injective

end SymplecticConjugatePair
