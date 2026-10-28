module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.CenterBounds
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings

/-!
# Elementary subgroup placement and the strict paired codimension bound

An elementary subgroup of Sp₄(F) is conjugate into one of the two elementary
wings of the standard Sylow subgroup. In the plane radical, consider the
pairs of diagonal entries of its symmetric shear matrices. Two independent
pairs force the common fixed space on the natural-plus-graph module to be
exactly plane × point, of binary codimension 5n. If all pairs are dependent,
a square root in F and an explicit SL₂ Levi matrix simultaneously conjugate
the shears into the actual Sylow center.

The exceptional graph automorphism exchanges the radicals. Swapping the
summands and applying Frobenius to one summand is a binary linear equivalence
that preserves the paired fixed codimension. Thus the same placement holds
in the point radical, and Sylow conjugacy gives it for every elementary
subgroup. The radical order bound gives rank at most 3n; the central exclusion
then proves rank(B) + 1 < fixedCodim(B). Mapping through the actual commutator
inclusion proves the same inequality for the derived action, including over
the binary field without identifying the full group with its derived group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed p.389, the native-group step in the F−1 exclusion.
-/

@[expose] public section

open scoped Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph

namespace SymplecticConjugatePair
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

private lemma independent_eq_zero {a c d f x y : F}
    (h : a*f-c*d ≠ 0) (h1 : a*x+c*y = 0) (h2 : d*x+f*y = 0) : x = 0 ∧ y = 0 := by
  have hx : (a*f-c*d)*x = 0 := by linear_combination f*h1-c*h2
  have hy : (a*f-c*d)*y = 0 := by linear_combination a*h2-d*h1
  exact ⟨(mul_eq_zero.mp hx).resolve_left h, (mul_eq_zero.mp hy).resolve_left h⟩

lemma shear_fixed_iff (B : Plane.symmetricMatrices F) (v : Space F) :
    graphPair (Plane.shearSp B) v = v ↔
      (B.val 0 0 * v.1 (.inr 0) + B.val 1 0 * v.1 (.inr 1) = 0 ∧
       B.val 1 0 * v.1 (.inr 0) + B.val 1 1 * v.1 (.inr 1) = 0) ∧
      (B.val 1 1 * v.2 (.inl 1) +
        (B.val 0 0 * B.val 1 1 + (B.val 1 0)^2) * v.2 (.inr 0) +
        B.val 0 0 * v.2 (.inr 1) = 0 ∧
       B.val 0 0 * v.2 (.inr 0) = 0 ∧ B.val 1 1 * v.2 (.inr 0) = 0) := by
  have hs : B.val 0 1 = B.val 1 0 := B.property.apply 1 0
  change (symplecticNatural 2 _ v.1, symplecticNatural 2 (graphAut _) v.2) = v ↔ _
  simp [Prod.ext_iff, funext_iff, Sum.forall, Fin.forall_fin_two,
    symplecticNatural_apply, Plane.shearSp, graphAut_apply, graphEnd,
    graphMatrix, minor, first, second, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks, one_apply, hs,
    pow_two, add_assoc, and_assoc]

lemma independent_shears_fixed {B C : Plane.symmetricMatrices F}
    (hind : B.val 0 0*C.val 1 1-B.val 1 1*C.val 0 0 ≠ 0)
    {v : Space F} (hB : graphPair (Plane.shearSp B) v = v)
    (hC : graphPair (Plane.shearSp C) v = v) :
    v.1 ∈ plane F ∧ v.2 ∈ point F := by
  obtain ⟨⟨hb1,hb2⟩,hb3,hb4,hb5⟩ := (shear_fixed_iff B v).mp hB
  obtain ⟨⟨hc1,hc2⟩,hc3,hc4,hc5⟩ := (shear_fixed_iff C v).mp hC
  have he (D : Plane.symmetricMatrices F) (h1 : D.val 0 0*v.1 (.inr 0)+D.val 1 0*v.1 (.inr 1)=0)
      (h2 : D.val 1 0*v.1 (.inr 0)+D.val 1 1*v.1 (.inr 1)=0) :
      D.val 0 0*(v.1 (.inr 0))^2+D.val 1 1*(v.1 (.inr 1))^2=0 := by
    have hh : D.val 0 0*(v.1 (.inr 0))^2-D.val 1 1*(v.1 (.inr 1))^2=0 := by
      linear_combination v.1 (.inr 0)*h1-v.1 (.inr 1)*h2
    simpa only [sub_eq_add_neg,CharTwo.neg_eq] using hh
  obtain ⟨hx,hy⟩ := independent_eq_zero hind (he B hb1 hb2) (he C hc1 hc2)
  have hz : v.2 (.inr 0) = 0 := by
    by_cases h0 : B.val 0 0 = 0
    · have h1 : B.val 1 1 ≠ 0 := by intro h1; simp [h0,h1] at hind
      exact (mul_eq_zero.mp hb5).resolve_left h1
    · exact (mul_eq_zero.mp hb4).resolve_left h0
  simp only [hz,mul_zero,add_zero,zero_add] at hb3 hc3
  have hind' : B.val 1 1*C.val 0 0-B.val 0 0*C.val 1 1 ≠ 0 := by
    rwa [← neg_sub,neg_ne_zero]
  obtain ⟨hu,hw⟩ := independent_eq_zero hind' hb3 hc3
  refine ⟨?_, (mem_point_iff _).mpr ⟨hu,?_⟩⟩
  · intro i
    fin_cases i
    · exact (sq_eq_zero_iff).mp hx
    · exact (sq_eq_zero_iff).mp hy
  · intro i
    fin_cases i
    · exact hz
    · exact hw

lemma independent_shears_fixedSpace {A : Subgroup (Sp F)} (hA : A ≤ planeRadical)
    {B C : Plane.symmetricMatrices F}
    (hB : Plane.shearSp B ∈ A) (hC : Plane.shearSp C ∈ A)
    (hind : B.val 0 0*C.val 1 1-B.val 1 1*C.val 0 0 ≠ 0) :
    fixedSpace (graphPair (F := F)) A =
      ((plane F).prod (point F)).restrictScalars (ZMod 2) := by
  apply le_antisymm
  · intro v hv
    exact independent_shears_fixed hind (hv ⟨_,hB⟩) (hv ⟨_,hC⟩)
  · rw [← planeRadical_fixedSpace]
    intro v hv g
    exact hv ⟨g.val,hA g.property⟩

lemma independent_shears_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    {A : Subgroup (Sp F)} (hA : A ≤ planeRadical)
    {B C : Plane.symmetricMatrices F}
    (hB : Plane.shearSp B ∈ A) (hC : Plane.shearSp C ∈ A)
    (hind : B.val 0 0*C.val 1 1-B.val 1 1*C.val 0 0 ≠ 0) :
    fixedCodim (graphPair (F := F)) A = 5*n := by
  unfold fixedCodim
  rw [independent_shears_fixedSpace hA hB hC hind, ← planeRadical_fixedSpace]
  exact planeRadical_fixedCodim hF

lemma shear_mem_sylowCenter (B : Plane.symmetricMatrices F) (h : B.val 1 1 = 0) :
    Plane.shearSp B ∈ sylowCenter := by
  apply (mem_sylowCenter_iff _).mpr
  refine ⟨B.val 0 0, B.val 1 0, ?_⟩
  apply Subtype.ext
  rw [central_matrix]
  change fromBlocks 1 !![B.val 0 0,B.val 1 0; B.val 1 0,0] 0 1 = fromBlocks 1 B.val 0 1
  congr 1
  have hs : B.val 0 1 = B.val 1 0 := B.property.apply 1 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h,hs]

lemma conjugate_levi_shear (A : SpecialLinearGroup (Fin 2) F) (B : Plane.symmetricMatrices F) :
    (MulAut.conj (Plane.leviSp A)) (Plane.shearSp B) = Plane.shearSp (Plane.congruence A B) := by
  have h := congrArg Subtype.val (Plane.conjugate_shear (Plane.levi A) B)
  rw [Plane.quotientMap_levi] at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv,
    Plane.levi, Plane.shear, MulAut.conj_apply] using h

lemma dependent_shears_conjugate_central {A : Subgroup (Sp F)} (hA : A ≤ planeRadical)
    (hdep : ∀ B C : Plane.symmetricMatrices F, Plane.shearSp B ∈ A →
      Plane.shearSp C ∈ A → B.val 0 0*C.val 1 1-B.val 1 1*C.val 0 0 = 0) :
    ∃ g : Sp F, A.map (MulAut.conj g).toMonoidHom ≤ sylowCenter := by
  classical
  by_cases hz : ∀ B : Plane.symmetricMatrices F, Plane.shearSp B ∈ A → B.val 1 1 = 0
  · refine ⟨1,?_⟩
    rintro _ ⟨g,hg,rfl⟩
    obtain ⟨B,rfl⟩ := (mem_planeRadical_iff _).mp (hA hg)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one]
      using shear_mem_sylowCenter B (hz B hg)
  · push Not at hz
    obtain ⟨B,hB,hb⟩ := hz
    obtain ⟨t,ht⟩ := (frobeniusEquiv F 2).surjective (B.val 0 0 / B.val 1 1)
    have ht' : t^2 = B.val 0 0 / B.val 1 1 := ht
    let M : SpecialLinearGroup (Fin 2) F := ⟨!![0,-1;1,t], by simp [det_fin_two]⟩
    refine ⟨Plane.leviSp M,?_⟩
    rintro _ ⟨g,hg,rfl⟩
    obtain ⟨C,rfl⟩ := (mem_planeRadical_iff _).mp (hA hg)
    change (MulAut.conj (Plane.leviSp M)) (Plane.shearSp C) ∈ sylowCenter
    rw [conjugate_levi_shear]
    apply shear_mem_sylowCenter
    have hc := hdep B C hB hg
    have he : C.val 0 0 + t^2*C.val 1 1 = 0 := by
      rw [ht']
      apply (mul_right_inj' hb).mp
      field_simp
      have hh : B.val 0 0*C.val 1 1 = B.val 1 1*C.val 0 0 := sub_eq_zero.mp hc
      rw [hh]
      simp [mul_comm, CharTwo.add_self_eq_zero]
    have hs : C.val 0 1 = C.val 1 0 := C.property.apply 1 0
    change (M.val * C.val * M.valᵀ) 1 1 = 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, transpose_apply, M,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, hs]
    calc
      _ = C.val 0 0 + t^2*C.val 1 1 := by
        ring_nf
        simp [CharTwo.two_eq_zero, mul_comm]
      _ = 0 := he

private noncomputable def frobeniusBinary : F ≃ₗ[ZMod 2] F :=
  LinearEquiv.ofBijective
    ((frobeniusEquiv F 2).toRingHom.toAddMonoidHom.toZModLinearMap 2)
    (frobeniusEquiv F 2).bijective

private noncomputable def graphSwap : Space F ≃ₗ[ZMod 2] Space F :=
  (LinearEquiv.prodComm (ZMod 2) (Vector F) (Vector F)).trans
    ((LinearEquiv.refl (ZMod 2) (Vector F)).prodCongr
      (LinearEquiv.piCongrRight (fun _ => frobeniusBinary (F := F))))

private lemma graphSwap_equivariant (g : Sp F) (v : Space F) :
    graphSwap (graphPair g v) = graphPair (graphAut g) (graphSwap v) := by
  have he : graphAut (graphAut g) =
      Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.fieldAutomorphism
        (frobeniusEquiv F 2) g := by
    exact DFunLike.congr_fun graphEnd_square g
  apply Prod.ext
  · rfl
  · ext i
    change (frobeniusEquiv F 2) ((g.val *ᵥ v.1) i) =
      ((graphAut (graphAut g)).val *ᵥ (fun j => (frobeniusEquiv F 2) (v.1 j))) i
    rw [he]
    change (frobeniusEquiv F 2) (∑ j, g.val i j*v.1 j) =
      ∑ j, (frobeniusEquiv F 2) (g.val i j)*(frobeniusEquiv F 2) (v.1 j)
    simp only [map_sum,map_mul]

lemma fixedCodim_map_graph (A : Subgroup (Sp F)) :
    fixedCodim graphPair (A.map (graphAut (F := F)).toMonoidHom) =
      fixedCodim graphPair A := by
  exact (fixedCodim_map_equivariant (graphPair (F := F)) (graphPair (F := F))
    (graphAut (F := F)).toMonoidHom (graphSwap (F := F))
    (graphSwap_equivariant (F := F)) A).symm

lemma graphAut_pointRadicalElement (u v z : F) :
    graphAut (pointRadicalElement u v z).val =
      Plane.shearSp ⟨!![u^2,z+u*v;z+u*v,v^2], by
        ext i j; fin_cases i <;> fin_cases j <;> rfl⟩ := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [graphAut_apply, graphEnd, graphMatrix, minor, first, second,
      Plane.shearSp, pointRadicalElement, pointRadicalMatrix, fromBlocks, pow_two, mul_comm, add_comm]

lemma graphAut_map_pointRadical_le : pointRadical.map (graphAut (F := F)).toMonoidHom ≤
    planeRadical := by
  rintro _ ⟨g,hg,rfl⟩
  obtain ⟨u,v,z,rfl⟩ := (mem_pointRadical_iff _).mp hg
  rw [MulEquiv.coe_toMonoidHom,graphAut_pointRadicalElement]
  exact (mem_planeRadical_iff _).mpr ⟨_,rfl⟩

lemma graphAut_map_sylowCenter : sylowCenter.map (graphAut (F := F)).toMonoidHom =
    sylowCenter := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g,hg,rfl⟩
    obtain ⟨s,t,rfl⟩ := (mem_sylowCenter_iff _).mp hg
    exact (mem_sylowCenter_iff _).mpr ⟨t^2,s,(graphAut_central s t).symm⟩
  · rw [Subgroup.card_map_of_injective (f := (graphAut (F := F)).toMonoidHom) graphAut.injective]

private lemma conjugate_central_of_graph {A : Subgroup (Sp F)}
    (hA : ∃ g : Sp F, (A.map (graphAut (F := F)).toMonoidHom).map
      (MulAut.conj g).toMonoidHom ≤ sylowCenter) :
    ∃ g : Sp F, A.map (MulAut.conj g).toMonoidHom ≤ sylowCenter := by
  obtain ⟨g,hg⟩ := hA
  refine ⟨graphAut.symm g,?_⟩
  apply (Subgroup.map_le_map_iff_of_injective
    (f := (graphAut (F := F)).toMonoidHom) graphAut.injective).mp
  rw [graphAut_map_sylowCenter]
  rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
  have hm := hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
    (Subgroup.mem_map_of_mem graphAut.toMonoidHom hy))
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply] using hm

lemma elementary_conjugate_radical {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (B : Subgroup (Sp F)) [IsElementaryAbelian 2 B] :
    ∃ g : Sp F, B.map (MulAut.conj g).toMonoidHom ≤ pointRadical ∨
      B.map (MulAut.conj g).toMonoidHom ≤ planeRadical := by
  obtain ⟨S,hS⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF hn)
  have hs : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun T : Sylow 2 (Sp F) => (T : Subgroup (Sp F))) hg
  let C := B.map (MulAut.conj g).toMonoidHom
  have hC : C ≤ unipotent := hs ▸ Subgroup.map_mono hS
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (C.subgroupOf unipotent) := IsElementaryAbelian.subgroupOf hC
  refine ⟨g,?_⟩
  rcases elementary_le_wing (C.subgroupOf unipotent) with hp | hl
  · left
    rw [pointRadical_eq_wing]
    change C ≤ _
    rw [← Subgroup.map_subgroupOf_eq_of_le hC]
    exact Subgroup.map_mono hp
  · right
    rw [planeRadical_eq_wing]
    change C ≤ _
    rw [← Subgroup.map_subgroupOf_eq_of_le hC]
    exact Subgroup.map_mono hl

lemma elementary_rank_le {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (B : Subgroup (Sp F)) [IsElementaryAbelian 2 B] : rank B ≤ 3*n := by
  obtain ⟨g,hg | hg⟩ := elementary_conjugate_radical hF hn B
  · have h := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hg)
    change rank (B.map (MulAut.conj g).toMonoidHom) ≤ Representation.BinaryOffender.rank (pointRadical (F := F)) at h
    rwa [rank_map_conj,rank_pointRadical hF] at h
  · have h := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hg)
    change rank (B.map (MulAut.conj g).toMonoidHom) ≤ Representation.BinaryOffender.rank (planeRadical (F := F)) at h
    rwa [rank_map_conj,rank_planeRadical hF] at h

private lemma elementary_not_offender_of_placement {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    {B : Subgroup (Sp F)} (hB : IsElementaryTwo B)
    (hplace : (∃ g : Sp F, B.map (MulAut.conj g).toMonoidHom ≤ sylowCenter) ∨
      5*n ≤ fixedCodim graphPair B) :
    rank B + 1 < fixedCodim graphPair B := by
  rcases hplace with ⟨g,hg⟩ | hcod
  · exact conjugate_central_subgroup_not_offender hF hn g hg hB.1
  · let := hB.2
    have := elementary_rank_le hF hn B
    omega

private lemma derived_not_offender_of_full
    (hfull : ∀ B : Subgroup (Sp F), IsElementaryTwo B → rank B + 1 < fixedCodim graphPair B)
    {B : Subgroup (commutator (Sp F))} (hB : IsElementaryTwo B) :
    rank B + 1 < fixedCodim (derivedPair (graphAut (F := F))) B := by
  let := hB.2
  have he : IsElementaryTwo (B.map (commutator (Sp F)).subtype) := by
    refine ⟨?_,IsElementaryAbelian.map _⟩
    intro h
    exact hB.1 ((Subgroup.map_eq_bot_iff_of_injective B
      (commutator (Sp F)).subtype_injective).mp h)
  have h := hfull _ he
  rw [rank_map_injective _ Subtype.val_injective] at h
  change rank B + 1 < Module.finrank (ZMod 2)
    (Space F ⧸ fixedSpace (graphPair.comp (commutator (Sp F)).subtype) B)
  rw [fixedSpace_comp_map]
  exact h

/-- A subgroup of the plane radical is central up to conjugacy, or already
has the full radical's fixed codimension on the paired module. -/
lemma plane_subgroup_placement {n : ℕ} (hF : Nat.card F = 2^n)
    {A : Subgroup (Sp F)} (hA : A ≤ planeRadical) :
    (∃ g : Sp F, A.map (MulAut.conj g).toMonoidHom ≤ sylowCenter) ∨
      5*n ≤ fixedCodim graphPair A := by
  classical
  by_cases hdep : ∀ B C : Plane.symmetricMatrices F, Plane.shearSp B ∈ A →
      Plane.shearSp C ∈ A → B.val 0 0*C.val 1 1-B.val 1 1*C.val 0 0 = 0
  · exact Or.inl (dependent_shears_conjugate_central hA hdep)
  · push Not at hdep
    obtain ⟨B,C,hB,hC,hind⟩ := hdep
    exact Or.inr (independent_shears_fixedCodim hF hA hB hC hind).ge

/-- The exceptional graph automorphism gives the same alternative for the
other actual parabolic radical. -/
lemma point_subgroup_placement {n : ℕ} (hF : Nat.card F = 2^n)
    {A : Subgroup (Sp F)} (hA : A ≤ pointRadical) :
    (∃ g : Sp F, A.map (MulAut.conj g).toMonoidHom ≤ sylowCenter) ∨
      5*n ≤ fixedCodim graphPair A := by
  have hm : A.map (graphAut (F := F)).toMonoidHom ≤ planeRadical :=
    (Subgroup.map_mono hA).trans graphAut_map_pointRadical_le
  rcases plane_subgroup_placement hF hm with hz | hc
  · exact Or.inl (conjugate_central_of_graph hz)
  · right
    rwa [fixedCodim_map_graph] at hc

/-- The elementary-subgroup alternative in the native symplectic group:
central up to conjugacy, or paired fixed codimension at least 5n. -/
lemma elementary_subgroup_placement {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (B : Subgroup (Sp F)) [IsElementaryAbelian 2 B] :
    (∃ g : Sp F, B.map (MulAut.conj g).toMonoidHom ≤ sylowCenter) ∨
      5*n ≤ fixedCodim graphPair B := by
  obtain ⟨g,hg⟩ := elementary_conjugate_radical hF hn B
  have hp : (∃ h : Sp F, (B.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj h).toMonoidHom ≤ sylowCenter) ∨
      5*n ≤ fixedCodim graphPair (B.map (MulAut.conj g).toMonoidHom) := by
    rcases hg with hg | hg
    · exact point_subgroup_placement hF hg
    · exact plane_subgroup_placement hF hg
  rcases hp with ⟨h,hh⟩ | hc
  · left
    refine ⟨h*g,?_⟩
    rintro _ ⟨b,hb,rfl⟩
    have hm := hh (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom
      (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hb))
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,_root_.mul_inv_rev,mul_assoc] using hm
  · right
    rwa [fixedCodim_map_conj] at hc

/-- No nontrivial elementary subgroup of the full matrix group is an
F−1 offender on its natural-plus-graph pair, including over the binary field. -/
lemma elementary_subgroup_not_offender {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    {B : Subgroup (Sp F)} (hB : IsElementaryTwo B) :
    rank B + 1 < fixedCodim graphPair B := by
  let := hB.2
  exact elementary_not_offender_of_placement hF hn hB
    (elementary_subgroup_placement hF hn B)

/-- The same strict inequality for the actual derived group. The inclusion,
rather than an identification with the full binary group, transports the action. -/
lemma derived_elementary_subgroup_not_offender {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    {B : Subgroup (commutator (Sp F))} (hB : IsElementaryTwo B) :
    rank B + 1 < fixedCodim (derivedPair (graphAut (F := F))) B :=
  derived_not_offender_of_full (fun _ h => elementary_subgroup_not_offender hF hn h) hB

end SymplecticConjugatePair
