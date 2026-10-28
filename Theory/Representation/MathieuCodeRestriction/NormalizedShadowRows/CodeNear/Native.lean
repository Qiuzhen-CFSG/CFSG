module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeNear.Checks
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeNear.SmallData
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.OuterSpan.Native
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.OuterSpan.Native
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Odd

/-!
# Small displacement in the full M22 code action

Fix an actual inner involution and conjugate its centralizer Sylow to the
native one. The checked cocode-commutator matrices, together with the literal
code/cocode duality, bound elementary subgroups containing that involution:
fewer than six displaced dimensions permit at most eight elements, and
fewer than five permit at most four. Conjugacy returns both bounds to the
original subgroup of the full pair stabilizer.

The private import deliberately extends the existing quotient-coordinate
implementation; its body is used only to prove a private evaluation lemma.
Source: Aschbacher--Smith H.16.2(5),H.16.5, printed pp.402--404,
refs/quasithin.pdf. The later source application uses these bounds to prove
the near-offender displacement premise for the original code row.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix
open Sporadic.Mathieu MathieuCode MathieuCode.QuadraticActors
open MathieuCode.CocodeOctad.Involutions
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
open Sporadic.Mathieu.M24LocalGeometry
open scoped IsMulCommutative Pointwise
namespace MathieuCode.NormalizedShadowRows.CodeNear

private def anchor : m22PairStabilizer := ⟨outerNative 27, by
  rw [m22PairStabilizer, MulAction.mem_stabilizer_finset']
  intro a ha
  have he : a = 0 ∨ a = 9 := by simpa [m22Pair] using ha
  rcases he with rfl | rfl
  · change (outerNative 27).val 0 ∈ m22Pair
    rw [outerNative_apply]
    decide +kernel
  · change (outerNative 27).val 9 ∈ m22Pair
    rw [outerNative_apply]
    decide +kernel⟩

private theorem anchor_order : orderOf anchor = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change (outerNative 27).val ((outerNative 27).val x) = x
    rw [outerNative_apply,outerNative_apply]
    revert x
    decide +kernel
  · intro he
    have hh := congrArg (fun a : m22PairStabilizer => a.val.val 1) he
    change (outerNative 27).val 1 = 1 at hh
    rw [outerNative_apply] at hh
    exact (by decide +kernel : outerPoint 27 1 ≠ (1 : Fin 24)) hh

private theorem anchor_inner : anchor ∈ m22ToPairStabilizer.range := by
  apply (m22ToPairStabilizer_mem_range_iff_fixed_zero anchor).mpr
  change (outerNative 27).val 0 = 0
  rw [outerNative_apply]
  decide +kernel

private theorem sylow_centralizes_anchor : M22ChapterH.CompatibleSylow.outer.toSubgroup ≤
    centralizer ({anchor} : Set m22PairStabilizer) := by
  have hc : M22ChapterH.CompatibleSylow.ambient.toSubgroup ≤
      centralizer ({anchor.val} : Set M24) := by
    rw [M22ChapterH.CompatibleSylow.ambient_coe,Subgroup.map_le_iff_le_comap,
      SylowNormalizer.candidate,Subgroup.closure_le]
    rintro _ ⟨i,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change (M22ChapterH.CompatibleSylow.transportPerm * SylowNormalizer.generatorPerm i *
        M22ChapterH.CompatibleSylow.transportPerm⁻¹) ((outerNative 27).val x) =
      (outerNative 27).val ((M22ChapterH.CompatibleSylow.transportPerm *
        SylowNormalizer.generatorPerm i * M22ChapterH.CompatibleSylow.transportPerm⁻¹) x)
    rw [outerNative_apply,outerNative_apply]
    revert x i
    decide +kernel
  intro g hg
  apply mem_centralizer_singleton_iff.mpr
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (hc hg))

private theorem quotient_coordinates_mk (v : Cocode) (i : Fin 11) :
    OuterSpan.quotientCoordinates (m22PairLine.mkQ v) i =
      coordinates v i - coordinates v 0 * pairCoordinate i := rfl

private theorem quotient_column (v : Fin 72) (a : m22PairStabilizer)
    (ha : outerNative v = a.val) (j : Fin 11) :
    (quotientMatrix v).col j = OuterSpan.quotientCoordinates
      (m22OuterCocodeRepresentation a (m22PairLine.mkQ (sectionMap (Pi.single j 1))) -
        m22PairLine.mkQ (sectionMap (Pi.single j 1))) := by
  have he := LinearMap.congr_fun (displacementMatrix_eq (outerNative v)) (Pi.single j 1)
  rw [displacementMatrix_outerNative] at he
  have he' : ∀ i, outerMatrix v i j = coordinates
      (cocodeRepresentation a.val (sectionMap (Pi.single j 1)) - sectionMap (Pi.single j 1)) i := by
    intro i
    have h := congrFun he i
    simpa only [ha,Matrix.mulVecLin_apply,Matrix.mulVec_single,MulOpposite.op_one,one_smul,
      Matrix.col_apply,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply] using h
  ext i
  rw [m22OuterCocodeRepresentation_mk,←map_sub]
  rw [quotient_coordinates_mk]
  change outerMatrix v i j - outerMatrix v 0 j * pairCoordinate i = _
  exact congrArg₂ (· - ·) (he' i) (congrArg (· * pairCoordinate i) (he' 0))

private theorem selected_rank_le (A : Subgroup m22PairStabilizer)
    (ha : anchor ∈ A) (v w : Fin 72)
    (hv : ∃ b ∈ A, outerNative v = b.val) (hw : ∃ b ∈ A, outerNative w = b.val) :
    (selected v w).rank ≤ fixedCodim m22OuterCodeRepresentation A := by
  have hcol (u : Fin 72) (hu : ∃ b ∈ A, outerNative u = b.val) (j : Fin 11) :
      (quotientMatrix u).col j ∈
        (subspaceCommutator m22OuterCocodeRepresentation ⊤ A).map OuterSpan.quotientCoordinates := by
    obtain ⟨b,hb,he⟩ := hu
    exact ⟨_,Submodule.subset_span ⟨b,hb,_,Submodule.mem_top,rfl⟩,(quotient_column u b he j).symm⟩
  have hle : Submodule.span (ZMod 2) (Set.range (selected v w).col) ≤
      (subspaceCommutator m22OuterCocodeRepresentation ⊤ A).map OuterSpan.quotientCoordinates := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change (fun i => quotientMatrix _ i _) ∈ _
    split_ifs
    · exact hcol 27 ⟨anchor,ha,rfl⟩ _
    · exact hcol v hv _
    · exact hcol w hw _
  have hf := Submodule.finrank_mono hle
  rw [←Matrix.rank_eq_finrank_span_cols] at hf
  have hm := Submodule.finrank_map_le OuterSpan.quotientCoordinates
    (subspaceCommutator m22OuterCocodeRepresentation ⊤ A)
  have hd := fixedCodim_map_equivariant m22OuterCodeRepresentation m22OuterCocodeRepresentation.dual
    (MonoidHom.id m22PairStabilizer) m22CodeCocodeDuality m22CodeCocodeDuality_equivariant A
  rw [Subgroup.map_id,fixedCodim_dual_eq_moved_finrank] at hd
  exact (hf.trans hm).trans_eq hd.symm

private theorem small_rank_le (A : Subgroup m22PairStabilizer)
    (ha : anchor ∈ A) (v : Fin 72)
    (hv : ∃ b ∈ A, outerNative v = b.val) :
    (smallSelected v).rank ≤ fixedCodim m22OuterCodeRepresentation A := by
  have hcol (u : Fin 72) (hu : ∃ b ∈ A, outerNative u = b.val) (j : Fin 11) :
      (quotientMatrix u).col j ∈
        (subspaceCommutator m22OuterCocodeRepresentation ⊤ A).map OuterSpan.quotientCoordinates := by
    obtain ⟨b,hb,he⟩ := hu
    exact ⟨_,Submodule.subset_span ⟨b,hb,_,Submodule.mem_top,rfl⟩,(quotient_column u b he j).symm⟩
  have hle : Submodule.span (ZMod 2) (Set.range (smallSelected v).col) ≤
      (subspaceCommutator m22OuterCocodeRepresentation ⊤ A).map OuterSpan.quotientCoordinates := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change (fun i => quotientMatrix _ i _) ∈ _
    split_ifs
    · exact hcol 27 ⟨anchor,ha,rfl⟩ _
    · exact hcol v hv _
  have hf := Submodule.finrank_mono hle
  rw [←Matrix.rank_eq_finrank_span_cols] at hf
  have hm := Submodule.finrank_map_le OuterSpan.quotientCoordinates
    (subspaceCommutator m22OuterCocodeRepresentation ⊤ A)
  have hd := fixedCodim_map_equivariant m22OuterCodeRepresentation m22OuterCocodeRepresentation.dual
    (MonoidHom.id m22PairStabilizer) m22CodeCocodeDuality m22CodeCocodeDuality_equivariant A
  rw [Subgroup.map_id,fixedCodim_dual_eq_moved_finrank] at hd
  exact (hf.trans hm).trans_eq hd.symm

private theorem native_card_bound (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A] (hS : A ≤ M22ChapterH.CompatibleSylow.outer.toSubgroup)
    (ha : anchor ∈ A) (hsmall : fixedCodim m22OuterCodeRepresentation A < 6) :
    Nat.card A ≤ 8 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hex (a : A) : ∃ v : Fin 72, outerNative v = a.val.val :=
    outer_vertex_of_square a.val (hS a.property)
      (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
  choose f hf using hex
  have hi : Function.Injective (fun a : A => color (f a)) := by
    intro a b hab
    by_contra hn
    have hne : f a ≠ f b := by
      intro he
      exact hn (Subtype.ext (Subtype.ext ((hf a).symm.trans (he ▸ hf b))))
    have bound (u v : A) (huv : f u < f v) (hc : color (f u) = color (f v)) : False := by
      have hadj := OuterSpan.native_adjacent (f u) (f v) (hf u) (hf v)
        (congrArg Subtype.val (mul_comm u v))
      have hr := Matrix.rank_mul_le_right (leftInverse (f u) (f v)) (selected (f u) (f v))
      rw [checked (f u) (f v) huv hc hadj,Matrix.rank_one,Fintype.card_fin] at hr
      have hb := selected_rank_le A ha (f u) (f v) ⟨u,u.property,hf u⟩ ⟨v,v.property,hf v⟩
      omega
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact bound a b hl hab
    · exact bound b a hl hab.symm
  simpa only [←Nat.card_eq_fintype_card,Nat.card_fin] using Fintype.card_le_of_injective _ hi

private theorem native_small_card_bound (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A] (hS : A ≤ M22ChapterH.CompatibleSylow.outer.toSubgroup)
    (ha : anchor ∈ A) (hsmall : fixedCodim m22OuterCodeRepresentation A < 5) :
    Nat.card A ≤ 4 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hex (a : A) : ∃ v : Fin 72, outerNative v = a.val.val :=
    outer_vertex_of_square a.val (hS a.property)
      (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
  choose f hf using hex
  have hmem (a : A) : f a ∈ smallSet := by
    by_contra hn
    have hr := Matrix.rank_mul_le_right (smallLeft (f a)) (smallSelected (f a))
    rw [small_checked (f a) hn,Matrix.rank_one,Fintype.card_fin] at hr
    have hb := small_rank_le A ha (f a) ⟨a,a.property,hf a⟩
    omega
  let g : A → smallSet := fun a => ⟨f a,hmem a⟩
  have hi : Function.Injective g := by
    intro a b he
    have he' : f a = f b := congrArg Subtype.val he
    exact Subtype.ext (Subtype.ext ((hf a).symm.trans (he' ▸ hf b)))
  have hc := Fintype.card_le_of_injective g hi
  rw [show Fintype.card smallSet = 4 from by decide +kernel] at hc
  rwa [Nat.card_eq_fintype_card]

private theorem normalize_inner_involution (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A]
    (x : m22PairStabilizer) (hx : x ∈ A) (hx2 : orderOf x = 2)
    (hxi : x ∈ m22ToPairStabilizer.range) :
    ∃ D : Subgroup m22PairStabilizer, IsElementaryAbelian 2 D ∧
      D ≤ M22ChapterH.CompatibleSylow.outer.toSubgroup ∧ anchor ∈ D ∧
      Nat.card D = Nat.card A ∧
      fixedCodim m22OuterCodeRepresentation D = fixedCodim m22OuterCodeRepresentation A := by
  obtain ⟨u,hu⟩ := hxi
  obtain ⟨v,hv⟩ := anchor_inner
  have hinj : Function.Injective m22ToPairStabilizer :=
    fun _ _ he => m22Embedding_injective (congrArg Subtype.val he)
  obtain ⟨g,hg⟩ := isConj_iff.mp (m22_involutions_isConj u v
    ((orderOf_injective _ hinj u).symm.trans (hu ▸ hx2))
    ((orderOf_injective _ hinj v).symm.trans (hv ▸ anchor_order)))
  let e := MulAut.conj (m22ToPairStabilizer g)
  let B := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hex : e x = anchor := by
    rw [←hu,←hv]
    rw [←hg,map_mul,map_mul,map_inv]
    rfl
  have hab : anchor ∈ B := hex ▸ mem_map_of_mem e.toMonoidHom hx
  let C := centralizer ({anchor} : Set m22PairStabilizer)
  have hBC : B ≤ C := by
    intro b hb
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨b,hb⟩ : B) ⟨anchor,hab⟩)
  let P := M22ChapterH.CompatibleSylow.outer.subtype sylow_centralizes_anchor
  let : IsElementaryAbelian 2 (B.subgroupOf C) := IsElementaryAbelian.subgroupOf hBC
  obtain ⟨R,hBR⟩ := (IsElementaryAbelian.isPGroup 2 (B.subgroupOf C)).exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq C R P
  let f := MulAut.conj c.val
  let D := B.map f.toMonoidHom
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map _
  have hDS : D ≤ M22ChapterH.CompatibleSylow.outer.toSubgroup := by
    rintro _ ⟨b,hb,rfl⟩
    have hm : MulAut.conj c (⟨b,hBC hb⟩ : C) ∈ P := by
      rw [←hc]
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hBR hb)
    exact hm
  have hac : f anchor = anchor := by
    change c.val * anchor * c.val⁻¹ = anchor
    rw [mem_centralizer_singleton_iff.mp c.property]
    group
  have had : anchor ∈ D := hac ▸ mem_map_of_mem f.toMonoidHom hab
  refine ⟨D,inferInstance,hDS,had,?_,?_⟩
  · dsimp only [D,B]
    rw [card_map_of_injective f.injective,card_map_of_injective e.injective]
  · dsimp only [D,B,f,e]
    rw [fixedCodim_map_conj,fixedCodim_map_conj]

/-- Low code displacement bounds the size of the original elementary subgroup;
conjugation retains its chosen inner involution in the centralizer Sylow. -/
theorem card_le_eight_of_inner_involution (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim m22OuterCodeRepresentation A < 6)
    (x : m22PairStabilizer) (hx : x ∈ A) (hx2 : orderOf x = 2)
    (hxi : x ∈ m22ToPairStabilizer.range) : Nat.card A ≤ 8 := by
  obtain ⟨D,hD,hDS,ha,hcard,hcodim⟩ := normalize_inner_involution A x hx hx2 hxi
  let := hD
  rw [←hcard]
  exact native_card_bound D hDS ha (hcodim ▸ hsmall)

/-- Below five code displacement, the same centralizer calculation leaves
at most four elements. -/
theorem card_le_four_of_inner_involution (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim m22OuterCodeRepresentation A < 5)
    (x : m22PairStabilizer) (hx : x ∈ A) (hx2 : orderOf x = 2)
    (hxi : x ∈ m22ToPairStabilizer.range) : Nat.card A ≤ 4 := by
  obtain ⟨D,hD,hDS,ha,hcard,hcodim⟩ := normalize_inner_involution A x hx hx2 hxi
  let := hD
  rw [←hcard]
  exact native_small_card_bound D hDS ha (hcodim ▸ hsmall)

end MathieuCode.NormalizedShadowRows.CodeNear
