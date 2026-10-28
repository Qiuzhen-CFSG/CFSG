module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeRank.ChecksSix
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeRank.ChecksSeven
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Native
public import Theory.Representation.MathieuCodeRestriction.Duality
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Rank saturation for near-offenders on the M24 code

The checked colorings distinguish all commuting square-one elements of any
subgroup whose code fixed codimension is below six or seven. Such a subgroup
has order at most six or seventeen, respectively. Thus elementary actors of
ranks four and five cannot have fixed codimension at most their rank plus one.
This gives the rank-six conclusion needed for the original code offender.
Source: Aschbacher--Smith H.16.5 and 8.2.5, printed pp.404,716--717.
-/

public noncomputable section
open Sporadic.Mathieu Representation Representation.BinaryOffender Subgroup
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
open Sporadic.Mathieu.M24LocalGeometry
open MathieuCode.CocodeOctad.Involutions MathieuCode.QuadraticActors
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.CodeRank

private lemma matrix_column_mem (A : Subgroup M24) (v : Fin 192)
    (hv : (native v).val ∈ A) (j : Fin 11) :
    (matrix v).col j ∈ (subspaceCommutator cocodeRepresentation ⊤ A).map coordinates := by
  refine ⟨_, Submodule.subset_span ⟨(native v).val, hv,
    sectionMap (Pi.single j 1), Submodule.mem_top, rfl⟩, ?_⟩
  have h := LinearMap.congr_fun (displacementMatrix_eq (native v).val) (Pi.single j 1)
  rw [displacementMatrix_native] at h
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using h.symm

private lemma selected_rank_le (c : Fin 2) (A : Subgroup M24) (v w : Fin 192)
    (hv : (native v).val ∈ A) (hw : (native w).val ∈ A) :
    (selected c v w).rank ≤ fixedCodim codeRepresentation A := by
  have hle : Submodule.span (ZMod 2) (Set.range (selected c v w).col) ≤
      (subspaceCommutator cocodeRepresentation ⊤ A).map coordinates := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : columnIndex c v w j < 11
    · have he : (selected c v w).col j =
          (matrix v).col ⟨columnIndex c v w j % 11, Nat.mod_lt _ (by decide)⟩ := by
        ext i
        simp only [selected, Matrix.col_apply, if_pos hj]
      rw [he]
      exact matrix_column_mem A v hv _
    · have he : (selected c v w).col j =
          (matrix w).col ⟨columnIndex c v w j % 11, Nat.mod_lt _ (by decide)⟩ := by
        ext i
        simp only [selected, Matrix.col_apply, if_neg hj]
      rw [he]
      exact matrix_column_mem A w hw _
  have hf := Submodule.finrank_mono hle
  rw [← Matrix.rank_eq_finrank_span_cols] at hf
  have he := coordinateEquiv.finrank_map_eq (subspaceCommutator cocodeRepresentation ⊤ A)
  change Module.finrank (ZMod 2)
      ((subspaceCommutator cocodeRepresentation ⊤ A).map coordinates) = _ at he
  rw [he] at hf
  have hd := fixedCodim_map_equivariant codeRepresentation cocodeRepresentation.dual
    (MonoidHom.id M24) codeDuality.toLinearEquiv
    (fun g x => LinearMap.congr_fun (codeDuality.isIntertwining' g) x) A
  rw [Subgroup.map_id, fixedCodim_dual_eq_moved_finrank] at hd
  exact hf.trans_eq hd.symm

private theorem check (c : Fin 2) (v : Fin 192) : checkRow c v := by
  fin_cases c
  · exact six_checked v
  · exact seven_checked v

private theorem native_card_bound (c : Fin 2) (A : Subgroup M24)
    [IsElementaryAbelian 2 A] (hA : A ≤ SylowNormalizer.candidate)
    (hsmall : fixedCodim codeRepresentation A < degree c) : Nat.card A ≤ colorBound c := by
  classical
  let s : Finset (Fin 192) := Finset.univ.filter (fun v => (native v).val ∈ A)
  have hs (v : Fin 192) : v ∈ s ↔ (native v).val ∈ A := by simp [s]
  have distinct (v w : Fin 192) (hv : v ∈ s) (hw : w ∈ s) (hlt : v < w) :
      color c v ≠ color c w := by
    intro he
    have hc : compatible v w = true := native_compatible v w (Subtype.ext
      (congrArg (fun a : A => a.val) (mul_comm
        (⟨(native v).val,(hs v).mp hv⟩ : A) ⟨(native w).val,(hs w).mp hw⟩)))
    have hi := check c v w hlt he hc
    have hr := Matrix.rank_mul_le_right (leftInverse c v w) (selected c v w)
    rw [hi,Matrix.rank_one,Fintype.card_fin] at hr
    have hu := selected_rank_le c A v w ((hs v).mp hv) ((hs w).mp hw)
    omega
  have hinj : Function.Injective (fun v : s => color c v.val) := by
    intro v w he
    apply Subtype.ext
    rcases lt_trichotomy v.val w.val with hl | heq | hg
    · exact (distinct _ _ v.property w.property hl he).elim
    · exact heq
    · exact (distinct _ _ w.property v.property hg he.symm).elim
  have hcard : s.card ≤ colorBound c := by
    have hh := Fintype.card_le_of_injective _ hinj
    simpa only [Fintype.card_coe,Fintype.card_fin] using hh
  let f : s → A := fun v => ⟨(native v.val).val,(hs v.val).mp v.property⟩
  have hf : Function.Surjective f := by
    intro a
    let b : SylowNormalizer.candidate := ⟨a.val,hA a.property⟩
    have hb : b^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
    obtain ⟨v,hv⟩ := vertex_of_square b hb
    have ha : (native v).val = a.val := congrArg Subtype.val hv
    exact ⟨⟨v,(hs v).mpr (ha.symm ▸ a.property)⟩,Subtype.ext ha⟩
  have hc := Nat.card_le_card_of_surjective f hf
  have he : Nat.card s = s.card := by simp
  exact (hc.trans_eq he).trans hcard

/-- Small code fixed codimension bounds the full elementary actor by the
checked coloring, after conjugacy into the native Sylow subgroup. -/
theorem card_bound (c : Fin 2) (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim codeRepresentation A < degree c) : Nat.card A ≤ colorBound c := by
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S SextetCore.nativeSylow
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom = SylowNormalizer.candidate :=
    congrArg Sylow.toSubgroup hg
  let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  have hc := native_card_bound c (A.map (MulAut.conj g).toMonoidHom)
    (hg' ▸ Subgroup.map_mono hAS) (by rwa [fixedCodim_map_conj])
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hc

/-- Ranks four and five are incompatible with the code near-offender
inequality. The rank-six conclusion applies to the full original image. -/
theorem rank_six (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hfour : 4 ≤ rank A) (hsix : rank A ≤ 6)
    (hnear : fixedCodim codeRepresentation A ≤ rank A + 1) : rank A = 6 := by
  have hn : A ≠ ⊥ := by intro he; rw [he,Representation.BinaryOffender.rank_bot] at hfour; omega
  have hc := (show IsElementaryTwo A from ⟨hn,inferInstance⟩).card_eq_two_pow_rank
  by_cases h4 : rank A = 4
  · have hb := card_bound 0 A (by change _ < 6; omega)
    change Nat.card A ≤ 6 at hb
    rw [hc,h4] at hb
    norm_num at hb
  by_cases h5 : rank A = 5
  · have hb := card_bound 1 A (by change _ < 7; omega)
    change Nat.card A ≤ 17 at hb
    rw [hc,h5] at hb
    norm_num at hb
  omega

end MathieuCode.NormalizedShadowRows.CodeRank
