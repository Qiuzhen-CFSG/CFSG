module
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12.Action
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Quadratic actors on the full native M12 heart

The checked quadratic graph bounds Sylow actors by four elements. For a
noncyclic actor, five selected independent displacement rows give a surjection
from its fixed-space quotient onto a five-space. Cyclic actors have displacement
at least four by the existing inner and outer involution calculations. Sylow
conjugation yields the strict quadratic bound on the entire native action.

The finite certificate hypotheses are discharged in the source assembly.
Source: Aschbacher--Smith B.4.5 and K.4.4, printed pp.87,459--460.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Sporadic.Mathieu M12ExceptionalExtension OverlapExtensions
open CFSG.Quasithin.ChapterH.Section10To12
open CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12
open Data
variable (hp : ∀ i, prefixCheck i) (hm : ∀ i, matrixCheck i)
include hp hm

private theorem double_matrix_zero (A : Subgroup Carrier)
    (hq : IsQuadratic coordinateRepresentation A) (i j : Fin 128)
    (hi : (Overlap.element i).val ∈ A) (hj : (Overlap.element j).val ∈ A) :
    (matrix i - 1) * (matrix j - 1) = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have hh := hq _ hi _ hj v
  rw [coordinate_element hp hm, coordinate_element hp hm] at hh
  simpa only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec, Matrix.mulVecLin_apply, sub_eq_zero] using hh

private theorem element_of_quadratic (hs : ∀ i, squareCheck i)
    (A : Subgroup Carrier) (hq : IsQuadratic coordinateRepresentation A)
    (a : overlap) (ha : a.val ∈ A) : ∃ v, Overlap.element (vertex v) = a := by
  obtain ⟨i, rfl⟩ := Overlap.element_surjective a
  rcases hs i with he | hn
  · exact ⟨squareIndex i, congrArg Overlap.element he⟩
  · have hz := double_matrix_zero hp hm A hq i i ha ha
    exact (hn (congrArg (fun m => m (squareWitness i).1 (squareWitness i).2) hz)).elim

private theorem quadratic_adjacent (hr : ∀ v w, rejectionCheck v w)
    (A : Subgroup Carrier) (hq : IsQuadratic coordinateRepresentation A) (v w : Fin 36)
    (hv : (Overlap.element (vertex v)).val ∈ A)
    (hw : (Overlap.element (vertex w)).val ∈ A) : adjacent v w = true := by
  rcases hr v w with he | hn
  · exact he
  · have h1 := double_matrix_zero hp hm A hq (vertex v) (vertex w) hv hw
    have h2 := double_matrix_zero hp hm A hq (vertex w) (vertex v) hw hv
    change displacement v * displacement w = 0 at h1
    change displacement w * displacement v = 0 at h2
    simp only [h1, h2, ite_self, Matrix.zero_apply] at hn
    exact (hn rfl).elim

set_option maxRecDepth 4096 in
/-- The finite graph certificate bounds each quadratic actor in the actual Sylow. -/
theorem sylow_card_le_four (hs : ∀ i, squareCheck i)
    (hr : ∀ v w, rejectionCheck v w) (hn : ∀ v, neighborsCheck v)
    (A : Subgroup Carrier) (hA : A ≤ overlap) (hq : IsQuadratic coordinateRepresentation A) :
    Nat.card A ≤ 4 := by
  classical
  let s : Finset (Fin 36) := Finset.univ.filter (fun v => (Overlap.element (vertex v)).val ∈ A)
  have hs4 : s.card ≤ 4 := MathieuCode.QuadraticActors.clique_card_le_four 0 adjacent hn s (by
    intro v hv w hw
    exact quadratic_adjacent hp hm hr A hq v w (Finset.mem_filter.mp hv).2
      (Finset.mem_filter.mp hw).2)
  let f : s → A := fun v => ⟨(Overlap.element (vertex v.val)).val, (Finset.mem_filter.mp v.property).2⟩
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨v, hv⟩ := element_of_quadratic hp hm hs A hq ⟨a.val,hA a.property⟩ a.property
    have he := congrArg Subtype.val hv
    exact ⟨⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm ▸ a.property⟩⟩, Subtype.ext he⟩
  exact (Nat.card_le_card_of_surjective f hf).trans (by simpa using hs4)

set_option maxRecDepth 4096 in
private theorem selected_annihilates (A : Subgroup Carrier) (v w : Fin 36)
    (hv : (Overlap.element (vertex v)).val ∈ A)
    (hw : (Overlap.element (vertex w)).val ∈ A) :
    fixedSpace coordinateRepresentation A ≤ (selected v w).mulVecLin.ker := by
  intro x hx
  have aux (j : Fin 36) (hj : (Overlap.element (vertex j)).val ∈ A) :
      (displacement j).mulVecLin x = 0 := by
    have hh := hx ⟨_,hj⟩
    change coordinateRepresentation (Overlap.element (vertex j)).val x = x at hh
    rw [coordinate_element hp hm] at hh
    simpa only [Data.displacement, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
      Matrix.one_mulVec, Pi.zero_apply, sub_eq_zero] using hh
  have hmin := aux (min v w) (by rcases min_choice v w with he | he <;> rw [he] <;> assumption)
  have hmax := aux (max v w) (by rcases max_choice v w with he | he <;> rw [he] <;> assumption)
  change (selected v w).mulVecLin x = 0
  ext r
  by_cases hr : rowIndex v w r < 10
  · have hh := congrFun hmin ⟨rowIndex v w r % 10, Nat.mod_lt _ (by decide)⟩
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, selected, hr, if_true, Pi.zero_apply] using hh
  · have hh := congrFun hmax ⟨rowIndex v w r % 10, Nat.mod_lt _ (by decide)⟩
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, selected, hr, if_false, Pi.zero_apply] using hh

private theorem pair_fixedCodim_ge_five (hr : ∀ v, rankCheck v)
    (A : Subgroup Carrier) (v w : Fin 36)
    (hv : (Overlap.element (vertex v)).val ∈ A)
    (hw : (Overlap.element (vertex w)).val ∈ A)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hwv : w ≠ v) (hadj : adjacent v w = true) :
    5 ≤ fixedCodim coordinateRepresentation A := by
  have hcert := hr v w hv0 hw0 hwv hadj
  let f := (fixedSpace coordinateRepresentation A).liftQ (selected v w).mulVecLin
    (selected_annihilates hp hm A v w hv hw)
  have hf : Function.Surjective f := by
    intro x
    refine ⟨(fixedSpace coordinateRepresentation A).mkQ ((rightInverse v w).mulVecLin x), ?_⟩
    change (selected v w).mulVecLin ((rightInverse v w).mulVecLin x) = x
    rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hcert, Matrix.mulVecLin_one]
    rfl
  have hh := LinearMap.finrank_le_finrank_of_surjective hf
  change 5 ≤ Module.finrank (ZMod 2) (Coordinates ⧸ fixedSpace coordinateRepresentation A)
  simpa only [Module.finrank_fin_fun] using hh


omit hp hm in
private theorem involution_bound (t : Carrier) (ht : orderOf t = 2) :
    4 ≤ fixedCodim coordinateRepresentation (zpowers t) := by
  have he := fixedCodim_map_equivariant coordinateRepresentation
    Ambient.automorphismRepresentation automorphismEquiv.toMonoidHom heartEquiv
    coordinate_equivariant (zpowers t)
  rw [he, MonoidHom.map_zpowers]
  change 4 ≤ fixedCodim Ambient.automorphismRepresentation (zpowers (automorphismEquiv t))
  have ha : orderOf (automorphismEquiv t) = 2 := (automorphismEquiv.orderOf_eq t).trans ht
  by_cases hi : automorphismEquiv t ∈ MulAut.innerSubgroup Sporadic.Mathieu.M12
  · obtain ⟨x,hx⟩ := hi
    have hxi : orderOf x = 2 := by
      rw [← hx] at ha
      exact (orderOf_injective _ M12AutomorphismRank.conjugation_injective x).symm.trans ha
    have hh := fixedSpace_comp_map Ambient.automorphismRepresentation MulAut.conj (zpowers x)
    rw [Ambient.automorphismRepresentation_inner, MonoidHom.map_zpowers] at hh
    rw [← hx]
    change 4 ≤ Module.finrank (ZMod 2) (M12Heart ⧸ fixedSpace _ _)
    rw [← hh]
    exact (fixedCodim_involution x hxi).ge
  · rw [LocalActors.fixedCodim_native_outer outer_involution_fusion
      Ambient.automorphismRepresentation Ambient.automorphismRepresentation_faithful hi ha]
    decide

private theorem sylow_rank_two_bound (hs : ∀ i, squareCheck i)
    (hr : ∀ v w, rejectionCheck v w) (hcert : ∀ v, rankCheck v)
    (A : Subgroup Carrier) (hA : IsElementaryTwo A) (hS : A ≤ overlap)
    (hq : IsQuadratic coordinateRepresentation A) (hd : rank A = 2) :
    5 ≤ fixedCodim coordinateRepresentation A := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ha2 : orderOf a = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  obtain ⟨b,hb,hb1,hba⟩ : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    by_contra hn
    push Not at hn
    have hle : A ≤ zpowers a := by
      intro b hb
      by_cases hb1 : b = 1
      · simpa only [hb1] using (zpowers a).one_mem
      · rw [hn b hb hb1]
        exact mem_zpowers a
    have hc := Subgroup.card_le_of_le hle
    rw [hA.card_eq_two_pow_rank, hd, Nat.card_zpowers, ha2] at hc
    omega
  obtain ⟨v,hv⟩ := element_of_quadratic hp hm hs A hq ⟨a,hS ha⟩ ha
  obtain ⟨w,hw⟩ := element_of_quadratic hp hm hs A hq ⟨b,hS hb⟩ hb
  have hv' : (Overlap.element (vertex v)).val = a := congrArg Subtype.val hv
  have hw' : (Overlap.element (vertex w)).val = b := congrArg Subtype.val hw
  have hzero : Overlap.element (vertex 0) = 1 := by
    rw [show vertex 0 = 0 from by decide +kernel, Overlap.element_zero]
  have hv0 : v ≠ 0 := by
    intro he
    apply ha1
    rw [he, hzero] at hv'
    exact hv'.symm
  have hw0 : w ≠ 0 := by
    intro he
    apply hb1
    rw [he, hzero] at hw'
    exact hw'.symm
  have hwv : w ≠ v := by
    intro he
    apply hba
    exact hw'.symm.trans (he ▸ hv')
  have hvA := hv'.symm ▸ ha
  have hwA := hw'.symm ▸ hb
  exact pair_fixedCodim_ge_five hp hm hcert A v w hvA hwA hv0 hw0 hwv
    (quadratic_adjacent hp hm hr A hq v w hvA hwA)

/-- The exact local certificate contract excludes every quadratic actor on the
literal ten-dimensional Aut(M12) heart, after Sylow conjugation. -/
theorem strict_of_certificates (hs : ∀ i, squareCheck i)
    (hr : ∀ v w, rejectionCheck v w) (hn : ∀ v, neighborsCheck v)
    (hcert : ∀ v, rankCheck v) : 2 < quadraticRatio coordinateRepresentation := by
  by_contra! hle
  obtain ⟨A,hA,hq,hsmall⟩ := (quadraticRatio_le_iff coordinateRepresentation (by simp)).mp hle
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S VerifiedPair.commonSylow
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom = overlap :=
    congrArg Sylow.toSubgroup hg
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB : IsElementaryTwo B := hA.map_conj g
  have hBq : IsQuadratic coordinateRepresentation B := quadratic_conj _ hq g
  have hBS : B ≤ overlap := hg' ▸ Subgroup.map_mono hAS
  have hsmallB : fixedCodim coordinateRepresentation B ≤ 2 * rank B := by
    dsimp only [B]
    rw [fixedCodim_map_conj, rank_map_conj]
    exact (actionRatio_le_nat_iff coordinateRepresentation hA 2).mp hsmall
  have hcard := sylow_card_le_four hp hm hs hr hn B hBS hBq
  have hrB : rank B ≤ 2 := (Nat.log_mono_right hcard : Nat.log 2 (Nat.card B) ≤ Nat.log 2 4)
  by_cases hr2 : rank B = 2
  · have hh := sylow_rank_two_bound hp hm hs hr hcert B hB hBS hBq hr2
    omega
  · have hr1 : rank B = 1 := by have := hB.rank_pos; omega
    let : IsElementaryAbelian 2 B := hB.2
    obtain ⟨t,ht,ht1⟩ := B.bot_or_exists_ne_one.resolve_left hB.1
    have ht2 : orderOf t = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
    have hh := involution_bound t ht2
    have hf := Submodule.finrank_mono
      (fixedSpace_antitone coordinateRepresentation (zpowers_le.mpr ht))
    have hdimB := fixedCodim_add_finrank coordinateRepresentation B
    have hdimt := fixedCodim_add_finrank coordinateRepresentation (zpowers t)
    omega

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12
