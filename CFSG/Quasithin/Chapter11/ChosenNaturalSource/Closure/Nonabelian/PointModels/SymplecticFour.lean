module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.Generation
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.SpecificGroups.PSp4Three.Generation

/-!
# Two field-line residuals generate native Sp₄

Given two distinct vector lines, a transvection either fixes one vector or
is conjugate, by a transvection fixing the first, to a transvection fixing
the second. To find the conjugator, choose a vector in the first orthogonal
hyperplane outside two proper kernels. Thus the two vector fixers generate
the full native symplectic group, for both orthogonal and nonorthogonal pairs.
For a nonbinary field these fixers are perfect, so they lie in the respective
line-stabilizer solvable residuals. No projective quotient is substituted.

Source: Aschbacher--Smith, 11.5.3(1), printed p.779. The native transvection
and generation APIs are the attributed ATLAS ports under
`Theory.SpecificGroups.PSp4Three`; see `LICENSES/ATLAS.txt`.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.SymplecticFour
open Matrix.PSp4Three
variable {F : Type*} [Field F]

private theorem exists_orthogonal_separating {u x : Vector 2 F}
    (hu : u ≠ 0) (hx : x ∉ Submodule.span F {u}) :
    ∃ y, form u y = 0 ∧ form x y ≠ 0 := by
  obtain ⟨t, ht⟩ := Matrix.PSp4Three.Frame.exists_partner form form_nondegenerate hu
  by_contra! h
  have he : x = (form x t) • u := by
    apply sub_eq_zero.mp
    apply form_nondegenerate.1
    intro y
    have hy : form u (y - (form u y) • t) = 0 := by simp [map_sub, map_smul, ht]
    have hh := h _ hy
    simp only [map_sub, map_smul, smul_eq_mul] at hh
    rw [LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul]
    linear_combination hh
  exact hx (he ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))

/-- Two distinct vector fixers generate the full symplectic group. -/
theorem vector_fixers_generate {u w : Vector 2 F} (hu : u ≠ 0)
    (hw : w ∉ Submodule.span F {u}) :
    MulAction.stabilizer (Sp 2 F) u ⊔ MulAction.stabilizer (Sp 2 F) w = ⊤ := by
  let J := MulAction.stabilizer (Sp 2 F) u ⊔ MulAction.stabilizer (Sp 2 F) w
  have htrans (x : Vector 2 F) (t : F) : transvection x t ∈ J := by
    by_cases hux : form u x = 0
    · exact mem_sup_left (by rw [MulAction.mem_stabilizer_iff]; exact transvection_fixes_of_orthogonal hux t)
    by_cases hwx : form w x = 0
    · exact mem_sup_right (by rw [MulAction.mem_stabilizer_iff]; exact transvection_fixes_of_orthogonal hwx t)
    have hxu : x ∉ Submodule.span F {u} := by
      rintro hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      exact hux (by simp)
    obtain ⟨a, hua, hxa⟩ := exists_orthogonal_separating hu hxu
    obtain ⟨b, hub, hwb⟩ := exists_orthogonal_separating hu hw
    obtain ⟨y, huy, hxy, hwy⟩ : ∃ y, form u y = 0 ∧ form x y ≠ 0 ∧ form w y ≠ 0 := by
      by_cases hwa : form w a = 0
      · by_cases hxb : form x b = 0
        · exact ⟨a+b, by simp [map_add, hua, hub], by simp [map_add, hxb, hxa],
            by simp [map_add, hwa, hwb]⟩
        · exact ⟨b, hub, hxb, hwb⟩
      · exact ⟨a, hua, hxa, hwa⟩
    let c := form w x / form w y
    let z := x - c • y
    have hwz : form w z = 0 := by
      simp only [z, map_sub, map_smul, smul_eq_mul]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ hwy).symm
    have hzy : form z y = form x y := by simp [z]
    let g := transvection y (c / form x y)
    have hg : g ∈ J := mem_sup_left (by
      rw [MulAction.mem_stabilizer_iff]; exact transvection_fixes_of_orthogonal huy _)
    have hgz : g • z = x := by
      rw [transvection_apply, hzy, div_mul_cancel₀ _ hxy]
      exact sub_add_cancel x (c • y)
    have hz : transvection z t ∈ J := mem_sup_right (by
      rw [MulAction.mem_stabilizer_iff]; exact transvection_fixes_of_orthogonal hwz t)
    rw [← hgz, ← transvection_conjugate]
    exact J.mul_mem (J.mul_mem hg hz) (J.inv_mem hg)
  apply top_unique
  rw [← transvectionGroup_eq_top (n := 2) (F := F)]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨v, t, rfl⟩
  exact htrans v t

variable [Finite F] [CharP F 2]

private theorem vector_fixer_perfect {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {u : Vector 2 F} (hu : u ≠ 0) : Group.IsPerfect (MulAction.stabilizer (Sp 2 F) u) := by
  have he0 : (e 0 : Vector 2 F) ≠ 0 := by
    intro he
    have hh := congrFun he (Sum.inl 0)
    simp [Matrix.PSp4Three.e] at hh
  obtain ⟨g, hg⟩ := Theory.SpecificGroups.SymplecticFour.TwoLocalCover.nonzero_vector_transitive he0 hu
  have he : MulAction.stabilizer (Sp 2 F) (e 0 : Vector 2 F) =
      Theory.SpecificGroups.SymplecticFour.pointLocal := by
    ext a
    exact (Theory.SpecificGroups.SymplecticFour.mem_pointLocal_iff_fixed a).symm
  have hp : Group.IsPerfect (MulAction.stabilizer (Sp 2 F) (e 0 : Vector 2 F)) := by
    rw [he]
    exact Theory.SpecificGroups.SymplecticFour.pointLocal_perfect hF hn
  let := hp
  exact Group.IsPerfect.ofSurjective (f := (MulAction.stabilizerEquivStabilizer hg.symm).toMonoidHom)
    (MulAction.stabilizerEquivStabilizer hg.symm).surjective

open CFSG.Quasithin.ChapterB.QuasisimpleSource
/-- The two field-line residuals generate native Sp₄, for every nonbinary field. -/
theorem linePairGeneration (F : BinaryField) (hn : 1 < F.degree) :
    LinePairGeneration F (symplecticNatural (k := F.Carrier) 2) := by
  intro U W hU hW hUW
  have hUne : U ≠ ⊥ := by
    intro he
    have hzero : Module.finrank F.Carrier U = 0 := by rw [he]; exact finrank_bot _ _
    omega
  have hWne : W ≠ ⊥ := by
    intro he
    have hzero : Module.finrank F.Carrier W = 0 := by rw [he]; exact finrank_bot _ _
    omega
  obtain ⟨u, hu, hu0⟩ := U.ne_bot_iff.mp hUne
  obtain ⟨w, hw, hw0⟩ := W.ne_bot_iff.mp hWne
  have hspanU := eq_span_singleton_of_mem_of_finrank_eq_one hU hu hu0
  have hwu : w ∉ Submodule.span F.Carrier {u} := by
    intro hh
    rw [← hspanU] at hh
    exact hUW ((eq_span_singleton_of_mem_of_finrank_eq_one hU hh hw0).trans
      (eq_span_singleton_of_mem_of_finrank_eq_one hW hw hw0).symm)
  have hle (P : Submodule F.Carrier (Matrix.PSp4Three.Vector 2 F.Carrier)) (hP : Module.finrank F.Carrier P = 1)
      (v : Matrix.PSp4Three.Vector 2 F.Carrier) (hv : v ∈ P) (hv0 : v ≠ 0) :
      MulAction.stabilizer (Sp 2 F.Carrier) v ≤ residualIn
        (BinaryOffender.subspaceStabilizer
          (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))
          (P.restrictScalars (ZMod 2))) := by
    let := vector_fixer_perfect F.card_eq hn hv0
    apply le_map_solvableResidual_of_isPerfect
    intro a ha x
    have hav : a • v = v := ha
    have hfix (y : Vector 2 F.Carrier) (hy : y ∈ P) : a • y = y := by
      rw [eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0] at hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      change Matrix.mulVec a.val (c • v) = c • v
      rw [Matrix.mulVec_smul]
      change c • (a • v) = c • v
      rw [hav]
    change a • x ∈ P ↔ x ∈ P
    constructor
    · intro hx
      have he : a • (a • x) = a • x := hfix _ hx
      exact (MulAction.injective a he) ▸ hx
    · intro hx
      rw [hfix x hx]
      exact hx
  apply top_unique
  rw [← vector_fixers_generate hu0 hwu]
  exact sup_le (le_sup_of_le_left (hle U hU u hu hu0))
    (le_sup_of_le_right (hle W hW w hw hw0))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.SymplecticFour
