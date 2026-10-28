module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.CentralizerGeometry
public import Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups.Directions
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry

/-!
# Overgroups of the binary transvection centralizer in arbitrary degree

Every proper overgroup of the centralizer of a rank-one transvection fixes
its image line or its fixed hyperplane. The proof uses full transvection
directions: they form an invariant subspace, and Gaussian elimination shows
that a subgroup with every direction is the whole binary linear group.
The invariant subspace is forced to be the image line or the fixed hyperplane.

This extends the degree-four proof in
`Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups` to the degrees
needed for the invariant parabolic pairs in Aschbacher–Smith 2.3.9(7),
printed pp.525–526. It does not use an automorphism classification.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup BinaryLinear BinaryLinear.FourCentralizerOvergroups

private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem all_directions_generate {n : ℕ} [Nontrivial (Fin n)] (K : Subgroup (BinaryLinear.GL (Fin n → ZMod 2)))
    (hK : directions K = ⊤) : K = ⊤ := by
  have ht (v : Fin n → ZMod 2) : IsDirection K v :=
    show v ∈ directions K from hK ▸ Submodule.mem_top
  have hsl (A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : A.toLin' ∈ K := by
    apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun A => A.toLin' ∈ K) A
    · intro i j hij c hc
      have he : Matrix.SpecialLinearGroup.diag2n hij c hc = 1 := by
        apply Subtype.ext
        simp [Matrix.SpecialLinearGroup.diag2n_coe, scalar_one hc]
      rw [he, map_one]
      exact K.one_mem
    · intro i j hij a
      let f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := a • LinearMap.proj j
      have hf : f (Pi.single i 1) = 0 := by simp [f, hij.symm]
      have he : (Matrix.SpecialLinearGroup.transvection hij a).toLin' =
          transvection (Pi.single i 1) f hf := by
        apply LinearEquiv.ext
        intro v
        change ((1 : Matrix (Fin n) (Fin n) (ZMod 2)) + Matrix.single i j a).mulVec v =
          v + f v • Pi.single i 1
        simp [Matrix.add_mulVec, Matrix.single_mulVec_eq, f]
      rw [he]
      exact ht _ f hf
    · intro A B hA hB
      simpa only [map_mul] using K.mul_mem hA hB
  apply top_unique
  intro g _
  obtain ⟨A, rfl⟩ := (slEquivLinear n).surjective g
  exact hsl A

variable {n : ℕ}
local notation "Vec" => (Vector n)

private theorem line_mem_of_fix (g : BinaryLinear.GL Vec) (w : Vec) (hw : g w = w) :
    g ∈ parabolic (Submodule.span (ZMod 2) {w}) := by
  intro v
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    exact Submodule.mem_span_singleton.mpr ⟨a, g.injective (by rwa [map_smul, hw])⟩
  · intro hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hw]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w)

private theorem transvection_mem_flag (w u : Vec)
    (f q : Vec →ₗ[ZMod 2] ZMod 2) (hfu : f u = 0) (hqw : q w = 0) (hqu : q u = 0) :
    transvection u q hqu ∈ parabolic (Submodule.span (ZMod 2) {w}) ⊓ parabolic f.ker := by
  constructor
  · apply line_mem_of_fix
    change w + q w • u = w
    simp [hqw]
  · intro v
    change f (v + q v • u) = 0 ↔ f v = 0
    simp [hfu]

/-- Every proper overgroup of the incident line–hyperplane stabilizer in
GLₙ(2) preserves one of the two subspaces. -/
private theorem linear_flag_overgroup_cover [Nontrivial (Fin n)] (w : Vec) (f : Vec →ₗ[ZMod 2] ZMod 2)
    (hfw : f w = 0) (K : Subgroup (BinaryLinear.GL Vec))
    (hC : parabolic (Submodule.span (ZMod 2) {w}) ⊓ parabolic f.ker ≤ K)
    (hK : K ≠ ⊤) :
    K ≤ parabolic (Submodule.span (ZMod 2) {w}) ∨ K ≤ parabolic f.ker := by
  classical
  let D := directions K
  have hwD : w ∈ D := by
    intro q hq
    exact hC (transvection_mem_flag w w f q hfw hq hq)
  have hstable {g : BinaryLinear.GL Vec} (hg : g ∈ K) {v : Vec} (hv : v ∈ D) : g v ∈ D :=
    (le_parabolic_directions K hg v).mpr hv
  have hproper : D ≠ ⊤ := fun hD => hK (all_directions_generate K hD)
  have hDH : D ≤ f.ker := by
    intro v hv
    by_contra hvf
    have hfv : f v = 1 := scalar_one hvf
    have hHD : f.ker ≤ D := by
      intro u hu
      have hg := hC (transvection_mem_flag w u f f hu hfw hu)
      have hh := hstable hg hv
      change v + f v • u ∈ D at hh
      rw [hfv, one_smul] at hh
      simpa only [add_sub_cancel_left] using D.sub_mem hh hv
    apply hproper
    apply top_unique
    intro x _
    have hx : x - f x • v ∈ f.ker := by
      change f (x - f x • v) = 0
      simp [hfv]
    simpa only [sub_add_cancel] using D.add_mem (hHD hx) (D.smul_mem (f x) hv)
  by_cases hDl : D ≤ Submodule.span (ZMod 2) {w}
  · have hD : D = Submodule.span (ZMod 2) {w} :=
      le_antisymm hDl ((Submodule.span_singleton_le_iff_mem w D).mpr hwD)
    exact Or.inl (by simpa only [← hD] using le_parabolic_directions K)
  · obtain ⟨v, hv, hvl⟩ := SetLike.not_le_iff_exists.mp hDl
    have hHD : f.ker ≤ D := by
      intro u hu
      by_contra huD
      have hvwu : v ∉ Submodule.span (ZMod 2) {w, u} := by
        intro hvwu
        obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hvwu
        by_cases hb : b = 0
        · apply hvl
          exact Submodule.mem_span_singleton.mpr ⟨a, by simpa [hb] using he⟩
        · have hb1 := scalar_one hb
          apply huD
          have hh : u = v - a • w := by rw [← he, hb1, one_smul, add_sub_cancel_left]
          rw [hh]
          exact D.sub_mem hv (D.smul_mem a hwD)
      obtain ⟨q, hqv, hq⟩ := Submodule.exists_le_ker_of_notMem hvwu
      have hqw : q w = 0 := hq (Submodule.subset_span (by simp))
      have hqu : q u = 0 := hq (Submodule.subset_span (by simp))
      have hh := hstable (hC (transvection_mem_flag w u f q hu hqw hqu)) hv
      change v + q v • u ∈ D at hh
      rw [scalar_one hqv, one_smul] at hh
      exact huD (by simpa only [add_sub_cancel_left] using D.sub_mem hh hv)
    have hD : D = f.ker := le_antisymm hDH hHD
    exact Or.inr (by simpa only [← hD] using le_parabolic_directions K)

variable {G : Type*} [Group G] {L : Subgroup G} [NeZero n]
  {e : L ≃* PSL n} {t : L}

/-- A proper overgroup of the transvection centralizer preserves one endpoint. -/
theorem TransvectionCoordinates.proper_overgroup_endpoint
    (c : TransvectionCoordinates e t) (hn : 2 ≤ n) (K : Subgroup L)
    (hC : centralizer ({t} : Set L) ≤ K) (hK : K ≠ ⊤) :
    K ≤ subspaceStabilizer e c.line ∨ K ≤ subspaceStabilizer e c.hyperplane := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let a := linearModel e
  have hC' : BinaryLinear.parabolic c.line ⊓ BinaryLinear.parabolic c.hyperplane ≤
      K.map a.toMonoidHom := by
    intro g hg
    obtain ⟨x, rfl⟩ := a.surjective g
    refine ⟨x, hC ?_, rfl⟩
    rw [c.centralizer_eq]
    exact hg
  have hK' : K.map a.toMonoidHom ≠ ⊤ := by
    intro he
    apply hK
    apply top_unique
    intro x _
    have hx : a x ∈ K.map a.toMonoidHom := he ▸ mem_top _
    obtain ⟨y, hy, hxy⟩ := hx
    exact a.injective hxy ▸ hy
  rcases linear_flag_overgroup_cover c.vector c.functional c.incident
    (K.map a.toMonoidHom) hC' hK' with h | h
  · exact Or.inl (fun x hx => h (mem_map_of_mem a.toMonoidHom hx))
  · exact Or.inr (fun x hx => h (mem_map_of_mem a.toMonoidHom hx))

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
