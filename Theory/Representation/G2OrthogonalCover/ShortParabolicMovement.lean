module
public import Theory.Representation.G2OrthogonalCover.ParabolicFixed
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Perfectness

/-!
# Movement by the short G₂ parabolic residual

Over a finite field of characteristic two with more than two elements, the
short residual moves the full trace-zero Cayley module. A torus element
supplies each noncentral coordinate, and a root displacement supplies the
scalar coordinate. The universal-cover quotient then gives the same movement
in every perfect central cover of the binary natural module.

This is the model calculation used in the crossed-block argument of
Aschbacher--Smith 4.3.7, with the natural-cover description of I.2.3.
Root coordinates use the attributed ATLAS imports; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff. No additional ATLAS source is copied here.
-/

public section
noncomputable section
open Atlas.SplitOctonion Representation Representation.OneCohomology
open Representation.BinaryOffender Subgroup
namespace Atlas.G2.Natural.OrthogonalCover.ParabolicFixed
open Explicit LieParabolicSetup
variable (F : Type*) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

private def coordinate (i : Fin 8) (hi : i ≠ 3 ∧ i ≠ 4) (a : F) : TraceZero F :=
  ⟨Pi.single i a,by simp [trace,Ne.symm hi.1,Ne.symm hi.2]⟩

omit [Algebra (ZMod 2) F] in
theorem short_displacements_span (hq : 2 < Nat.card F)
    (S : AddSubgroup (TraceZero F))
    (hS : ∀ g ∈ local₁ (F := F), ∀ x : TraceZero F, traceZeroAction F g x - x ∈ S) : S = ⊤ := by
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ht' : t ≠ 0 ∧ t ≠ 1 := by simpa using ht
  let m : Fˣ := Units.mk0 t ht'.1
  have ht2 : t^2 ≠ 1 := by
    intro he
    rcases sq_eq_one_iff.mp he with he | he
    · exact ht'.2 he
    · exact ht'.2 (he.trans (CharTwo.neg_eq _))
  have hw (i : Fin 8) (hi : i ≠ 3 ∧ i ≠ 4) : (torusWeights m m⁻¹ i : F) ≠ 1 := by
    fin_cases i <;> simp_all [torusWeights,m,pow_two]
    intro he
    exact ht2 (by rw [←inv_eq_one,mul_inv_rev]; exact he)
  have hcS (i : Fin 8) (hi : i ≠ 3 ∧ i ≠ 4) (a : F) : coordinate F i hi a ∈ S := by
    let c : F := torusWeights m m⁻¹ i
    have hc1 : c - 1 ≠ 0 := sub_ne_zero.mpr (hw i hi)
    have hd := hS (torus m m⁻¹) (short_torus_mem_local₁ m) (coordinate F i hi (a/(c-1)))
    have he : traceZeroAction F (torus m m⁻¹) (coordinate F i hi (a/(c-1))) -
        coordinate F i hi (a/(c-1)) = coordinate F i hi a := by
      apply Subtype.ext
      funext j
      by_cases hj : j=i
      · subst j
        simp [coordinate,traceZeroAction_val,torus,torusEquiv,torusLinear]
        change c * (a/(c-1)) - a/(c-1) = a
        field_simp
      · simp [coordinate,traceZeroAction_val,torus,torusEquiv,torusLinear,Pi.single_apply,hj]
    rwa [he] at hd
  have hscalar (a : F) : a • identity F ∈ S := by
    have hroot : rootC (1 : F) ∈ local₁ := unipotent_le_local₁ (subset_closure (by simp))
    have hd := hS (rootC 1) hroot (coordinate F 7 (by decide) a)
    have he : traceZeroAction F (rootC 1) (coordinate F 7 (by decide) a) -
        coordinate F 7 (by decide) a - coordinate F 0 (by decide) a = a • identity F := by
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [traceZeroAction_val,coordinate,Matrix.vecHead,Matrix.vecTail,rootC,
        rootCEquiv,rootCLinear,rootCApply,identity,unit,CharTwo.neg_eq]
    rw [←he]
    exact S.sub_mem hd (hcS 0 (by decide) a)
  apply top_unique
  intro x _
  have ht : x.val 4 = x.val 3 := by
    have hh := x.property
    change x.val 3+x.val 4=0 at hh
    exact eq_of_sub_eq_zero (by simpa [CharTwo.sub_eq_add,add_comm] using hh)
  have he : x = coordinate F 0 (by decide) (x.val 0) + coordinate F 1 (by decide) (x.val 1) +
      coordinate F 2 (by decide) (x.val 2) + coordinate F 5 (by decide) (x.val 5) +
      coordinate F 6 (by decide) (x.val 6) + coordinate F 7 (by decide) (x.val 7) + x.val 3 • identity F := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [coordinate,Matrix.vecHead,Matrix.vecTail,identity,unit,ht]
  rw [he]
  exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem
    (hcS _ _ _) (hcS _ _ _)) (hcS _ _ _)) (hcS _ _ _)) (hcS _ _ _)) (hcS _ _ _)) (hscalar _)

theorem short_cover_moved {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) (Model F) W}
    (p : σ.IntertwiningMap (fullBinaryNatural F)) (hq : 2 < Nat.card F) (hp : IsCover p) :
    subspaceCommutator σ ⊤ (local₁ (F := F)) = ⊤ := by
  obtain ⟨f,hf,_⟩ := exists_full_quotient F p hq hp
  let S := subspaceCommutator σ ⊤ (local₁ (F := F))
  have ht : S.toAddSubgroup.comap f.toLinearMap.toAddMonoidHom = ⊤ := by
    apply short_displacements_span F hq
    intro g hg x
    change f (fullBinaryAction F g x - x) ∈ S
    rw [map_sub,f.isIntertwining]
    exact Submodule.subset_span ⟨g,hg,f x,Submodule.mem_top,rfl⟩
  apply top_unique
  intro w _
  obtain ⟨x,rfl⟩ := hf w
  exact (show x ∈ S.toAddSubgroup.comap f.toLinearMap.toAddMonoidHom from ht ▸ trivial)
end Atlas.G2.Natural.OrthogonalCover.ParabolicFixed
