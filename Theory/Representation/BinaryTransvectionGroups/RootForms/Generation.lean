module

public import Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups.Directions
public import Theory.Representation.BinaryTransvectionGroups.RootForms
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Generation by full binary root groups

Full transvection directions form a subspace, so full root groups at a spanning
set of centers supply every transvection.  Gaussian elimination then generates
the whole binary linear group, including dimensions zero and one.

The coordinate argument generalizes the checked degree-four calculation in
`BinaryLinear.FourCentralizerOvergroups.Directions`; matrix induction is from
Mathlib.  This is the final linear-algebra step for the irreducible repair of
Aschbacher--Smith G.3.1, printed pp.337--338.
-/

@[expose] public section

open BinaryLinear BinaryLinear.FourCentralizerOvergroups
namespace BinaryTransvectionGroups
theorem coordinate_eq_top_of_directions_eq_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Subgroup (GL (ι → ZMod 2)))
    (hK : directions K = ⊤) : K = ⊤ := by
  have ht (v : ι → ZMod 2) : IsDirection K v :=
    show v ∈ directions K from hK ▸ Submodule.mem_top
  have hsl (A : Matrix.SpecialLinearGroup ι (ZMod 2)) : A.toLin' ∈ K := by
    rcases subsingleton_or_nontrivial ι with h | h
    · have he : A = 1 := Subsingleton.elim _ _
      rw [he, map_one]
      exact K.one_mem
    · apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun A => A.toLin' ∈ K) A
      · intro i j hij c hc
        have he : Matrix.SpecialLinearGroup.diag2n hij c hc = 1 := by
          apply Subtype.ext
          simp [Matrix.SpecialLinearGroup.diag2n_coe, ((by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc)]
        rw [he, map_one]
        exact K.one_mem
      · intro i j hij a
        let f : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 := a • LinearMap.proj j
        have hf : f (Pi.single i 1) = 0 := by simp [f, hij.symm]
        have he : (Matrix.SpecialLinearGroup.transvection hij a).toLin' =
            transvection (Pi.single i 1) f hf := by
          apply LinearEquiv.ext
          intro v
          change ((1 : Matrix ι ι (ZMod 2)) + Matrix.single i j a).mulVec v =
            v + f v • Pi.single i 1
          simp [Matrix.add_mulVec, Matrix.single_mulVec_eq, f]
        rw [he]
        exact ht _ f hf
      · intro A B hA hB
        simpa only [map_mul] using K.mul_mem hA hB
  apply top_unique
  intro g _
  let M := LinearMap.toMatrix' g.toLinearMap
  let N := LinearMap.toMatrix' g.symm.toLinearMap
  have hinv : M * N = 1 := by
    change LinearMap.toMatrix' g.toLinearMap * LinearMap.toMatrix' g.symm.toLinearMap = 1
    rw [← LinearMap.toMatrix'_comp]
    simp
  have hd : M.det = 1 := by
    apply ((by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) M.det)
    intro hz
    have hh := congrArg Matrix.det hinv
    rw [Matrix.det_mul, Matrix.det_one, hz, zero_mul] at hh
    exact zero_ne_one hh
  have he : Matrix.SpecialLinearGroup.toLin'
      (⟨M, hd⟩ : Matrix.SpecialLinearGroup ι (ZMod 2)) = g := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.toMatrix'_mulVec g.toLinearMap v
  rw [← he]
  exact hsl _

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem eq_top_of_directions_eq_top [FiniteDimensional (ZMod 2) V]
    (K : Subgroup (GL V)) (hK : directions K = ⊤) : K = ⊤ := by
  classical
  let b := Module.Free.chooseBasis (ZMod 2) V
  let ι := Module.Free.ChooseBasisIndex (ZMod 2) V
  let : Fintype ι := Fintype.ofFinite ι
  let e : V ≃ₗ[ZMod 2] (ι → ZMod 2) := b.equivFun
  let ρ : GL (ι → ZMod 2) →* GL V :=
    { toFun a := e.trans (a.trans e.symm)
      map_one' := by ext v; simp
      map_mul' := by intros; ext v; simp }
  have hco : directions (K.comap ρ) = ⊤ := by
    apply top_unique
    intro u _ f hf
    change ρ (transvection u f hf) ∈ K
    have hf' : (f.comp e.toLinearMap) (e.symm u) = 0 := by simp [hf]
    have he : ρ (transvection u f hf) =
        transvection (e.symm u) (f.comp e.toLinearMap) hf' := by
      ext v
      simp [ρ, transvection]
    rw [he]
    exact (show e.symm u ∈ directions K from hK ▸ Submodule.mem_top) _ _
  have ht := coordinate_eq_top_of_directions_eq_top (K.comap ρ) hco
  apply top_unique
  intro g _
  have hg : e.symm.trans (g.trans e) ∈ K.comap ρ := ht ▸ Subgroup.mem_top _
  change ρ (e.symm.trans (g.trans e)) ∈ K at hg
  have he : ρ (e.symm.trans (g.trans e)) = g := by ext v; simp [ρ]
  exact he ▸ hg

theorem eq_top_of_rootForms_on_spanning [FiniteDimensional (ZMod 2) V]
    (G : Subgroup (GL V)) (Δ : Set V) (hspan : Submodule.span (ZMod 2) Δ = ⊤)
    (hforms : ∀ x ∈ Δ, rootForms G x = (centerLine x).dualAnnihilator) : G = ⊤ := by
  apply eq_top_of_directions_eq_top
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro x hx f hf
  apply (mem_rootForms hf).mp
  rw [hforms x hx]
  exact (mem_line_annihilator x f).mpr hf

end BinaryTransvectionGroups
