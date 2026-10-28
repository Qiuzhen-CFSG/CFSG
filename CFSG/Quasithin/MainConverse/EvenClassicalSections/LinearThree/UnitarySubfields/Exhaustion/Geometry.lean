module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.BorelCases
public import Theory.AlgebraicGroup.Bor1.AdaptedBasis
public import Mathlib.LinearAlgebra.Determinant
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Reducible and decomposition-stabilizing unitary subgroups

The full inverse image in SU of a projective subgroup is used throughout.
If it preserves a nonzero proper subspace, an adapted basis identifies its
matrices with a subgroup of an SL₃ point or line parabolic. The projection
kernel is central and solvable, so the projective parabolic envelope also
handles this full lift and its projective quotient. This covers degenerate
and nondegenerate invariant subspaces uniformly.

If the lift permutes three independent lines, its action on those lines has
abelian kernel: elements of the kernel are diagonal in the chosen basis.
The image embeds in the solvable symmetric group on four letters. Thus the
lift, and then its projective image, is solvable. No assertion that these
geometric cases exhaust all proper subgroups is made.

Source: Hartley–Mitchell, GLS3, Theorem 6.5.3(a,b),
`refs/KGroup/GLS3/chapter6.tex`. These geometric arguments use no K-group
hypothesis or assumed subgroup classification.
-/

open Matrix BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped MatrixGroups Pointwise

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion

variable {F : Type} [Field F]

local notation:1024 "↑ₘ" A:1024 => ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)

/-- The full inverse image under the actual SU → PSU projection. -/
@[expose] public def specialLift (J : HermitianForm 3 F)
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Subgroup J.specialSubgroup :=
  U.comap (suProjection J)

/-- Reducibility of the full lift on its defining matrix space. -/
@[expose] public def IsReducible (J : HermitianForm 3 F)
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ∃ W : Submodule F (Fin 3 → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
    ∀ g : specialLift J U, ∀ v ∈ W, g.val.val.val.mulVec v ∈ W

/-- The defining inclusion of SU into SL over the coefficient field. -/
@[expose] public def specialToSL (J : HermitianForm 3 F) : J.specialSubgroup →* SL(3, F) where
  toFun g := ⟨g.val.val, by
    have h := (J.mem_specialSubgroup_iff g.val).mp g.property |>.2
    simpa using congrArg Units.val h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The defining SU → SL map is faithful. -/
public theorem specialToSL_injective (J : HermitianForm 3 F) :
    Function.Injective (specialToSL J) := by
  intro a b h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

private noncomputable def basisChange (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    SL(3, F) →* SL(3, F) where
  toFun g := ⟨LinearMap.toMatrix b b (Matrix.toLin' ↑ₘg), by
    rw [LinearMap.det_toMatrix, LinearMap.det_toLin']
    exact g.property⟩
  map_one' := by
    apply Subtype.ext
    change LinearMap.toMatrix b b (Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3) F)) = 1
    simp
  map_mul' g h := by
    apply Subtype.ext
    change LinearMap.toMatrix b b (Matrix.toLin' (↑ₘg * ↑ₘh)) =
      LinearMap.toMatrix b b (Matrix.toLin' ↑ₘg) * LinearMap.toMatrix b b (Matrix.toLin' ↑ₘh)
    rw [Matrix.toLin'_mul, LinearMap.toMatrix_comp b b b]

private theorem basisChange_injective (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    Function.Injective (basisChange b) := by
  intro a c h
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply (LinearMap.toMatrix b b).injective
  exact congrArg Subtype.val h

private theorem exists_adapted_basis (W : Submodule F (Fin 3 → F)) :
    ∃ b : Module.Basis (Fin 3) F (Fin 3 → F),
      (∀ j : Fin 3, j.val < Module.finrank F W → b j ∈ W) ∧
      (∀ v ∈ W, ∀ i : Fin 3, Module.finrank F W ≤ i.val → b.repr v i = 0) := by
  obtain ⟨b, hr, hb⟩ : ∃ (b : Module.Basis (Fin 3) F (Fin 3 → F))
      (hr : Module.finrank F W ≤ 3),
      ∀ j : Fin (Module.finrank F W),
        b (Fin.castLE hr j) = (Module.finBasis F W j : Fin 3 → F) := by
    have h := Theory.AlgebraicGroup.Bor1.exists_basis_extends_finBasis W
    rw [Module.finrank_fin_fun] at h
    exact h
  refine ⟨b, ?_, ?_⟩
  · intro j hj
    have he : Fin.castLE hr (⟨j.val, hj⟩ : Fin (Module.finrank F W)) = j := rfl
    rw [← he, hb]
    exact Subtype.property _
  · intro v hv i hi
    have hsum : v = ∑ j : Fin (Module.finrank F W),
        (Module.finBasis F W).repr ⟨v, hv⟩ j • b (Fin.castLE hr j) := by
      simp_rw [hb]
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
        (congrArg (fun x : W => (x : Fin 3 → F))
        ((Module.finBasis F W).sum_repr ⟨v, hv⟩)).symm
    rw [hsum]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      Module.Basis.repr_self, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j _
    have hji : Fin.castLE hr j ≠ i := by
      intro he
      have hh := congrArg Fin.val he
      dsimp at hh
      omega
    simp [hji]

private theorem envelope_linear_preimage [Finite F] {n : ℕ}
    (P : Subgroup SL(3, F)) (hP : Envelope n (P.map (Matrix.PSL3.projection F))) :
    Envelope n P := by
  let p := (Matrix.PSL3.projection F).subgroupMap P
  let i : p.ker →* (Matrix.PSL3.projection F).ker :=
    (P.subtype.comp p.ker.subtype).codRestrict _ (by
      intro x
      have hx := congrArg Subtype.val x.property
      exact hx)
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : (Matrix.PSL3.projection F).ker => x.val) hab
  let : Group.IsSolvable p.ker := Group.isSolvable_of_isSolvable_injective hi
  exact hP.of_solvable_kernel p

private theorem envelope_reducible_representation [Finite F] {n : ℕ}
    {H : Type} [Group H] (r : H →* SL(3, F)) (hr : Function.Injective r)
    (W : Submodule F (Fin 3 → F)) (hW0 : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hW : ∀ g : H, ∀ v ∈ W, (↑ₘ(r g)).mulVec v ∈ W) : Envelope n H := by
  obtain ⟨b, hbin, hbzero⟩ := exists_adapted_basis W
  let s := (basisChange b).comp r
  have hs : Function.Injective s := (basisChange_injective b).comp hr
  have hzero (g : H) (i j : Fin 3) (hi : Module.finrank F W ≤ i.val)
      (hj : j.val < Module.finrank F W) : (↑ₘ(s g)) i j = 0 := by
    change (LinearMap.toMatrix b b (Matrix.toLin' (↑ₘ(r g)))) i j = 0
    rw [LinearMap.toMatrix_apply]
    exact hbzero _ (hW g _ (hbin j hj)) i hi
  have hpos : 0 < Module.finrank F W := by
    by_contra h
    exact hW0 (Submodule.finrank_eq_zero.mp (by omega))
  have hlt : Module.finrank F W < 3 := by
    simpa only [Module.finrank_fin_fun] using Submodule.finrank_lt hWtop
  have hrank : Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by omega
  rcases hrank with h1 | h2
  · let t : H →* Matrix.PSL3.LinearThree.pointParabolicSL F := s.codRestrict _ (by
      intro g
      rw [Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff]
      exact ⟨hzero g 1 0 (by omega) (by omega), hzero g 2 0 (by omega) (by omega)⟩)
    have ht : Function.Injective t := by
      intro a c h
      exact hs (congrArg Subtype.val h)
    exact .subgroup t ht (envelope_linear_preimage _ (.pointParabolic F))
  · let t : H →* Matrix.PSL3.LinearThree.lineParabolicSL F := s.codRestrict _ (by
      intro g
      rw [Matrix.PSL3.LinearThree.mem_lineParabolicSL_iff]
      exact ⟨hzero g 2 0 (by omega) (by omega), hzero g 2 1 (by omega) (by omega)⟩)
    have ht : Function.Injective t := by
      intro a c h
      exact hs (congrArg Subtype.val h)
    exact .subgroup t ht (envelope_linear_preimage _ (.lineParabolic F))

/-- Every reducible projective subgroup has a parabolic envelope. -/
public theorem envelope_of_reducible [Finite F] {n : ℕ} (J : HermitianForm 3 F)
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hU : IsReducible J U) :
    Envelope n U := by
  obtain ⟨W, hW0, hWtop, hW⟩ := hU
  let r := (specialToSL J).comp (specialLift J U).subtype
  have hr : Function.Injective r :=
    (specialToSL_injective J).comp (specialLift J U).subtype_injective
  have h : Envelope n (specialLift J U) :=
    envelope_reducible_representation r hr W hW0 hWtop hW
  let p := (suProjection J).subgroupComap U
  have hp : Function.Surjective p := by
    intro u
    obtain ⟨g, hg⟩ := suProjection_surjective J u.val
    exact ⟨⟨g, by change suProjection J g ∈ U; rw [hg]; exact u.property⟩,
      Subtype.ext hg⟩
  exact .quotient p hp h

/-- The full special-unitary lift permutes three independent lines. -/
@[expose] public def PreservesThreeLines (J : HermitianForm 3 F)
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ∃ b : Module.Basis (Fin 3) F (Fin 3 → F), ∀ g : specialLift J U, ∀ i : Fin 3,
    ∃ j : Fin 3, (Submodule.span F {b i}).map (Matrix.toLin' g.val.val.val) =
      Submodule.span F {b j}

private theorem basis_lines_injective (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    Function.Injective (fun i => Submodule.span F {b i}) := by
  intro i j hij
  by_contra hne
  change Submodule.span F {b i} = Submodule.span F {b j} at hij
  have hm : b i ∈ Submodule.span F {b j} := by
    rw [← hij]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hh := congrArg (fun v => b.repr v i) hc
  simp [Ne.symm hne] at hh

private theorem solvable_of_three_lines {H : Type} [Group H]
    (r : H →* SL(3, F)) (hr : Function.Injective r)
    (b : Module.Basis (Fin 3) F (Fin 3 → F))
    (hperm : ∀ g : H, ∀ i : Fin 3, ∃ j : Fin 3,
      (Submodule.span F {b i}).map (Matrix.toLin' (↑ₘ(r g))) = Submodule.span F {b j}) :
    Group.IsSolvable H := by
  classical
  let rho := SpecialLinearGroup.toLin'.comp r
  let : MulAction H (Submodule F (Fin 3 → F)) :=
    MulAction.compHom _ rho
  let A : SubMulAction H (Submodule F (Fin 3 → F)) := {
    carrier := Set.range (fun i => Submodule.span F {b i})
    smul_mem' := by
      rintro g _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hperm g i
      exact ⟨j, hj.symm⟩ }
  let p : H →* Equiv.Perm A := MulAction.toPermHom H A
  let e : Fin 3 ≃ A := Equiv.ofInjective _ (basis_lines_injective b)
  let e4 : A ↪ Fin 4 := ⟨fun a => (e.symm a).castSucc,
    fun _ _ h => e.symm.injective (Fin.castSucc_inj.mp h)⟩
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm A) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e4)
  have heigen (g : p.ker) (i : Fin 3) :
      ∃ c : F, (↑ₘ(r g.val)).mulVec (b i) = c • b i := by
    have hg : p g.val = 1 := g.property
    have hline := congrArg (fun s : Equiv.Perm A => s ⟨Submodule.span F {b i}, ⟨i, rfl⟩⟩) hg
    have hfix : (Submodule.span F {b i}).map (Matrix.toLin' (↑ₘ(r g.val))) =
        Submodule.span F {b i} := congrArg Subtype.val hline
    have hm : (↑ₘ(r g.val)).mulVec (b i) ∈ Submodule.span F {b i} := by
      rw [← hfix]
      exact ⟨b i, Submodule.mem_span_singleton_self _, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨c, hc.symm⟩
  have hcomm (g h : p.ker) : g * h = h * g := by
    apply Subtype.ext
    apply hr
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply b.ext
    intro i
    obtain ⟨c, hc⟩ := heigen g i
    obtain ⟨d, hd⟩ := heigen h i
    change ((↑ₘ(r (g.val * h.val))).mulVec (b i)) =
      ((↑ₘ(r (h.val * g.val))).mulVec (b i))
    simp only [map_mul]
    change ((↑ₘ(r g.val)) * (↑ₘ(r h.val))).mulVec (b i) =
      ((↑ₘ(r h.val)) * (↑ₘ(r g.val))).mulVec (b i)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hd, hc, Matrix.mulVec_smul, Matrix.mulVec_smul, hc, hd, smul_smul, smul_smul,
      mul_comm d c]
  let : Group.IsSolvable p.ker := Group.isSolvable_of_comm hcomm
  exact Group.isSolvable_of_ker_le_range p.ker.subtype p (by rw [Subgroup.range_subtype])

/-- A subgroup preserving three independent lines is solvable. -/
public theorem solvable_of_preservesThreeLines (J : HermitianForm 3 F)
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : PreservesThreeLines J U) : Group.IsSolvable U := by
  obtain ⟨b, hb⟩ := hU
  let r := (specialToSL J).comp (specialLift J U).subtype
  have hr : Function.Injective r :=
    (specialToSL_injective J).comp (specialLift J U).subtype_injective
  let : Group.IsSolvable (U.comap (suProjection J)) := solvable_of_three_lines r hr b hb
  let p := (suProjection J).subgroupComap U
  apply Group.isSolvable_of_surjective (f := p)
  intro u
  obtain ⟨g, hg⟩ := suProjection_surjective J u.val
  exact ⟨⟨g, by change suProjection J g ∈ U; rw [hg]; exact u.property⟩,
    Subtype.ext hg⟩

/-- The decomposition-stabilizer alternative contributes only solvable groups. -/
public theorem envelope_of_preservesThreeLines {n : ℕ} (J : HermitianForm 3 F)
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : PreservesThreeLines J U) : Envelope n U :=
  .solvable U (solvable_of_preservesThreeLines J U hU)

/-- The full lift is irreducible and preserves no decomposition into three lines.
In dimension three, these are precisely the remaining linear primitive cases. -/
@[expose] public def IsPrimitiveLift (J : HermitianForm 3 F)
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ¬ IsReducible J U ∧ ¬ PreservesThreeLines J U

end CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion
