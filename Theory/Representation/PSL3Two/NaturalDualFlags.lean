module
public import Theory.Representation.PSL3Two.FanoLocalStructure.ParabolicSpaces
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.PSL3Two.NaturalDualCentralizer

/-!
# Opposite flag commutators in the natural-plus-dual six-space

The point parabolic fixes the natural point and the line parabolic fixes
the dual point. Each lies in the opposite parabolic's commutator of the
common Sylow fixed plane. Four eight-vector certificates identify the
fixed lines; two explicit displacements generate each opposite line.
The actual natural-dual action is recovered by the dot-product equivalence.
This is the semisimple linear row of Aschbacher–Smith 13.4.14(1),
printed p.911, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender Subgroup Matrix.PSL3Two
namespace BinaryLinearThree.NaturalDualFlags
open AutomorphismAction FanoDecomposition FanoLocalStructure.ParabolicSpaces

private def pair := W.prod (W.comp graph.toMonoidHom)
private def p : Vector × Vector := (![1,0,0],0)
private def l : Vector × Vector := (0,![0,0,1])

private theorem natural_upper : ∀ v : Vector,
    W (Bruhat.upper 1) v = v → W (Bruhat.upper 4) v = v →
      v = 0 ∨ v = ![1,0,0] := by decide +kernel
private theorem dual_upper : ∀ v : Vector,
    W (graph (Bruhat.upper 1)) v = v → W (graph (Bruhat.upper 4)) v = v →
      v = 0 ∨ v = ![0,0,1] := by decide +kernel
private theorem natural_line : ∀ v : Vector,
    W (Bruhat.upper 1) v = v → W (Bruhat.upper 4) v = v →
      W (Bruhat.perm 2) v = v → v = 0 := by decide +kernel
private theorem dual_point : ∀ v : Vector,
    W (graph (Bruhat.upper 1)) v = v → W (graph (Bruhat.upper 4)) v = v →
      W (graph (Bruhat.perm 1)) v = v → v = 0 := by decide +kernel

private theorem fixed_point (v : Vector × Vector) (hv : v ∈ fixedSpace pair pointParabolicSL) :
    v = 0 ∨ v = p := by
  have h₁ := hv ⟨Bruhat.upper 1,(Bruhat.upper_mem 1).1⟩
  have h₄ := hv ⟨Bruhat.upper 4,(Bruhat.upper_mem 4).1⟩
  have hs := hv ⟨Bruhat.perm 1,by decide⟩
  have hw := dual_point v.2 (congrArg Prod.snd h₁) (congrArg Prod.snd h₄) (congrArg Prod.snd hs)
  rcases natural_upper v.1 (congrArg Prod.fst h₁) (congrArg Prod.fst h₄) with h | h
  · exact Or.inl (Prod.ext h hw)
  · exact Or.inr (Prod.ext h hw)
private theorem fixed_line (v : Vector × Vector) (hv : v ∈ fixedSpace pair lineParabolicSL) :
    v = 0 ∨ v = l := by
  have h₁ := hv ⟨Bruhat.upper 1,(Bruhat.upper_mem 1).2⟩
  have h₄ := hv ⟨Bruhat.upper 4,(Bruhat.upper_mem 4).2⟩
  have hs := hv ⟨Bruhat.perm 2,by decide⟩
  have hw := natural_line v.1 (congrArg Prod.fst h₁) (congrArg Prod.fst h₄) (congrArg Prod.fst hs)
  rcases dual_upper v.2 (congrArg Prod.snd h₁) (congrArg Prod.snd h₄) with h | h
  · exact Or.inl (Prod.ext hw h)
  · exact Or.inr (Prod.ext hw h)

private theorem p_fixed : p ∈ fixedSpace pair borelSL := by
  intro g
  apply Prod.ext
  · exact congrArg Subtype.val ((mem_pointParabolic_iff_fixes_point g.val).mp g.property.1)
  · exact map_zero (W (graph g.val))
private theorem l_fixed : l ∈ fixedSpace pair borelSL := by
  intro g
  apply Prod.ext
  · exact map_zero (W g.val)
  · exact congrArg (fun x : Line => x.normal.val)
      ((mem_lineParabolic_iff_fixes_line g.val).mp g.property.2)

private def lower10 : Group := ⟨!![1,0,0; 1,1,0; 0,0,1],by decide⟩
private def lower21 : Group := ⟨!![1,0,0; 0,1,0; 0,1,1],by decide⟩
private theorem p_moves : (pair (Bruhat.perm 2) p-p) + (pair lower10 p-p) = p := by
  decide +kernel
private theorem l_moves : (pair (Bruhat.perm 1) l-l) + (pair lower21 l-l) = l := by
  decide +kernel
private theorem pair_tests :
    fixedSpace pair lineParabolicSL ≤ subspaceCommutator pair (fixedSpace pair borelSL) pointParabolicSL ∧
    fixedSpace pair pointParabolicSL ≤ subspaceCommutator pair (fixedSpace pair borelSL) lineParabolicSL := by
  constructor
  · intro v hv
    rcases fixed_line v hv with rfl | rfl
    · exact Submodule.zero_mem _
    · rw [←l_moves]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨Bruhat.perm 1,by decide,l,l_fixed,rfl⟩)
        (Submodule.subset_span ⟨lower21,by decide,l,l_fixed,rfl⟩)
  · intro v hv
    rcases fixed_point v hv with rfl | rfl
    · exact Submodule.zero_mem _
    · rw [←p_moves]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨Bruhat.perm 2,by decide,p,p_fixed,rfl⟩)
        (Submodule.subset_span ⟨lower10,by decide,p,p_fixed,rfl⟩)

private def pairEquiv : Representation.Equiv pair (W.prod W.dual) where
  toLinearEquiv := (LinearEquiv.refl (ZMod 2) Vector).prodCongr graphNaturalDual.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · rfl
    · exact LinearMap.congr_fun (graphNaturalDual.isIntertwining' g) v.2

/-- Both marked fixed lines lie in the opposite flag commutator in the
semisimple natural-plus-dual model. -/
theorem flag_tests :
    fixedSpace (W.prod W.dual) lineParabolicSL ≤
      subspaceCommutator (W.prod W.dual) (fixedSpace (W.prod W.dual) borelSL) pointParabolicSL ∧
    fixedSpace (W.prod W.dual) pointParabolicSL ≤
      subspaceCommutator (W.prod W.dual) (fixedSpace (W.prod W.dual) borelSL) lineParabolicSL := by
  let e := pairEquiv
  have hfix (A : Subgroup Group) : (fixedSpace pair A).map e.toLinearMap = fixedSpace (W.prod W.dual) A := by
    simpa only [Subgroup.map_id] using fixedSpace_map_equivariant pair (W.prod W.dual)
      (MonoidHom.id Group) e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A
  have hcomm (A : Subgroup Group) :
      (subspaceCommutator pair (fixedSpace pair borelSL) A).map e.toLinearMap =
        subspaceCommutator (W.prod W.dual) (fixedSpace (W.prod W.dual) borelSL) A := by
    have hh := subspaceCommutator_map_embedding (W.prod W.dual) pair (MonoidHom.id Group)
      e.toLinearMap (fun g v => (LinearMap.congr_fun (e.isIntertwining' g) v).symm) A (fixedSpace pair borelSL)
    simpa only [Subgroup.map_id,hfix] using hh.symm
  constructor
  · rw [←hfix,←hcomm]
    exact Submodule.map_mono pair_tests.1
  · rw [←hfix,←hcomm]
    exact Submodule.map_mono pair_tests.2
end BinaryLinearThree.NaturalDualFlags
