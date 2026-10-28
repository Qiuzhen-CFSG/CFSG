module
public import Theory.Representation.G2BinaryPointElementary
public import Theory.Representation.G2BinaryPointFlagDisplacement
public import Theory.Representation.BinaryOffender.SubspaceAction
/-!
# The normal elementary point-parabolic image fixes the seed

The literal three-root elementary subgroup fixes the marked three-space in
the natural module. Combined with the normal-image calculation, this gives
the pointwise action used to prove the smaller source closure abelian in
Aschbacher–Smith, Lemma 13.3.18, printed p.895.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.Explicit Subgroup

/-- Every element of the actual three-root image fixes the source seed. -/
theorem elementary_fixes_seed (g : Model F) (hg:g∈BinaryCore.elementary)
    (v:W) (hv:v∈seed) : Restricted.NaturalCoordinates.action F g v=v := by
  obtain ⟨x,hx,rfl⟩ := hg
  obtain ⟨v3,v4,v5⟩ := (mem_seed v).mp hv
  change Restricted.NaturalCoordinates.action F
    (unipotentProduct (BinaryCore.parameters x)) v=v
  simp only [unipotentProduct,map_mul,Module.End.mul_apply,
    action_rootA,action_rootB,action_rootC,action_rootD,action_rootE,action_rootF]
  ext i
  fin_cases i <;> simp [BinaryCore.parameters,hx.1,hx.2,v3,v4,v5]

/-- The normal elementary source image centralizes V₃. -/
theorem elementary_normalized_point_fixes_seed (A : Subgroup (Model F))
    [IsElementaryAbelian 2 A] (hA:A≤unipotent)
    (hn:BinaryParabolicPair.derivedSecondAmbient≤normalizer (A:Set (Model F)))
    (g:Model F) (hg:g∈A) (v:W) (hv:v∈seed) :
    Restricted.NaturalCoordinates.action F g v=v :=
  elementary_fixes_seed g (elementary_normalized_point_le A hA hn hg) v hv
end Atlas.G2.Natural.BinaryPointFlag
