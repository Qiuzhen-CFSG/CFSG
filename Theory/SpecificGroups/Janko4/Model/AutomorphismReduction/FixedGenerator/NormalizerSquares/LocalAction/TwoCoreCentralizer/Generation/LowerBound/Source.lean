module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Conjugacy

/-!
# Source words for the max2 lower bound

The actors here belong to the literal closure of the two unchanged ATLAS
outputs. Thirteen prescribed factors are the square of `(XYXYY)^11` and
twelve conjugates of that word. If the 8192 binary products are distinct,
every homomorphism killing the seed has a kernel of order at least 8192.
Distinctness is a separate matrix certificate, not an assumption about a
normal closure or an extraspecial group.

The conjugating words come from `LowerBound/source/lower_candidate.json`,
copied from `Scratch/J4Max2Generation/` in the retained parent workspace.
The ATLAS program and attribution are in `TwoCoreCentralizer/source/`.
GLS3, Table 5.3i, printed p.270, motivates the numerical target only.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
namespace LowerBound

/-- The first original ATLAS output in its generated subgroup. -/
def sourceX : sourceSubgroup :=
  ⟨w10, Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- The second original ATLAS output in its generated subgroup. -/
def sourceY : sourceSubgroup :=
  ⟨w14, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

/-- The source word whose square is the certified word involution. -/
def sourceSeed : sourceSubgroup :=
  (sourceX * sourceY * sourceX * sourceY * sourceY) ^ 11

@[simp] theorem coe_sourceX : (sourceX : Model) = w10 := rfl
@[simp] theorem coe_sourceY : (sourceY : Model) = w14 := rfl

theorem coe_sourceSeed_sq : ((sourceSeed ^ 2 : sourceSubgroup) : Model) = t := by
  change ((w10 * w14 * w10 * w14 * w14) ^ 11) ^ 2 = t
  rw [← pow_mul]
  rfl

/-- The twelve positive words used to conjugate the seed, in witness order. -/
def kernelConjugators : Vector sourceSubgroup 12 :=
  let y2 := sourceY * sourceY
  let y2x := y2 * sourceX
  let y2xy := y2x * sourceY
  let y2xyx := y2xy * sourceX
  let y2xyy := y2xy * sourceY
  let y2xyxy := y2xyx * sourceY
  let y2xyyx := y2xyy * sourceX
  #v[1, sourceY, y2, y2x, y2xy, y2xyx, y2xyy, y2xyxy, y2xyyx,
    y2xyxy * sourceX, y2xyxy * sourceY, y2xyyx * sourceY]

/-- Factor zero is the involution; the remaining factors are conjugates of the seed. -/
def kernelFactor : Fin 13 → sourceSubgroup :=
  Fin.cases (sourceSeed ^ 2) (fun i =>
    (kernelConjugators.get i)⁻¹ * sourceSeed * kernelConjugators.get i)

/-- Increasing bit positions give the multiplication order of the saved first rows. -/
def kernelProduct (i : Fin 8192) : sourceSubgroup :=
  (List.ofFn (fun j : Fin 13 => if i.val.testBit j.val then kernelFactor j else 1)).prod

theorem map_kernelFactor_eq_one {G : Type*} [Group G]
    (f : sourceSubgroup →* G) (hs : f sourceSeed = 1) (j : Fin 13) :
    f (kernelFactor j) = 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [kernelFactor, hs]
  · simp [kernelFactor, hs]

theorem map_kernelProduct_eq_one {G : Type*} [Group G]
    (f : sourceSubgroup →* G) (hs : f sourceSeed = 1) (i : Fin 8192) :
    f (kernelProduct i) = 1 := by
  rw [kernelProduct, map_list_prod, List.map_ofFn]
  apply List.prod_eq_one
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  dsimp only [Function.comp_apply]
  split_ifs
  · exact map_kernelFactor_eq_one f hs j
  · exact f.map_one

attribute [local irreducible] kernelProduct

/-- A first-row distinctness certificate suffices for the entire kernel lower bound. -/
theorem kernel_card_ge_of_injective
    (hinj : Function.Injective kernelProduct)
    {G : Type*} [Group G] (f : sourceSubgroup →* G) (hs : f sourceSeed = 1) :
    8192 ≤ Nat.card f.ker := by
  let e : Fin 8192 → f.ker := fun i =>
    ⟨kernelProduct i, map_kernelProduct_eq_one f hs i⟩
  have he : Function.Injective e := by
    intro i j hij
    exact @hinj i j (congrArg (fun z : f.ker => (z : sourceSubgroup)) hij)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective e he

end LowerBound
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
