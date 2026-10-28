module
public import Theory.SpecificGroups.SymmetricFourWreath.Planes
public import Theory.GroupTheory.Gaschutz
/-!
# A complement to the marked elementary subgroup in the wreath Sylow

The opposite reflections complement each coordinate four-group. Including
both reflections and the pure swap gives an actual complement to B inside
D₈ wr C₂. This is the local input to Gaschütz splitting of the original
normalizer in Aschbacher–Smith 13.9.10 (printed p.973).
-/

public section
namespace SymmetricFourWreath
open Subgroup

private def reflectionLine : Subgroup D8 where
  carrier := {x | x=1 ∨ x=DihedralGroup.sr 1}
  one_mem' := Or.inl rfl
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

/-- A complement formed by the opposite reflections and the pure swap. -/
def planeComplement : Subgroup P where
  carrier := {x | ∀ i, x.left i ∈ reflectionLine}
  one_mem' := fun _ => reflectionLine.one_mem
  mul_mem' := by
    intro x y hx hy i
    exact reflectionLine.mul_mem (hx i) (hy (x.right⁻¹*i))
  inv_mem' := by
    intro x hx i
    exact reflectionLine.inv_mem (hx (x.right*i))

private instance : DecidablePred (· ∈ reflectionLine) := fun x =>
  inferInstanceAs (Decidable (x=1 ∨ x=DihedralGroup.sr 1))

private theorem elementaryInP_mem (x : P) :
    x ∈ elementaryInP false false ↔ x.right=1 ∧ ∀i,x.left i∈plane false := by
  constructor
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    refine ⟨rfl,fun i=>?_⟩
    change (if i=1 then a else b)∈plane false
    split <;> assumption
  · rintro ⟨hr,hl⟩
    refine ⟨(x.left 1,x.left turn),⟨hl _,hl _⟩,?_⟩
    apply RegularWreathProduct.ext
    · funext i
      have hi : i=1 ∨ i=turn := by
        exact (by decide +kernel : ∀i:C2,i=1 ∨ i=turn) i
      rcases hi with rfl | rfl <;> simp [pair,turn_ne_one]
    · exact hr.symm

/-- The literal marked elementary sixteen splits in the dihedral wreath Sylow. -/
theorem elementaryInP_complement : (elementaryInP false false).IsComplement' planeComplement := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    intro x hx hy
    obtain ⟨hr,hl⟩ := (elementaryInP_mem x).mp hx
    apply RegularWreathProduct.ext
    · funext i
      exact (by decide +kernel : ∀a:D8,a∈plane false → a∈reflectionLine → a=1) _ (hl i) (hy i)
    · exact hr
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    have hd : ∀a:D8,∃b∈plane false,∃c∈reflectionLine,a=b*c := by decide +kernel
    choose b hb c hc he using fun i=>hd (x.left i)
    let y : P := ⟨b,1⟩
    let z : P := ⟨c,x.right⟩
    refine ⟨y,(elementaryInP_mem y).mpr ⟨rfl,hb⟩,z,hc,?_⟩
    apply RegularWreathProduct.ext
    · funext i
      change b i*c (1⁻¹*i)=x.left i
      simpa only [inv_one,one_mul] using (he i).symm
    · exact one_mul _

end SymmetricFourWreath
