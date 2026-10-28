module
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic

/-!
# Full diagonal coordinates for opposite-root Cartans

A matrix normalizing the upper and lower root groups is diagonal. An
injective Cartan image of order |F|-1 therefore exhausts that diagonal
subgroup, in the same coordinates as the two prescribed roots. The proof
uses the upper-left entry and finite cardinality; it applies in every
characteristic.

The commuting elementary DGS application retains its original local map
and uses these full coordinates to compare the cubic braid with its chosen
apartment reflection. Source: DGS, Groups and Graphs (1985), (14.3)(b),
p.212, and the exchange argument (14.11)--(14.12), p.217.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
open Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
variable {F E : Type*} [Field F] [Finite F] [Group E]

omit [Finite F] in
/-- Opposite root normalizers have diagonal matrices. -/
theorem diagonal_of_normalizes_opposite (g : SL(2,F))
    (hu : g∈normalizer (upperUnipotent F : Set SL(2,F)))
    (hl : ∃ b : F, g*lower 1*g⁻¹=lower b) :
    ∃ a : F, ∃ ha : a≠0, g=diag2 a ha := by
  have h10 := (mem_rankOneBorel_iff g).mp hu
  obtain ⟨b,hb⟩ := hl
  have he : g*lower 1=lower b*g := (mul_inv_eq_iff_eq_mul).mp hb
  have h01 : g.val 0 1=0 := by
    have hh := congrArg (fun z : SL(2,F) => z.val 0 0) he
    simpa [lower,coe_mul,transvection_coe,Matrix.mul_apply,Fin.sum_univ_two] using hh
  have hd : g.val 0 0*g.val 1 1=1 := by
    simpa only [det_fin_two,h10,mul_zero,sub_zero] using g.property
  have ha := left_ne_zero_of_mul_eq_one hd
  refine ⟨g.val 0 0,ha,?_⟩
  have h11 : g.val 1 1=(g.val 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2_coe',h10,h01,h11]

/-- A full-sized complement normalizing the same opposite roots fills their
actual diagonal torus, without a new change of coordinates. -/
theorem full_diagonal_image_of_opposite_roots (f : E →* SL(2,F))
    (R V C : Subgroup E)
    (hR : R.map f=upperUnipotent F)
    (hV : ∀ y : SL(2,F), y∈V.map f ↔ ∃ a : F, lower a=y)
    (hCR : C ≤ normalizer (R : Set E)) (hCV : C ≤ normalizer (V : Set E))
    (hi : Function.Injective (f.comp C.subtype))
    (hc : Nat.card C=Nat.card F-1) :
    ∀ a : F, ∀ ha : a≠0, diag2 a ha∈C.map f := by
  have hB (x : C) : f x∈rankOneBorel F := by
    rw [rankOneBorel,←hR]
    exact R.le_normalizer_map f (mem_map_of_mem f (hCR x.property))
  let d : C → Fˣ := fun x => Units.mk0 ((f x).val 0 0) (by
    have hd : (f x).val 0 0*(f x).val 1 1=1 := by
      simpa only [det_fin_two,(mem_rankOneBorel_iff _).mp (hB x),mul_zero,sub_zero]
        using (f x).property
    exact left_ne_zero_of_mul_eq_one hd)
  have hdiag (x : C) : f x=diag2 (d x : F) (d x).ne_zero := by
    obtain ⟨a,ha,he⟩ := diagonal_of_normalizes_opposite (f x) (hB x) (by
      have hm : lower 1∈V.map f := (hV _).mpr ⟨1,rfl⟩
      have hn := V.le_normalizer_map f (mem_map_of_mem f (hCV x.property))
      obtain ⟨a,ha⟩ := (hV _).mp ((mem_normalizer_iff.mp hn _).mp hm)
      exact ⟨a,ha.symm⟩)
    have he00 : (d x : F)=a := by
      change (f x).val 0 0=a
      rw [he]
      simp [diag2_coe']
    simpa only [he00] using he
  have hdi : Function.Injective d := by
    intro x y hxy
    apply hi
    change f x=f y
    rw [hdiag,hdiag,hxy]
  have hdonto : Function.Surjective d :=
    ((Nat.bijective_iff_injective_and_card d).mpr ⟨hdi,by rw [hc,Nat.card_units]⟩).2
  intro a ha
  obtain ⟨x,hx⟩ := hdonto (Units.mk0 a ha)
  refine ⟨x,x.property,?_⟩
  simpa only [hx,Units.val_mk0] using hdiag x

end Matrix.SpecialLinearGroup
