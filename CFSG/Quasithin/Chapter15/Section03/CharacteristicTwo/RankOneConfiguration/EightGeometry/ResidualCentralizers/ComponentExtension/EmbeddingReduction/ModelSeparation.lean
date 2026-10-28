module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.BinaryLinear.SylowCenters

/-!
# Distinguishing the two simple groups of order 20160

The upper unitriangular subgroup of SL₃(F₄) injects into PSL₃(F₄), has order
64, and has center of order four. It is therefore a Sylow two-subgroup.
In contrast, the proved binary-linear Sylow center bound is at most two
for PSL₄(F₂). The actual A₈–PSL₄(F₂) equivalence transfers that obstruction.
This is the model distinction needed in A.3.12(13) for 15.3.32(3), printed
p.1133; comparing orders alone would not exclude this branch.

Adapted from ATLAS `LinearGroups/UpperUnitriangularThree.lean`,
`LinearGroups/UnitriangularThreeProjective.lean`, and
`Comparisons/Exceptional/Order20160Nonisomorphism.lean`. The binary-four
calculation reuses the existing CFSG theorem in `BinaryLinear.SylowCenters`.
-/

noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.ModelSeparation.UnitriangularThree
open Matrix
open scoped MatrixGroups
variable (F : Type*) [Field F]

def mat (v : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  !![1,v 0,v 2;0,1,v 1;0,0,1]

def element (v : Fin 3 → F) : SL(3,F) := ⟨mat F v, by simp [mat, Matrix.det_fin_three]⟩

def product (v w : Fin 3 → F) : Fin 3 → F := ![v 0+w 0, v 1+w 1, v 2+w 2+v 0*w 1]
def inverse (v : Fin 3 → F) : Fin 3 → F := ![-v 0,-v 1,v 0*v 1-v 2]

theorem element_injective : Function.Injective (element F) := by
  intro v w h
  have h0 := congrArg (fun g : SL(3,F) => g.val 0 1) h
  have h1 := congrArg (fun g : SL(3,F) => g.val 1 2) h
  have h2 := congrArg (fun g : SL(3,F) => g.val 0 2) h
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem element_zero : element F 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [element,mat]

theorem element_mul (v w : Fin 3 → F) : element F v * element F w = element F (product F v w) := by
  apply Subtype.ext
  change mat F v * mat F w = mat F (product F v w)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat,product,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem element_inv (v : Fin 3 → F) : (element F v)⁻¹ = element F (inverse F v) := by
  apply inv_eq_of_mul_eq_one_right
  rw [element_mul, ← element_zero F]
  congr 1
  funext i
  fin_cases i <;> simp [product,inverse]

def subgroup : Subgroup SL(3,F) where
  carrier := Set.range (element F)
  one_mem' := ⟨0,element_zero F⟩
  mul_mem' := by rintro a b ⟨v,rfl⟩ ⟨w,rfl⟩; exact ⟨product F v w,(element_mul F v w).symm⟩
  inv_mem' := by rintro a ⟨v,rfl⟩; exact ⟨inverse F v,(element_inv F v).symm⟩

def member (v : Fin 3 → F) : subgroup F := ⟨element F v,⟨v,rfl⟩⟩
theorem member_injective : Function.Injective (member F) := fun _ _ h =>
  element_injective F (congrArg Subtype.val h)
theorem member_surjective : Function.Surjective (member F) := by
  rintro ⟨g,v,hv⟩
  exact ⟨v,Subtype.ext hv⟩

def parameterEquiv : (Fin 3 → F) ≃ subgroup F :=
  Equiv.ofBijective (member F) ⟨member_injective F,member_surjective F⟩

theorem card [Finite F] : Nat.card (subgroup F) = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (parameterEquiv F),Nat.card_fun,Nat.card_fin]

theorem member_mul (v w : Fin 3 → F) : member F v * member F w = member F (product F v w) :=
  Subtype.ext (element_mul F v w)

theorem member_center_iff (v : Fin 3 → F) : member F v ∈ Subgroup.center (subgroup F) ↔
    v 0 = 0 ∧ v 1 = 0 := by
  constructor
  · intro h
    have hc := Subgroup.mem_center_iff.mp h
    have h0 := congrArg (fun g : subgroup F => g.val.val 0 2) (hc (member F ![0,1,0]))
    have h1 := congrArg (fun g : subgroup F => g.val.val 0 2) (hc (member F ![1,0,0]))
    rw [member_mul,member_mul] at h0 h1
    simp [member,element,mat,product] at h0 h1
    exact ⟨h0,h1⟩
  · rintro ⟨h0,h1⟩
    apply Subgroup.mem_center_iff.mpr
    intro g
    obtain ⟨w,rfl⟩ := member_surjective F g
    rw [member_mul,member_mul]
    congr 1
    funext i
    fin_cases i <;> simp [product,h0,h1]
    ring

def central (c : F) : Subgroup.center (subgroup F) :=
  ⟨member F ![0,0,c], (member_center_iff F _).mpr ⟨rfl,rfl⟩⟩

def centerEquiv : F ≃ Subgroup.center (subgroup F) := Equiv.ofBijective (central F) (by
  constructor
  · intro c d h
    exact congrArg (fun g : Subgroup.center (subgroup F) => g.val.val.val 0 2) h
  · intro g
    obtain ⟨v,hv⟩ := member_surjective F g.val
    have hp := (member_center_iff F v).mp (hv.symm ▸ g.property)
    refine ⟨v 2,?_⟩
    apply Subtype.ext
    rw [←hv]
    apply congrArg (member F)
    funext i
    fin_cases i <;> simp [hp.1,hp.2])

theorem center_card : Nat.card (Subgroup.center (subgroup F)) = Nat.card F :=
  (Nat.card_congr (centerEquiv F)).symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.ModelSeparation.UnitriangularThree

noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.ModelSeparation.UnitriangularThree
open Matrix
open scoped MatrixGroups
variable (F : Type*) [Field F]

def projective : subgroup F →* PSL(3,F) :=
  (QuotientGroup.mk' (Subgroup.center SL(3,F))).comp (subgroup F).subtype

theorem projective_injective : Function.Injective (projective F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro g hg
  have hc : g.val ∈ Subgroup.center SL(3,F) :=
    (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨r,hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  obtain ⟨v,hv⟩ := member_surjective F g
  subst g
  have hd := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) he
  have hr1 : r = 1 := by simpa [member,element,mat,Matrix.scalar_apply] using hd
  change member F v = 1
  apply Subtype.ext
  apply Subtype.ext
  simpa [hr1] using he.symm

variable [Finite F]
theorem psl3_card_four (hF : Nat.card F = 4) : Nat.card PSL(3,F) = 20160 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at h
  norm_num [Fin.prod_univ_succ] at h
  omega

theorem projective_range_card : Nat.card (projective F).range = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (projective_injective F)).toEquiv,card]

local instance unitriangularThreePrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

def sylowTwo (hF : Nat.card F = 4) : Sylow 2 PSL(3,F) :=
  Sylow.ofCard (projective F).range (by
    rw [projective_range_card,hF,psl3_card_four F hF]
    decide +kernel)

def sylowModelEquiv (hF : Nat.card F = 4) : subgroup F ≃* sylowTwo F hF :=
  MonoidHom.ofInjective (projective_injective F)

theorem sylowTwo_card (hF : Nat.card F = 4) : Nat.card (sylowTwo F hF) = 64 := by
  rw [← Nat.card_congr (sylowModelEquiv F hF).toEquiv,card,hF]
  norm_num

theorem sylowTwo_center_card (hF : Nat.card F = 4) :
    Nat.card (Subgroup.center (sylowTwo F hF)) = 4 := by
  rw [← Nat.card_congr (Subgroup.centerCongr (sylowModelEquiv F hF)).toEquiv,center_card,hF]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.ModelSeparation.UnitriangularThree

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.ModelSeparation
open scoped MatrixGroups

/-- A₈ and PSL₃(F₄) have different Sylow two-center orders. -/
public theorem alt8_not_equiv_psl3Card4 {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) :
    ¬ Nonempty (alternatingGroup (Fin 8) ≃* PSL(3,F)) := by
  rintro ⟨e⟩
  let f := e.symm.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two
  let S := UnitriangularThree.sylowTwo F hF
  have h := BinaryLinear.psl_sylow_center_card_le_two (by decide : 2 ≤ 4)
    (S.mapSurjective (f := f.toMonoidHom) f.surjective)
  rw [← BinaryLinear.sylow_center_card_congr f S,
    UnitriangularThree.sylowTwo_center_card] at h
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.ModelSeparation
