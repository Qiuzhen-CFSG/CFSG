module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Centralizer

/-!
# The indices determined by the centralizer character

A character of the literal critical span whose restriction to the natural
kernel is its cofixed coordinate has a kernel supplementing that kernel.
If its kernel is the source relative centralizer, the centralizer meets
the natural kernel in the original critical intersection. The two source
indices are therefore q, by the actual root image of the opposite group.

The construction of the character from the point-Levi commutator pairing
is separate. No field restriction is assumed here.
-/

public noncomputable section
open Subgroup
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
variable {F G : Type*} [Field F] [Group G] [Finite G]
variable {κ : G →* Sp F} {A B : Subgroup G} (s : MarkedPair κ A B)

/-- The centralizer character determines both of the source order clauses. -/
theorem centralizer_indices_of_character
    (φ : (A ⊔ B : Subgroup G) →* Multiplicative F)
    (hφA : ∀ a : A, φ ⟨a,(show A ≤ A ⊔ B from le_sup_left) a.property⟩ = s.naturalLine a)
    (hφker : φ.ker =
      (commutatorPreimage (A ⊔ B) (pointRadicalAmbient.comap κ) ⁅A,B⁆).subgroupOf (A ⊔ B)) :
    let W := commutatorPreimage (A ⊔ B) (pointRadicalAmbient.comap κ) ⁅A,B⁆
    W ⊔ A = A ⊔ B ∧ W ⊓ A = A ⊓ B ∧
      (A ⊓ B).relIndex W = Nat.card F ∧ A.relIndex (W ⊔ A) = Nat.card F := by
  let C := A ⊔ B
  let W := commutatorPreimage C (pointRadicalAmbient.comap κ) ⁅A,B⁆
  have hWC : W ≤ C := commutatorPreimage_le _ _ _
  have hWA : W ⊔ A = C := by
    apply le_antisymm (sup_le hWC le_sup_left)
    intro x hx
    let xC : C := ⟨x,hx⟩
    obtain ⟨a,ha⟩ := s.naturalLine_onto (φ xC)
    let aC : C := ⟨a,(show A ≤ C from le_sup_left) a.property⟩
    have hwa : xC*aC⁻¹ ∈ φ.ker := by
      change φ (xC*aC⁻¹)=1
      rw [map_mul,map_inv,hφA a,ha,mul_inv_cancel]
    have hw' : xC*aC⁻¹ ∈ W.subgroupOf C := by rw [←hφker]; exact hwa
    have hw : x*a.val⁻¹ ∈ W := hw'
    have hh := (W ⊔ A).mul_mem (mem_sup_left hw) (mem_sup_right a.property)
    simpa only [inv_mul_cancel_right] using hh
  have hWI : W ⊓ A = A ⊓ B := by
    ext x
    constructor
    · rintro ⟨hw,ha⟩
      refine ⟨ha,?_⟩
      have hpx : φ ⟨x,(show A ≤ C from le_sup_left) ha⟩=1 :=
        show (⟨x,(show A ≤ C from le_sup_left) ha⟩ : C) ∈ φ.ker from hφker.symm ▸ hw
      have hlin : s.naturalLine ⟨x,ha⟩=1 := (hφA ⟨x,ha⟩).symm.trans hpx
      exact show (⟨x,ha⟩ : A) ∈ B.subgroupOf A from s.naturalLine_kernel ▸ hlin
    · rintro ⟨ha,hb⟩
      refine ⟨?_,ha⟩
      have hlin : s.naturalLine ⟨x,ha⟩=1 :=
        show (⟨x,ha⟩ : A) ∈ s.naturalLine.ker from s.naturalLine_kernel.symm ▸ hb
      have hpx : φ ⟨x,(show A ≤ C from le_sup_left) ha⟩=1 := (hφA ⟨x,ha⟩).trans hlin
      exact show (⟨x,(show A ≤ C from le_sup_left) ha⟩ : C) ∈ W.subgroupOf C from hφker ▸ hpx
  let : A.Normal := s.kernel ▸ inferInstance
  have hAC : A.relIndex C=Nat.card F := by
    change A.relIndex (A ⊔ B)=Nat.card F
    rw [relIndex_sup_left,←s.kernel,relIndex_ker,s.root_image,RootSubgroup.card]
  refine ⟨hWA,hWI,?_,by rw [hWA]; exact hAC⟩
  rw [←hWI,inf_relIndex_left,←relIndex_sup_right W A,hWA]
  exact hAC

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
