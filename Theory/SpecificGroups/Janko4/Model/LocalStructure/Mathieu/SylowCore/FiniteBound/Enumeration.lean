module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FixedCoordinates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowCard

/-!
# Enumerating the literal star Sylow candidate

The existing Schreier certificate has transversals of lengths 16, 8, and 8.
Their products are distinct: evaluating successively at points 0, 1, and 2
recovers the three transversal indices. The certified order 1024 therefore
makes these products a bijection onto `sylowCandidate`.

This is an enumeration of the actual permutation subgroup, with membership
proved from the original four generators. No alternative group model or
representation is introduced. The transversals and ATLAS word provenance are
in `QuotientInvolutions.SylowCard` and `QuotientInvolutions.SylowData`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
open Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions
open Simplicity.Max1Fusion.QuotientInvolutions.SylowCardCertificate
open Theory.GroupTheory

/-- Stabilizer-chain coordinates, of cardinality 16 * 8 * 8. -/
abbrev Index := Fin 16 × Fin 8 × Fin 8

/-- The literal product of the three certified transversals. -/
def perm (i : Index) : Equiv.Perm (Fin 24) := rep0 i.1 * rep1 i.2.1 * rep2 i.2.2

private theorem group0_le_image : group0 ≤ sylowCandidate.map StarGroup.subtype := by
  rintro g ⟨w, rfl⟩
  induction w with
  | nil => exact (sylowCandidate.map StarGroup.subtype).one_mem
  | cons i w ih =>
    apply (sylowCandidate.map StarGroup.subtype).mul_mem _ ih
    exact ⟨sylowGenerator i, Subgroup.subset_closure ⟨i, rfl⟩,
      (congrFun gen0_eq i).symm⟩

private theorem perm_mem_image (i : Index) :
    perm i ∈ sylowCandidate.map StarGroup.subtype := by
  apply group0_le_image
  exact group0.mul_mem (group0.mul_mem ⟨repWords0 i.1, rfl⟩
    (inclusion1 ⟨repWords1 i.2.1, rfl⟩))
    (inclusion1 (inclusion2 ⟨repWords2 i.2.2, rfl⟩))

private theorem perm_mem_star (i : Index) : perm i ∈ StarGroup := by
  rcases perm_mem_image i with ⟨g, _, hg⟩
  rw [← hg]
  exact g.property

private theorem perm_mem_candidate (i : Index) :
    (⟨perm i, perm_mem_star i⟩ : StarGroup) ∈ sylowCandidate := by
  rcases perm_mem_image i with ⟨g, hg, heq⟩
  have : g = ⟨perm i, perm_mem_star i⟩ := Subtype.ext heq
  exact this ▸ hg

/-- The same product as an element of the original candidate subgroup. -/
def element (i : Index) : sylowCandidate :=
  ⟨⟨perm i, by exact perm_mem_star i⟩, by exact perm_mem_candidate i⟩

@[simp] theorem element_val (i : Index) : (element i).val.val = perm i := rfl

/-- The faithful literal permutation map, for transporting group identities
without unfolding the transversal tables during abstract proofs. -/
def permHom : sylowCandidate →* Equiv.Perm (Fin 24) :=
  StarGroup.subtype.comp sylowCandidate.subtype

@[simp] theorem permHom_element (i : Index) : permHom (element i) = perm i := rfl

private theorem rep0_point : ∀ i, rep0 i 0 = point0 i := by decide +kernel
private theorem rep1_point : ∀ i, rep1 i 1 = point1 i := by decide +kernel
private theorem rep2_point : ∀ i, rep2 i 2 = point2 i := by decide +kernel
private theorem rep1_fix0 : ∀ i, rep1 i 0 = 0 := by decide +kernel
private theorem rep2_fix0 : ∀ i, rep2 i 0 = 0 := by decide +kernel
private theorem rep2_fix1 : ∀ i, rep2 i 1 = 1 := by decide +kernel
private theorem point0_inj : Function.Injective point0 := by decide +kernel
private theorem point1_inj : Function.Injective point1 := by decide +kernel
private theorem point2_inj : Function.Injective point2 := by decide +kernel

theorem perm_injective : Function.Injective perm := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  have had : a = d := by
    apply point0_inj
    have := congrArg (fun p : Equiv.Perm (Fin 24) => p 0) h
    simpa [perm, Equiv.Perm.mul_apply, rep2_fix0, rep1_fix0, rep0_point] using this
  subst d
  have htail : rep1 b * rep2 c = rep1 e * rep2 f := by
    exact mul_left_cancel (by simpa only [perm, mul_assoc] using h)
  have hbe : b = e := by
    apply point1_inj
    have := congrArg (fun p : Equiv.Perm (Fin 24) => p 1) htail
    simpa [Equiv.Perm.mul_apply, rep2_fix1, rep1_point] using this
  subst e
  have hcf : c = f := by
    apply point2_inj
    have := congrArg (fun p : Equiv.Perm (Fin 24) => p 2) (mul_left_cancel htail)
    simpa only [rep2_point] using this
  subst f
  rfl

theorem element_injective : Function.Injective element := by
  intro i j h
  exact perm_injective (congrArg (fun g : sylowCandidate => g.val.val) h)

theorem element_bijective : Function.Bijective element := by
  apply (Nat.bijective_iff_injective_and_card element).mpr
  exact ⟨element_injective, by simp [sylowCandidate_card]⟩

/-- The complete enumeration, proved using the existing order certificate. -/
noncomputable def enumeration : Index ≃ sylowCandidate :=
  Equiv.ofBijective element element_bijective

@[simp] theorem enumeration_apply (i : Index) : enumeration i = element i := rfl

@[simp] theorem element_enumeration_symm (g : sylowCandidate) :
    element (enumeration.symm g) = g := enumeration.apply_symm_apply g

def identityIndex : Index := (0, 0, 0)

@[simp] theorem element_identityIndex : element identityIndex = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem element_eq_one_iff (i : Index) : element i = 1 ↔ i = identityIndex := by
  rw [← element_identityIndex]
  exact element_injective.eq_iff

end Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
