module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Conjugation displacement on an abelian subgroup

The map r ↦ [r,v] is a homomorphism when v normalizes an abelian R.
For an involution its image is the literal cyclic commutator. Commuting
conjugation actions make this homomorphism equivariant. This is the
linear-section calculation used in Aschbacher--Smith 12.2.25, p.805.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup.ConjugationDisplacement
variable {G : Type*} [Group G] (R : Subgroup G) [IsMulCommutative R]

/-- The displacement of the actual normalizer element, with codomain R. -/
def hom (v : normalizer (R : Set G)) : R →* R :=
  MonoidHom.id R * (R.normalizerMonoidHom v).toMonoidHom⁻¹

@[simp] theorem hom_apply (v : normalizer (R : Set G)) (r : R) :
    (hom R v r : G) = ⁅(r : G),(v : G)⁆ := by
  change (r : G) * ((v : G) * (r : G) * (v : G)⁻¹)⁻¹ = _
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]

/-- Its kernel is the centralizer of the chosen element inside R. -/
theorem ker (v : normalizer (R : Set G)) :
    (hom R v).ker = (centralizer ({(v : G)} : Set G)).subgroupOf R := by
  ext r
  rw [MonoidHom.mem_ker, ← Subtype.val_inj, hom_apply]
  change ⁅(r : G),(v : G)⁆ = 1 ↔ (r : G) ∈ centralizer ({(v : G)} : Set G)
  rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]

/-- For an involution the image is the whole cyclic commutator subgroup. -/
theorem range (v : normalizer (R : Set G)) (hv : (v : G) ^ 2 = 1) :
    ((hom R v).range).map R.subtype = ⁅R,zpowers (v : G)⁆ := by
  apply le_antisymm
  · rintro x ⟨r,⟨s,rfl⟩,rfl⟩
    change (hom R v s : G) ∈ ⁅R,zpowers (v : G)⁆
    rw [hom_apply]
    exact commutator_mem_commutator s.property (mem_zpowers _)
  · apply commutator_le.mpr
    intro r hr x hx
    have hx2 : x = 1 ∨ x = (v : G) := by
      by_cases hv1 : (v : G) = 1
      · left
        simpa [hv1] using hx
      · have hc : Nat.card (zpowers (v : G)) = 2 := by
          rw [Nat.card_zpowers, orderOf_eq_prime hv hv1]
        obtain ⟨a,ha,hu⟩ := (Nat.card_eq_two_iff' (1 : zpowers (v : G))).mp hc
        by_cases hx1 : x = 1
        · exact Or.inl hx1
        · right
          exact congrArg Subtype.val ((hu ⟨x,hx⟩ (fun he => hx1 (congrArg Subtype.val he))).trans
            (hu ⟨v,mem_zpowers _⟩ (fun he => hv1 (congrArg Subtype.val he))).symm)
    rcases hx2 with rfl | rfl
    · simp
    · exact ⟨hom R v ⟨r,hr⟩,⟨⟨r,hr⟩,rfl⟩,hom_apply R v ⟨r,hr⟩⟩

/-- Commuting normalizer actions intertwine their actual displacement. -/
theorem equivariant (v y : normalizer (R : Set G))
    (hc : Commute (R.normalizerMonoidHom v) (R.normalizerMonoidHom y)) (r : R) :
    hom R v (R.normalizerMonoidHom y r) = R.normalizerMonoidHom y (hom R v r) := by
  have hc' := MulEquiv.congr_fun hc.eq r
  change R.normalizerMonoidHom v (R.normalizerMonoidHom y r) =
    R.normalizerMonoidHom y (R.normalizerMonoidHom v r) at hc'
  change R.normalizerMonoidHom y r *
    (R.normalizerMonoidHom v (R.normalizerMonoidHom y r))⁻¹ =
    R.normalizerMonoidHom y (r * (R.normalizerMonoidHom v r)⁻¹)
  rw [hc',map_mul,map_inv]

end Subgroup.ConjugationDisplacement
