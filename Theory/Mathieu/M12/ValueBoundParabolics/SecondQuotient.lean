module
public import Theory.Mathieu.M12.SmallParabolicPair

/-!
# The second M₁₂ parabolic's intrinsic two-core quotient

The normalizer of the marked natural four acts on its three nonidentity
members. The moving cubic and a quaternion generator induce a three-cycle
and a transposition, so this action is onto S₃. Since the normalizer has
order 192, the action kernel is exactly its intrinsic two-core.

The restriction construction follows the corresponding local action in
`Stellmacher.SectionNine.NineFiveM12LocalActions`, with the marked elements
from `M12.SmallParabolicPair` and its existing order calculation.
Source: Aschbacher–Smith, E.4.3(1), printed p.241 (PDF p.252).
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
open FirstCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def naturalLabel : Fin 3 → M12 := ![z, v, z * v]

theorem naturalLabel_injective : Function.Injective naturalLabel := by decide +kernel

theorem mem_natural_iff_label (g : M12) :
    g ∈ natural ↔ g = 1 ∨ ∃ i, g = naturalLabel i := by
  rw [mem_natural]
  simp [naturalLabel, Fin.exists_fin_succ]

def naturalRepresentation : secondParabolic →* Equiv.Perm M12 :=
  conjugationPermHom.comp secondParabolic.subtype

theorem natural_stable (g : secondParabolic) (i : Fin 3) :
    ∃ j, naturalRepresentation g (naturalLabel i) = naturalLabel j := by
  have hi : naturalLabel i ∈ natural :=
    (mem_natural_iff_label _).mpr (Or.inr ⟨i, rfl⟩)
  have hm := (Subgroup.mem_set_normalizer_iff.mp g.property (naturalLabel i)).mp hi
  rcases (mem_natural_iff_label _).mp hm with he | he
  · have hn : ∀ i, naturalLabel i ≠ 1 := by decide +kernel
    exact (hn i ((MulAut.conj (g : M12)).injective
      (he.trans (map_one (MulAut.conj (g : M12))).symm))).elim
  · exact he

/-- Conjugation on the three nonidentity elements of the marked normal four. -/
def secondQuotientMap : secondParabolic →* Equiv.Perm (Fin 3) :=
  restrictAction naturalRepresentation naturalLabel naturalLabel_injective natural_stable

theorem secondQuotientMap_eq (g : secondParabolic) (s : Equiv.Perm (Fin 3))
    (h : ∀ i, (g : M12) * naturalLabel i * (g : M12)⁻¹ = naturalLabel (s i)) :
    secondQuotientMap g = s := by
  apply Equiv.ext
  intro i
  apply naturalLabel_injective
  exact (restrictAction_spec naturalRepresentation naturalLabel naturalLabel_injective
    natural_stable g i).symm.trans (h i)

theorem secondQuotientMap_surjective : Function.Surjective secondQuotientMap := by
  have hl : leftI ∈ secondParabolic :=
    (core_le_sylowCandidate ((mem_core _).mpr ⟨.a 1, .a 0, by decide +kernel⟩)).2
  apply surjective_of_two_images secondQuotientMap
    ⟨movingActor, movingActor_mem⟩ ⟨leftI, hl⟩
    (List.formPerm [0, 1, 2]) (Equiv.swap 1 2)
  · apply secondQuotientMap_eq
    decide +kernel
  · apply secondQuotientMap_eq
    change ∀ i, leftI * naturalLabel i * leftI⁻¹ = naturalLabel ((Equiv.swap 1 2) i)
    decide +kernel
  · decide +kernel

theorem second_pCore_eq_kernel : pCore 2 secondParabolic = secondQuotientMap.ker :=
  core_eq_ker_of_surjective_perm_three card_secondParabolic
    secondQuotientMap secondQuotientMap_surjective

/-- The quotient is by the intrinsic two-core of the actual normalizer. -/
def secondCoreQuotient : secondParabolic ⧸ pCore 2 secondParabolic ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq second_pCore_eq_kernel).trans
    (QuotientGroup.quotientKerEquivOfSurjective secondQuotientMap secondQuotientMap_surjective)

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
