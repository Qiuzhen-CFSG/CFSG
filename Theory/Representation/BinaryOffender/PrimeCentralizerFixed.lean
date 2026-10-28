module
public import Theory.Representation.BinaryOffender.FixedSpaceFaithfulness
public import Theory.Representation.BinaryOffender.RestrictedConstituent
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.ElementaryAbelian.Injective

/-!
# Fixed spaces of the kernel on a normal odd subgroup

For a faithful binary representation, an elementary two-subgroup B and a
normal odd p-subgroup R, put K = C_B(R). Thompson A×B makes R faithful on
C_V(K). Normality then makes the B-kernel on that space exactly K.
The resulting B-image has the same order as the literal conjugation image
on R, and is nontrivial whenever B moves R.

Source: Aschbacher–Smith A.1.18, used in the representation reduction of
14.5.11, printed pp.1015–1016, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The odd subgroup stays faithful and the elementary kernel is exactly its centralizer. -/
theorem prime_centralizer_fixed_kernel
    (hf : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (R B : Subgroup G) [R.Normal] [IsElementaryAbelian 2 B]
    (hR : IsPGroup p R) :
    let K := B ⊓ centralizer (R : Set G)
    let U := fixedSpace ρ K
    subspaceKernel ρ U R = ⊥ ∧ subspaceKernel ρ U B = K := by
  let K := B ⊓ centralizer (R : Set G)
  let U := fixedSpace ρ K
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_injective
    (inclusion (show K ≤ B from inf_le_left)) (inclusion_injective _)
  have hRK : ⁅R,K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mpr inf_le_right)
  have hRs := le_stabilizer_fixedSpace_of_commutator_eq_bot ρ R K hRK
  have hker := fixedSpace_primeGroup_kernel_eq_bot ρ hf hp R K hR
    (IsElementaryAbelian.isPGroup 2 K) hRK
  refine ⟨hker,le_antisymm ?_ ?_⟩
  · have hi := (subgroupActionHom_injective_iff ρ U R hRs).mpr hker
    have hfaith : Function.Injective (invariantSubspace ρ R U hRs).toRepresentation := by
      intro a b he
      apply hi
      apply subspaceImageRepresentation_injective ρ U
      exact he
    exact subspaceKernel_le_centralizer_of_faithful ρ R B U hRs hfaith
  · intro k hk
    exact ⟨hk.1,fun v hv => hv ⟨k,hk⟩⟩

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The fixed-space image and the conjugation image on the odd subgroup have equal order. -/
theorem prime_centralizer_fixed_image_card
    (hf : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (R B : Subgroup G) [R.Normal] [IsElementaryAbelian 2 B]
    (hR : IsPGroup p R) :
    let K := B ⊓ centralizer (R : Set G)
    let U := fixedSpace ρ K
    Nat.card (restrictedSubgroup ρ U B) =
      Nat.card (B.map (MulAut.conjNormal : G →* MulAut R)) := by
  let K := B ⊓ centralizer (R : Set G)
  let U := fixedSpace ρ K
  have hBs : B ≤ subspaceStabilizer ρ U :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ B K
      (commutator_eq_bot_iff_le_centralizer.mpr
        ((Subgroup.le_centralizer B).trans (centralizer_le inf_le_left)))
  have hc := card_subspaceKernel_mul_image ρ U B hBs
  rw [(prime_centralizer_fixed_kernel ρ hf hp R B hR).2] at hc
  have hr := relIndex_mul_relIndex (⊥ : Subgroup G) K B bot_le inf_le_left
  simp only [relIndex_bot_left] at hr
  have hi : K.relIndex B = Nat.card (B.map (MulAut.conjNormal : G →* MulAut R)) := by
    change (B ⊓ centralizer (R : Set G)).relIndex B = _
    rw [inf_relIndex_left,←MulAut.conjNormal_ker_eq_centralizer,relIndex_ker]
  rw [hi] at hr
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K)) (hc.trans hr.symm)

/-- Movement of the odd subgroup survives on the literal kernel-fixed space. -/
theorem prime_centralizer_fixed_image_nontrivial
    (hf : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (R B : Subgroup G) [R.Normal] [IsElementaryAbelian 2 B]
    (hR : IsPGroup p R) (hm : ¬ B ≤ centralizer (R : Set G)) :
    restrictedSubgroup ρ (fixedSpace ρ (B ⊓ centralizer (R : Set G))) B ≠ ⊥ := by
  intro he
  have hc := prime_centralizer_fixed_image_card ρ hf hp R B hR
  dsimp only at hc
  rw [he,card_bot] at hc
  have hz := (eq_bot_iff_card _).mpr hc.symm
  apply hm
  rw [←MulAut.conjNormal_ker_eq_centralizer]
  intro b hb
  have hh := mem_map_of_mem (MulAut.conjNormal : G →* MulAut R) hb
  rw [hz,mem_bot] at hh
  exact hh
end Representation.BinaryOffender
