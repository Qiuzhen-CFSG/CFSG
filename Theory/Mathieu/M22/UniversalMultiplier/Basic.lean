module

public import Theory.Mathieu.M22.TripleCover.Recognition
public import Theory.GroupTheory.CoveringKernelCard
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The genuine cubic quotient of the M₂₂ multiplier

The native Mathieu group is perfect as the image of the certified perfect
matrix triple cover, and its proved simplicity makes it quasisimple. Package
the actual triple-cover projection in the finite quasisimple covering API.
Universality gives a surjective commuting triangle, so its order-three
kernel is a quotient of the universal kernel.

This proves the cubic lower bound needed for Aschbacher–Smith I.1.3(4),
printed p.407. It makes no assertion about the missing two-primary part.
-/

namespace Sporadic.Mathieu.M22UniversalMultiplier
open Theory.GroupTheory

/-- Quasisimplicity of the literal Steiner-design M₂₂. -/
public instance m22Quasisimple : IsQuasisimple M22 := by
  let g := M22TripleCover.coverOfCentralQuotientEquiv M22TripleCover.centralQuotientEquiv
  let : Group.IsPerfect M22 := Group.IsPerfect.ofSurjective g.surjective
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  have hcenter : Subgroup.center M22 = ⊥ := by
    rcases (inferInstance : (Subgroup.center M22).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative M22
        (Subgroup.center_eq_top_iff.mp h)).elim
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
    QuotientGroup.quotientBot).isSimpleGroup }

/-- The genuine matrix triple cover, with its specified projection to M₂₂. -/
@[expose] public noncomputable def tripleCovering : Covering M22TripleCover M22 :=
  (M22TripleCover.coverOfCentralQuotientEquiv M22TripleCover.centralQuotientEquiv).toCovering

public theorem tripleCovering_kernel_card : Nat.card tripleCovering.toMonoidHom.ker = 3 := by
  change Nat.card
    (M22TripleCover.coverOfCentralQuotientEquiv M22TripleCover.centralQuotientEquiv).toMonoidHom.ker = 3
  rw [M22TripleCover.coverOfCentralQuotientEquiv_ker]
  exact M22TripleCover.center_card

universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

/-- Universality maps the actual multiplier onto the genuine triple-cover kernel. -/
public theorem three_dvd_kernel (f : Covering L M22)
    (hf : Covering.IsUniversal.{0, u, 0} f) : 3 ∣ Nat.card f.toMonoidHom.ker := by
  rw [← tripleCovering_kernel_card]
  exact kernel_card_dvd_of_surjective_factor f.toMonoidHom tripleCovering.toMonoidHom
    (hf.lift tripleCovering).toMonoidHom (hf.lift tripleCovering).surjective
    (congrArg Covering.toMonoidHom (hf.lift_fac tripleCovering))

end Sporadic.Mathieu.M22UniversalMultiplier
