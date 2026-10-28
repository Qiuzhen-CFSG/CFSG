module
public import Theory.GroupTheory.InvolutionGeneratedAbelianKernel
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration

/-!
# From the actual generating pair to cyclic local generation

The original starred involutions generate G. Thus the elementary odd kernel
of a constructed involution complement equals its commutator with that
involution. The actual kernel, actor and full moved space therefore satisfy
every premise of `LocalGeneration`, with no extra commutator assumption.

Source: Aschbacher–Smith D.2.25 and the D.2.17(3) endpoint, printed p.190.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterD.CyclicSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The normalizer endpoint needs only the actual generated pair; the full
commutator follows from generation by the original starred involutions. -/
theorem CoreHypotheses.localGeneration_of_three_kernel (h : CoreHypotheses ρ)
    (P : Subgroup G) [P.Normal] [IsElementaryAbelian 3 P]
    (hne : P ≠ ⊥) (hm : subspaceCommutator ρ ⊤ P = ⊤)
    (t : G) (ht : orderOf t = 2) (hgen : P ⊔ zpowers t = ⊤)
    (hcodim : fixedCodim ρ (zpowers t) ≤ 2) : Nonempty (LocalGeneration ρ) := by
  have hP := IsElementaryAbelian.isPGroup 3 P
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    exact hn ▸ (by decide : Odd 3).pow
  have hc : ⁅P,zpowers t⁆ = P :=
    odd_abelian_kernel_eq_commutator_of_involution_generated h.smallSupport_generated
      (fun z hz => hz.1 ▸ pow_orderOf_eq_one z) P hodd (zpowers t) hgen
  exact ⟨{
    kernel := P
    normal := inferInstance
    prime := 3
    prime_prime := by decide
    prime_odd := by decide
    pgroup := hP
    nontrivial := hne
    involution := t
    order_two := ht
    generated := hgen
    commutator := hc
    moved := hm
    codimension := hcodim }⟩

end CFSG.Quasithin.ChapterD.CyclicSource
