module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.Contracts
public import Theory.Alternating.OddCentralCovers

/-!
# Two model inputs for the triple-seven exclusion

The carrier is the actual quotient of the universal alternating cover. The
degree input only asks for the lower bound ten. The independent normalizer
input concerns elementary subgroup orders and generation by three conjugate
involutions centralizing the cubic center. Neither input mentions offenders.

These contracts are not assertions of the model facts. Their combination is
proved in `SevenExclusion`; the two producers must still be supplied before
claiming the intrinsic exclusion in B.1.13.

Source: Aschbacher–Smith, B.1.13, printed p.74, and K.1, printed p.452,
citing Guralnick–Malle, Theorem 6.2 and Table 6.3.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
open GLS3.Chapter5.OddCentralCovers
universe v w

/-- The coarse faithful binary degree bound needed by the exclusion. -/
def DegreeBound : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) TripleSeven W),
    Function.Injective τ → Representation.IsIrreducible τ →
      10 ≤ Module.finrank (ZMod 2) W

/-- Structural facts about a faithful linear overgroup of the actual triple
cover. Involutions fixing its center generate the component with two conjugates;
elementary subgroups of the overgroup have order at most eight. -/
def NormalizerGeometry : Prop :=
  ∀ {H : Type v} {W : Type w} [Group H] [Finite H]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ι : TripleSeven →* H), Function.Injective ι → ι.range.Normal →
    ∀ (σ : Representation (ZMod 2) H W), Function.Injective σ →
      Representation.IsIrreducible (σ.comp ι) →
      (∀ A : Subgroup H, IsElementaryAbelian 2 A → Nat.card A ≤ 8) ∧
      ∀ a : H, a ≠ 1 → a ^ 2 = 1 →
        a ∈ centralizer ((center TripleSeven).map ι : Set H) →
        ∃ g h : H, ι.range ≤
          zpowers a ⊔ zpowers (g * a * g⁻¹) ⊔ zpowers (h * a * h⁻¹)

end CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
