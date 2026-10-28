module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.CoreComparison.Movement
public import Theory.Representation.BinaryConjugationSection.CentralDuality
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.Representation.Quotient

/-!
# The faithful core section from the original commutator pairing

Central binary commutators construct U_H/C_UH(Q_H) and its dual Q_H/H_C.
The earlier source kernel equality C_H(U_H/C_UH(Q_H))=Q_H descends this
action faithfully through the literal map H→H/O₂(H). The dual has the same
faithfulness, and both coordinate maps retain their vanishing-commutator
pairing. No isomorphism type is substituted for either source quotient.

Source: Aschbacher–Smith 13.7.4(1),(2), via F.9.7; application 13.8.27,
printed p.963. The earlier plus-kernel equality remains with the source
assembly owner qt-d-138-six-g2-source and its earlier-source producers.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic

variable {G : Type*} [Group G] [Finite G] {H V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Construct the faithful whole-star plus action and its literal dual core
section from the original central commutators and earlier kernel equality. -/
theorem source_faithful_core_section
    (hUH : Source.UH H V₃ ≤ H) (hline : V₁ ≤ Source.UH H V₃)
    (hcard : Nat.card V₁ = 2) (hz : H ≤ centralizer (V₁ : Set G))
    (hUQ : Source.UH H V₃ ≤ Source.QH H)
    (hcomm : ⁅Source.QH H, Source.UH H V₃⁆ ≤ V₁)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (hpluskernel : commutatorPreimage H (Source.UH H V₃)
      (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G)) = Source.QH H) :
    let U := Source.UH H V₃
    let U₀ := U ⊓ centralizer (Source.QH H : Set G)
    ∃ (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (U ⧸ U₀.subgroupOf U)))
      (sU : BinaryConjugationSection H U U₀ (σ.comp (QuotientGroup.mk' (pCore 2 H))))
      (sQ : BinaryConjugationSection H (Source.QH H) (Source.HC H V₃)
        (σ.dual.comp (QuotientGroup.mk' (pCore 2 H)))),
      Function.Injective σ ∧ Function.Injective σ.dual ∧
      (∀ (q : Source.QH H) (u : U),
        (sQ.coordinates q).toAdd (sU.coordinates u).toAdd = 0 ↔ ⁅(q : G), (u : G)⁆ = 1) ∧
      ∀ u : U, (sU.coordinates u).toAdd = Additive.ofMul
        (QuotientGroup.mk' (U₀.subgroupOf U) u) := by
  dsimp only
  let U := Source.UH H V₃
  let Q := Source.QH H
  let U₀ := U ⊓ centralizer (Q : Set G)
  have hNQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hNU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy V₃ H
  have hN₀ : H ≤ normalizer (U₀ : Set G) :=
    (le_inf hNU (hNQ.trans (normalizer_le_normalizer_centralizer Q))).trans
      inf_normalizer_le_normalizer_inf
  have hCQ : Source.HC H V₃ ≤ Q := by
    apply le_trans _ hcentralizer
    apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le
  have hC : Q ⊓ centralizer (U : Set G) = Source.HC H V₃ :=
    le_antisymm (inf_le_inf_right _ (pCoreIn_le 2 H)) (le_inf hCQ inf_le_right)
  have hd := BinaryConjugationSection.exists_central_duality H Q U V₁
    (pCoreIn_le 2 H) hUH hNQ hNU (hline.trans hUQ)
    (le_centralizer_iff.mp hz) hcomm hcard
  rw [hC] at hd
  obtain ⟨α, sU, sQ, hpair, hcoord⟩ := hd
  have hker : α.ker = pCore 2 H := map_injective H.subtype_injective
    ((sU.action_kernel_map hN₀).trans hpluskernel)
  let σ := quotientOfLEKer α (pCore 2 H) hker.symm.le
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
    exact (QuotientGroup.eq_one_iff a).mpr (hker ▸ (show a ∈ α.ker from hx))
  let hsU : BinaryConjugationSection H U U₀
      (σ.comp (QuotientGroup.mk' (pCore 2 H))) := sU
  let hsQ : BinaryConjugationSection H Q (Source.HC H V₃)
      (σ.dual.comp (QuotientGroup.mk' (pCore 2 H))) := sQ
  exact ⟨σ, hsU, hsQ, hf, faithful_dual σ hf, hpair, hcoord⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
