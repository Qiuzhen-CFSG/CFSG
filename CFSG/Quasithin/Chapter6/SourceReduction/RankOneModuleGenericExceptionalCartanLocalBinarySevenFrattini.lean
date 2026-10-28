module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinarySevenMovement
public import Theory.GroupAction.SevenMovedFrattini

/-!
# The Frattini section of the original seven-moved core

Keep X = CT, U = ⟨Ω₁Z(T)ᴸ⟩, E = U intersect O₂(X), N = ⟨Eˣ⟩,
and P = [N,B]. The original seven-action is coprime, so [P,B] = P.
The elementary Frattini quotient therefore has no nonidentity B-fixed
point. Since P is nontrivial and |B| = 7, this action is faithful and
|P/Φ(P)| = 8^k for k > 0.

Because B fixes U, the intersection P intersect U lies in Φ(P), and the
inclusion P → N puts the ambient Φ(P) inside the same Φ(N). Thus the
seven-moved subgroup is separated from the original omega-span even
before passage to N/Φ(N). No core is discarded, and P is not assumed
abelian. These conclusions feed the remaining ambient core comparison;
the binary-triality exclusion and full exceptional witness remain open.

Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638, refs/quasithin.pdf,
with the standard coprime-action and Burnside-basis theorems.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

/-- The same P has a faithful, fixed-point-free seven-action on its
Frattini quotient, and its intersection with U disappears there. -/
theorem original_binary_triality_seven_moved_frattini
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    let P := ⁅N,B⁆
    ⁅P,B⁆ = P ∧
      P ⊓ U ≤ (frattini P).map P.subtype ∧
      (frattini P).map P.subtype ≤ (frattini N).map N.subtype ∧
      ∃ a : B →* MulAut P,
        (∀ (b : B) (v : P), ((a b v : P) : G) =
          (b : G) * (v : G) * (b : G)⁻¹) ∧
        let d := (quotientAut (frattini P)).comp a
        (∀ v : P ⧸ frattini P, (∀ b : B, d b v = v) → v = 1) ∧
        Function.Injective d ∧
        ∃ k : ℕ, 0 < k ∧ Nat.card (P ⧸ frattini P) = 8^k := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  let P := ⁅N,B⁆
  obtain ⟨_,_,hb,hBU,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,_,hNQ,hXN,_⟩ := original_binary_triality_kernel_large_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,_,hPphi,_⟩ := original_binary_triality_seven_moved_core
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hHX : H ≤ X := by
    rw [←hKT]
    exact sup_le (hKC.trans le_sup_left) le_sup_right
  have hBN : B ≤ normalizer (N : Set G) :=
    (c.right_le.trans inf_le_right).trans (hHX.trans hXN)
  have hN : IsPGroup 2 N := (isPGroup_pCoreIn 2 X).to_le hNQ
  change ¬ P ≤ (frattini N).map N.subtype at hPphi
  have hP0 : P ≠ ⊥ := fun hp => hPphi (by rw [hp]; exact bot_le)
  exact seven_moved_subgroup_frattini N B U hN hBN hb hP0 hBU

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
