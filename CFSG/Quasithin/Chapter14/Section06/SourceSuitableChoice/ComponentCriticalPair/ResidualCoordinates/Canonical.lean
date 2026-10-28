module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.FixedFactor
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.SingleComponent

/-!
# The original residual coordinates from paired single-component supports

The fixed factor is constructed as the literal commutator preimage modulo Z.
Gaschütz gives its supplement, and natural faithfulness proves separation.
The source seed is then marked at the same suitable u by the unique natural
Sylow-fixed vector. Residual monotonicity places O^2(P) in the original
component, giving the actual moving dual eight-group [B,O^2(P)], its fixed
independent factor, the S3 quotient of P, and rank four and escape from M.

Only the genuine single-component and paired-support data remain explicit:
14.6.20--23 are supplied by qt-e-suitable-component-supports, while the
component exclusions and actual model markings remain with
qt-e-suitable-component-marking. Final suitable-choice assembly belongs to
qt-e-suitable-existence. This theorem does not assert unconditional 14.6.24.

Source: Aschbacher--Smith, 14.6.22--24 and the final paragraph on p.1042.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Matrix.PSL3Two.NaturalDualMarking
variable {G : Type*} [Group G] [Finite G]

/-- The same paired supports construct all residual data without a fixed
factor, seed decomposition, coordinate record, or residual-placement premise. -/
theorem source_residual_geometry_of_paired_supports
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (A B : Subgroup G)
    (hAU : A ≤ conjugateSpanBy (localModule T M) Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (hsep : A ⊓ B ≤ centralInvolutions T)
    (hpair : ∀ x ∈ Mc, A.map (MulAut.conj x).toMonoidHom = A ∨
      A.map (MulAut.conj x).toMonoidHom = B)
    (q : (Mc ⊓ normalizer (A : Set G) : Subgroup G) →* BinaryLinear.GL Space)
    (hq : Function.Surjective q)
    (n : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) A (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q))
    (d : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) B (centralInvolutions T)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q)))
    (hmove : ⁅conjugateSpanBy (localModule T M) Mc,Mc⁆ ≤ A ⊔ B)
    (K : Subgroup G)
    (hKres : (solvableResidual Mc).map Mc.subtype = K)
    (hKtwo : (pResidual 2 Mc).map Mc.subtype = K)
    (hK : (K.subgroupOf Mc).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL)
    (hKA : K ≤ normalizer (A : Set G))
    (s : G) (hs : s ∈ (T : Subgroup G))
    (hsB : B.map (MulAut.conj s).toMonoidHom = A)
    (u : G) (huA : u ∈ A)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u) :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let P := h.kernel (zpowers u)
    let R := (pResidual 2 P).map P.subtype
    let C := commutatorPreimage (conjugateSpanBy (localModule T M) Mc) Mc (centralInvolutions T)
    Nonempty (SourceParabolicAction P) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ b ∈ B, ∃ c ∈ C,
        ∃ coords : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T) R,
          coords.W = ⁅B,R⁆ ∧ coords.a = u*c ∧ coords.b = b ∧
          primeRank 2 (conjugateSpanBy (localModule T M) R) = 4 ∧ ¬R ≤ M := by
  dsimp only
  let C := commutatorPreimage (conjugateSpanBy (localModule T M) Mc) Mc (centralInvolutions T)
  obtain ⟨hCU,hZC,hsepC,hfixed,hcover⟩ := source_fixed_factor_of_pair_commutator
    hG T hempty hM hunique hmany hcard e hab A B hAU hBU hsep q hq n d hmove
  exact source_residual_geometry_of_single_component
    hG T hempty hM hunique hmany hcard e hab A B C hAU hBU hCU hZC hsepC hpair
    q hq n d hcover hfixed K hKres hKtwo hK eK hKA s hs hsB u huA hu

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
