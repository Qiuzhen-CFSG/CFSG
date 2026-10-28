module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.SourceSeed
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SourceBounds
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Residual geometry on the original single component

The original identities H-infinity = O^2(H) = K place the residual of the
literal point centralizer inside the same component. The checked component
quotient embeds it in the generalized Fitting preimage. The constructed
natural--dual seed then supplies the actual moving eight-group [B,O^2(P)],
its independent fixed factor u*c, the S3 parabolic quotient, and rank four
and escape from M. None of these conclusions or coordinates is a premise.

The genuine component and support markings remain explicit from 14.6.20--23
and the component eliminations of 14.6.24. Their owners are
qt-e-suitable-component-supports and qt-e-suitable-component-marking;
qt-e-suitable-existence retains final suitable-choice assembly.

Source: Aschbacher--Smith, 14.6.23--24 and printed p.1042.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Matrix.PSL3Two.NaturalDualMarking
variable {G : Type*} [Group G] [Finite G]

/-- Construct the parabolic action and moving dual eight-group on the same
suitable element from the genuine single-component and paired support data. -/
theorem source_residual_geometry_of_single_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (A B C : Subgroup G)
    (hAU : A ≤ conjugateSpanBy (localModule T M) Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (hCU : C ≤ conjugateSpanBy (localModule T M) Mc)
    (hZC : centralInvolutions T ≤ C)
    (hsep : A ⊓ (B ⊔ C) ≤ centralInvolutions T)
    (hpair : ∀ x ∈ Mc, A.map (MulAut.conj x).toMonoidHom = A ∨
      A.map (MulAut.conj x).toMonoidHom = B)
    (q : (Mc ⊓ normalizer (A : Set G) : Subgroup G) →* BinaryLinear.GL Space)
    (hq : Function.Surjective q)
    (n : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) A (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q))
    (d : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) B (centralInvolutions T)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q)))
    (hcover : ∀ v ∈ conjugateSpanBy (localModule T M) Mc,
      ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, v = a*b*c)
    (hfixed : ∀ x ∈ Mc, ∀ c ∈ C, ⁅c,x⁆ ∈ centralInvolutions T)
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
    Nonempty (SourceParabolicAction P) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ b ∈ B, ∃ c ∈ C,
        ∃ coords : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T) R,
          coords.W = ⁅B,R⁆ ∧ coords.a = u*c ∧ coords.b = b ∧
          primeRank 2 (conjugateSpanBy (localModule T M) R) = 4 ∧ ¬R ≤ M := by
  dsimp only
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let P := h.kernel (zpowers u)
  let qSL := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp q
  have hqSL : Function.Surjective qSL :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp hq
  obtain ⟨_,_,hKF,_⟩ := source_component_action_placement
    hG T hempty hM hunique hmany hcard e K A hKres hK eK hKA qSL hqSL
  have hPH : P ≤ Mc := by
    intro x hx
    exact ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu.1))).mp hx).1
  have hRF : (pResidual 2 P).map P.subtype ≤
      ChapterA.Section04.twoGeneralizedFittingPreimage Mc :=
    (embedded_pResidual_mono 2 hPH).trans (by rw [hKtwo]; exact hKF)
  obtain ⟨b,hb,c,hc,v,hv,hvZ,hseed⟩ := source_exists_natural_dual_seed
    hG T hempty hM hunique hmany hcard e hab A B C hAU hBU hCU hZC hsep hpair
    q hq n d hcover hfixed s hs hsB u huA hu
  obtain ⟨action,quotient,coords,hcoords⟩ := source_residual_span_of_natural_dual_seed
    hG T hempty hM hunique hmany hcard e hab A B C hAU hBU hCU hsep hpair
    q hq n d hcover hfixed u b c v huA hb hc hv hvZ hseed hu hRF
  exact ⟨action,quotient,b,hb,c,hc,coords,hcoords⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
