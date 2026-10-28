module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportDisplacement
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionComponentRank

/-!
# Actor rank with the simultaneous component centralizer retained

The two natural SL₃ coordinates bound the actor rank only after accounting
for the subgroup centralizing both components. Inner action fixes every
homogeneous support seed; the literal seed action then bounds each quotient
rank by twice its defining field degree.

A nontrivial simultaneous centralizer moves a further component. The source
D.2.13 removes odd prime cores, and uniqueness of a component of nonzero
three-rank makes this new component three-free and distinct from the chosen
support. The actual Chapter12 application identifies it as a Suzuki group
and proves that the original actor exchanges its two conjugates.

This retains the kernel in the source D.3.10 rank estimate instead of assuming
it is trivial. Its Suzuki exclusion, the complementary displacement bound,
U = W and Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.15--19 and the final D.3.10 argument,
printed pp.202--204; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource ChapterD
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- Inner action fixes the original homogeneous seed itself. -/
theorem homogeneous_support_invariant_of_inner
    (ρ : Representation (ZMod 2) H E) {X P : Subgroup H} {R : Submodule (ZMod 2) E}
    (hR : IsIrrPlusWith ρ X P R)
    (hi : ChapterB.SourceInduction.ComponentReduction.InducesInner P X) :
    P ≤ subspaceStabilizer ρ R := by
  intro p hp
  apply (subspace_map_eq_iff ρ R p).mp
  obtain ⟨x,hx,he⟩ := hi p⁻¹ (P.inv_mem hp)
  let σ := (quotientImage ρ X R hR.invariant).toRepresentation
  let u : X := ⟨x,hx⟩
  let c := LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom u)
  apply hR.map_eq_of_central_twist ρ ⟨p,hp⟩ c
  intro y v
  have hy : X.normalizerMonoidHom ⟨p⁻¹,hR.normalizes (P.inv_mem hp)⟩ y = u*y*u⁻¹ := by
    apply Subtype.ext
    exact he y y.property
  rw [hy]
  change σ u (σ y v) = σ (u*y*u⁻¹) (σ u v)
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]

omit [FiniteDimensional (ZMod 2) E] in
/-- The rank of a stabilizing actor, retaining its actual component centralizer. -/
theorem natural_support_actor_rank
    (ρ : Representation (ZMod 2) H E) (X A : Subgroup H) [X.Normal] [IsQuasisimple X]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlus ρ X R)
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (invariantSubspace ρ X R hR.choose).toRepresentation (linearNatural F 3))
    (hAR : A ≤ subspaceStabilizer ρ R) (hA : IsElementaryAbelian 2 A) :
    rank A ≤ rank (A ⊓ centralizer (X : Set H)) + 2 * F.degree := by
  have hsum := rank_subspaceKernel_add_image ρ R A hAR (hA.isPGroup 2 A)
  have him := restricted_rank_le_odd_linearThree ρ X R hR.choose F ho e A hAR hA
  have hker : subspaceKernel ρ R A ≤ A ⊓ centralizer (X : Set H) :=
    le_inf (subspaceKernel_le ρ R A)
      (subspaceKernel_le_component_centralizer ρ X R hR.choose (hR.not_le_fixedSpace ρ) A)
  have hr : rank (subspaceKernel ρ R A) ≤ rank (A ⊓ centralizer (X : Set H)) :=
    Nat.log_mono_right (Nat.card_le_card_of_injective (inclusion hker) (inclusion_injective hker))
  omega

/-- If an actor centralizing K and X survives, its moved support is a
three-free component distinct from X. Odd prime cores are removed by D.2.13. -/
theorem common_centralizer_moves_three_free_component
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (K X A N : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hcore : pCore 2 H = ⊥) (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    (hX : IsComponent H X) (hXC : X ≤ centralizer (K : Set H))
    (hr : primeRank 3 (centralizer (K : Set H)) ≤ 1) (hthree : 3 ∣ Nat.card X)
    (hA : A ∈ QhatStar ρ) (hNA : N ≤ A) (hNn : N ≠ ⊥)
    (hNK : N ≤ centralizer (K : Set H)) (hNX : N ≤ centralizer (X : Set H)) :
    ∃ J : Subgroup H, IsComponent H J ∧ J ≤ centralizer (K : Set H) ∧
      J ≠ X ∧ ¬ 3 ∣ Nat.card J ∧
      ⁅componentOrbit J A,N⁆ = componentOrbit J A := by
  let C := centralizer (K : Set H)
  let := hA.1.2.1.2
  have hAN : A ≤ normalizer (N : Set H) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro a ha n hn
    exact congrArg Subtype.val (mul_comm (⟨n,hNA hn⟩ : A) ⟨a,ha⟩)
  obtain ⟨Y,hYC,_,hYn,hYN,hcases⟩ := exists_moved_subgroup_in_component_centralizer
    K hcore A N ((IsElementaryAbelian.isPGroup 2 A).to_le hNA) hNn hNA hAN hNK
  rcases hcases with ⟨p,hp,ho,hYP,_⟩ | ⟨J,hJ,hJC,hY⟩
  · let : Fact p.Prime := ⟨hp⟩
    have hP : (pCore p C).map C.subtype ≤ pCore p H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map C.subtype⟩
    have hm : ⁅pCore p H,A⁆ ≠ ⊥ := by
      intro he
      exact hYn (bot_unique (hYN.symm ▸ (commutator_mono (hYP.trans hP) hNA).trans he.le))
    obtain ⟨hp35,hfive⟩ := source_lemma_D_2_13_one_two ρ hf hA ho hm
    rcases hp35 with rfl | hp5
    · have h3 := three_core_eq_bot_of_component_in_rank_one C hr X hX hXC hthree
      rw [h3,Subgroup.map_bot] at hYP
      exact (hYn (bot_unique hYP)).elim
    · have hz := rank_one_starred_component_centralizer_eq_bot ρ hf K hfull hA (hfive hp5).2.1
      exact (hNn (bot_unique ((le_inf hNA hNK).trans hz.le))).elim
  · have hne : J ≠ X := by
      intro he
      have hXN : X ≤ centralizer (N : Set H) := le_centralizer_iff.mp hNX
      have hAX : A ≤ normalizer (centralizer (N : Set H) : Set H) := by
        intro a ha
        exact normalizer_le_normalizer_centralizer N (hAN ha)
      have hYNfix : Y ≤ centralizer (N : Set H) := by
        rw [hY,he]
        exact iSup_conjugates_le_of_le_normalizer X A _ hXN hAX
      exact hYn (hYN.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hYNfix))
    refine ⟨J,hJ,hJC,hne,?_,by simpa only [hY] using hYN⟩
    intro hJ3
    exact hne (component_unique_in_three_rank_one C hr J X hJ hX hJC hXC hJ3 hthree)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
