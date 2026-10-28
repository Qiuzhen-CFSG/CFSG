module

public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.QuotientNormalImage
public import Theory.GroupAction.OddFiveSixteen
public import Theory.GroupAction.FaithfulSixteen
public import Theory.GroupAction.OddBinaryFourOvergroups
public import Theory.LinearAlgebra.BinaryFivePointStabilizer

/-!
# Linear-overgroup reductions for the Ree and Tits branch

These reductions support Aschbacher--Smith, *The Classification of Quasithin
Groups*, Lemma 14.2.21, printed p.989 (PDF p.1006). A faithful quotient
representation whose marked subgroup maps onto a normal linear subgroup
pulls normality back to the original group. Burnside transfer identifies the
two-residual with the odd core when the Sylow two-subgroup is cyclic.

The actual binary five-space point stabilizer has an elementary abelian kernel
of order sixteen, equal to its two-core, and quotient GL₄(2). A Hall--Sylow
argument proves normality of each five-subgroup in an odd solvable faithful
four-dimensional actor. A strict enlargement is consequently cyclic of order
fifteen and regular on the nonzero vectors. Applying this to the two-residual
discharges the independent linear calculations in the source. The caller still
supplies the actual parabolic embedding and the marked five-subgroup.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal

/-- Pull the linear normality statement back through the actual quotient
representation. In the application, `Q` is QH and `N` is O₂(Λ). -/
public theorem normal_of_faithful_quotient_image {M L : Type*} [Group M] [Group L]
    (F Q : Subgroup M) [F.Normal] (hFQ : F ≤ Q)
    (ρ : M ⧸ F →* L) (hρ : Function.Injective ρ)
    (N : Subgroup L) [N.Normal]
    (hQN : (Q.map (QuotientGroup.mk' F)).map ρ = N) : Q.Normal :=
  Subgroup.normal_of_faithful_quotient_image F Q hFQ ρ hρ N hQN

/-- The cyclic-Sylow step identifies the source's two-residual with the odd core. -/
public theorem twoResidual_eq_oddCore
    {M : Type*} [Group M] [Finite M] (T : Sylow 2 M) (hT : IsCyclic T) :
    pResidual 2 M = pPrimeCore 2 M :=
  T.twoResidual_eq_oddCore_of_isCyclic hT

/-- The two-residual is itself a normal odd complement. -/
public theorem twoResidual_normal_complement
    {M : Type*} [Group M] [Finite M] (T : Sylow 2 M) (hT : IsCyclic T) :
    ∃ hN : (pResidual 2 M).Normal,
      Odd (Nat.card (pResidual 2 M)) ∧
      @IsPGroup 2 (M ⧸ pResidual 2 M)
        (@QuotientGroup.Quotient.group M _ (pResidual 2 M) hN) :=
  T.twoResidual_normal_complement_of_isCyclic hT

open Theory.LinearAlgebra.BinaryFivePointStabilizer in
/-- The source's Λ is the actual point stabilizer, and N is its actual quotient
action kernel. The quotient identification is an isomorphism of groups. -/
public theorem binary_point_stabilizer_structure
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (z : E) (hz : z ≠ 0) (hE : Module.finrank (ZMod 2) E = 5) :
    Function.Surjective (quotientAction z) ∧
      IsElementaryAbelian 2 (kernel z) ∧ Nat.card (kernel z) = 16 ∧
      pCore 2 (stabilizer z) = kernel z ∧
      Nonempty ((stabilizer z ⧸ kernel z) ≃*
        LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2)) :=
  ⟨quotientAction_surjective z, inferInstance, natCard_kernel z hz hE,
    pCore_eq_kernel z hz hE, ⟨quotientEquivGL4 z hz hE⟩⟩

open Theory.LinearAlgebra.BinaryFivePointStabilizer in
/-- QH is normal in Mc once the concrete faithful representation of Mc/F
identifies QH/F with the two-core of the point stabilizer. Normality is in Mc;
no ambient normality or linear normality premise is required. -/
public theorem normal_of_point_stabilizer_quotient_image
    {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (z : E) (hz : z ≠ 0) (hE : Module.finrank (ZMod 2) E = 5)
    (F Q : Subgroup M) [F.Normal] (hFQ : F ≤ Q)
    (ρ : M ⧸ F →* stabilizer z) (hρ : Function.Injective ρ)
    (hQN : (Q.map (QuotientGroup.mk' F)).map ρ = pCore 2 (stabilizer z)) :
    Q.Normal := by
  rw [pCore_eq_kernel z hz hE] at hQN
  exact normal_of_faithful_quotient_image F Q hFQ ρ hρ (kernel z) hQN

/-- For the source's Mc/Q, cyclic Sylow two-subgroups make the residual odd.
Its faithful binary representation then forces a strict overgroup of the
marked five-subgroup to be cyclic of order fifteen and regular. -/
public theorem twoResidual_cyclic_fifteen_regular_of_linear_four
    {M V : Type*} [Group M] [Finite M] [Group.IsSolvable M]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (T : Sylow 2 M) (hT : IsCyclic T)
    (ρ : M →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (hV : Module.finrank (ZMod 2) V = 4)
    (K : Subgroup (pResidual 2 M)) (hK : Nat.card K = 5) (hproper : K < ⊤) :
    Nat.card (pResidual 2 M) = 15 ∧ IsCyclic (pResidual 2 M) ∧
      ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃! a : pResidual 2 M, ρ a x = y := by
  exact Theory.GroupAction.cyclic_fifteen_regular_of_odd_linear_four
    inferInstance (ρ.comp (pResidual 2 M).subtype)
    (hρ.comp Subtype.val_injective) (T.odd_card_twoResidual_of_isCyclic hT)
    hV K hK hproper

/-- Once the marked five-subgroup is proved normal, its strict odd overgroup
acts regularly on the fifteen nonidentity elements of the supplied module. -/
public theorem regular_of_normal_five_strict_overgroup
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    (ρ : A →* MulAut V) (hρ : Function.Injective ρ)
    (K : Subgroup A) [K.Normal] (hK : Nat.card K = 5)
    (hA : Odd (Nat.card A)) (hV : Nat.card V = 16) (hproper : K < ⊤) :
    Nat.card A = 15 ∧ IsCyclic A ∧
      ∀ x y : V, x ≠ 1 → y ≠ 1 → ∃! a : A, ρ a x = y := by
  obtain ⟨hcard, hcyc⟩ := Theory.GroupAction.cyclic_fifteen_of_normal_five_lt_top
    ρ hρ K hK hA hV hproper
  let := hcyc
  exact ⟨hcard, hcyc, Theory.GroupAction.faithful_cyclic_fifteen_regular
    ρ hρ hcard hV⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal
