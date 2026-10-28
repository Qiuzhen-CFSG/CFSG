module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherReduction
public import Theory.Representation.BinaryNaturalFullAction

/-!
# The normalizer and faithful action after eliminating the central factor

The marked binary natural action realizes every automorphism of V inside L.
Together with C_G(V)=V and V≤L, this gives N_G(V)≤L. Since V is now the
literal two-core of L, every element normalizing L normalizes V, and L is
self-normalizing. We also construct the actual quotient N_G(U)/U and its
faithful conjugation action, retaining the equation on every representative.

The final application feeds these normalizer and core identities into the
existing parabolic/Gaschütz consumer. Normality of the hyperplane residual
in N_G(C_T(U)), its fixed-space identity, dimension four and the actual
parabolic factors remain explicit. These implications do not complete the
component or tensor arguments in original 12.2.25.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, 12.2.25--26,
printed pp.805--806.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G} {d : ℕ}

omit [Finite G] in
private theorem natural_normalizer_le_of_centralizer
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hcentral : centralizer (V : Set G) = V) : normalizer (V : Set G) ≤ L := by
  obtain ⟨e, f, hf⟩ := A.natural
  intro g hg
  let a : MulAut V := V.normalizerMonoidHom ⟨g, hg⟩
  obtain ⟨x, hx⟩ := Representation.specialLinearNatural_binary_full d
    ((f.symm.trans a).trans f)
  obtain ⟨l, hl⟩ := (QuotientGroup.mk'_surjective (pCore 2 L)) (e.symm x)
  have hel : e (QuotientGroup.mk' (pCore 2 L) l) = x := by rw [hl, e.apply_symm_apply]
  have ha : V.normalizerMonoidHom ⟨l, D.normalizes l.property⟩ = a := by
    ext v
    have hact := hf l v
    rw [hel] at hact
    have heq := hx (f v)
    simp only [MulEquiv.trans_apply, f.symm_apply_apply] at heq
    rw [heq, f.symm_apply_apply] at hact
    exact hact.symm
  have hk : (⟨l, D.normalizes l.property⟩⁻¹ * (⟨g, hg⟩ : normalizer (V : Set G))) ∈
      V.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha]
    exact inv_mul_cancel a
  rw [normalizerMonoidHom_ker] at hk
  have hm : (l : G)⁻¹ * g ∈ L := D.le_component (hcentral ▸ hk)
  simpa only [mul_inv_cancel_left] using L.mul_mem l.property hm

theorem higher_normalizer_eq_of_kernel_vanishing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hzero : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥) :
    normalizer (L : Set G) = L := by
  have hc := (higher_kernel_vanishing_consequences D B hzero).2.1
  have hN : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rw [← hc]
    exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  exact le_antisymm (hN.trans (natural_normalizer_le_of_centralizer D A
    (higher_selfCentralizing_of_kernel_vanishing h D structural A C B hzero).1)) L.le_normalizer

namespace HigherRigidity

/-- The source quotient G_U/U, with U embedded in its actual normalizer. -/
abbrev NormalizerQuotient (U : Subgroup G) :=
  normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))

omit [Finite G] in
def quotient (U : Subgroup G) : normalizer (U : Set G) →* NormalizerQuotient U :=
  QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G)))

omit [Finite G] in
def action (U : Subgroup G) (hc : U ≤ centralizer (U : Set G)) :
    NormalizerQuotient U →* MulAut U :=
  QuotientGroup.lift (U.subgroupOf (normalizer (U : Set G))) U.normalizerMonoidHom
    (by rw [normalizerMonoidHom_ker]; exact subgroupOf_mono _ hc)

omit [Finite G] in
theorem action_quotient (U : Subgroup G) (hc : U ≤ centralizer (U : Set G))
    (g : normalizer (U : Set G)) (u : U) :
    (action U hc (quotient U g) u : G) = (g : G) * (u : G) * (g : G)⁻¹ := rfl

omit [Finite G] in
theorem action_injective (U : Subgroup G) (hc : centralizer (U : Set G) = U) :
    Function.Injective (action U hc.symm.le) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker, hc]

end HigherRigidity

/-- The faithful source action after the component-normalizer argument.
Both the literal quotient and its conjugation marking are retained. -/
theorem higher_normalizer_action_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G))
    (hf : ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓
      centralizer (rigidityHyperplaneResidual L U V : Set G) =
        (T : Subgroup G) ⊓ centralizer (L : Set G)) :
    normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ∃ a : HigherRigidity.NormalizerQuotient U →* MulAut U,
        Function.Injective a ∧ ∀ (g : normalizer (U : Set G)) (u : U),
          (a (HigherRigidity.quotient U g) u : G) = (g : G) * (u : G) * (g : G)⁻¹ := by
  have hzero := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn hf
  have hc := (higher_selfCentralizing_of_kernel_vanishing h D structural A C B hzero).2
  exact ⟨higher_normalizer_eq_of_kernel_vanishing h D structural A C B hzero,
    (higher_kernel_vanishing_consequences D B hzero).2.1,
    HigherRigidity.action U hc.symm.le, HigherRigidity.action_injective U hc,
    HigherRigidity.action_quotient U hc.symm.le⟩

/-- Application to the existing Gaschütz consumer. The dimension and parabolic
factors remain explicit; the normalizer and core conclusions are derived here. -/
theorem higher_split_of_residual_normal_and_factorization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G))
    (hf : ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓
      centralizer (rigidityHyperplaneResidual L U V : Set G) =
        (T : Subgroup G) ⊓ centralizer (L : Set G))
    (hd : d = 4) (F : ParabolicFactorization L V U P) :
    SplitLinearConfiguration L V d := by
  have hzero := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn hf
  exact splitLinearConfiguration_of_cyclic_factorization D A C (Or.inr hd)
    (higher_normalizer_eq_of_kernel_vanishing h D structural A C B hzero)
    (higher_kernel_vanishing_consequences D B hzero).2.1 F

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
