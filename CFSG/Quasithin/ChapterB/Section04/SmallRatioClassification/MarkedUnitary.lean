module
public import Theory.Representation.ScalarRestrictionSmallDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.Modules
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios

/-!
# Excluding the natural unitary row for the original marked chief action

Table B.4.5 contains the binary restriction of the natural SU₃(2^n) module
for n>=2. Its native coefficient degree is 2n and its binary dimension is
6n. A faithful chief-action actor of displacement at most two is smaller
than both the coefficient degree and half that dimension. The scalar-
restriction theorem forces it to be the identity, contradicting the
original nontrivial actor.

The action equivalence supplies the actual coefficient-linear layer action;
neither a semilinearity premise nor an ambient automorphism classification
is assumed. The genuine B.4 hypotheses and marked involution from the
original chief-image construction supply the source wrapper. The universal
B.4.5 table and its unitary constructor remain unchanged.

Source: Aschbacher–Smith, Lemma 13.5.21, printed pp.923–924, especially
condition (iii); Table B.4.5, printed p.87, and K.3.3, printed p.456.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) G V}

/-- A nonidentity actor of binary displacement at most two excludes the
native SU₃ row over a quadratic field of degree at least four. -/
public theorem unitary_excluded_of_small_actor (L : Subgroup G) [L.Normal]
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    (F : BinaryField) (n : ℕ) (hn : 2 ≤ n) (hd : F.degree = 2*n)
    (J : HermitianForm 3 F.Carrier)
    (t : G) (ht : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) :
    ¬ Nonempty (ActionEquiv (ρ.comp L.subtype) (unitaryThree F J)) := by
  rintro ⟨a⟩
  let _ : IsIrreducible (ρ.comp L.subtype) := hi
  let σ : Representation F.Carrier L (Fin 3 → F.Carrier) :=
    (((generalLinearNatural 3).comp J.specialSubgroup.subtype).comp a.groupEquiv.toMonoidHom)
  have he (g : L) (v : V) : a.linearEquiv (ρ g v) = σ g (a.linearEquiv v) :=
    a.intertwines g v
  have hF : Module.finrank (ZMod 2) F.Carrier = 2*n := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod,F.card_eq,hd] at hh
    exact ((Nat.pow_right_injective (by decide : 2 ≤ 2)) hh).symm
  have hV : Module.finrank (ZMod 2) V = 6*n := by
    rw [a.linearEquiv.finrank_eq,Module.finrank_pi_fintype]
    simp only [hF,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    omega
  have hh := small_displacement_eq_one_of_scalar_restriction ρ L σ a.linearEquiv he t
    (le_normalizer_of_normal (mem_top t)) (by rw [hV]; omega) (by rw [hF]; omega)
  exact ht (hf (hh.trans ρ.map_one.symm))

variable [Finite G]

/-- Chapter K's original faithful irreducible layer, retaining the actual
small-displacement involution supplied by the chief-image source. -/
public theorem source_unitary_excluded_of_small_involution {L : Subgroup G}
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (F : BinaryField) (n : ℕ) (hn : 2 ≤ n) (hd : F.degree=2*n)
    (J : HermitianForm 3 F.Carrier) (t : G) (ht : orderOf t=2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t-1))≤2) :
    ¬ Nonempty (ActionEquiv (ρ.comp L.subtype) (unitaryThree F J)) := by
  let _ : L.Normal := h.layer_normal
  exact unitary_excluded_of_small_actor L h.faithful h.irreducible F n hn hd J t
    (fun h1 => by
      have hh := congrArg orderOf h1
      rw [orderOf_one] at hh
      omega) hr

open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
/-- The literal B.4 chief-action input and its original marked involution
eliminate the unitary table row, while preserving the universal table. -/
public theorem marked_b4_unitary_source
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (F : BinaryField) (n : ℕ) (hn : 2 ≤ n) (hd : F.degree=2*n)
    (J : HermitianForm 3 F.Carrier) (t : G) (ht : orderOf t=2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t-1))≤2) :
    ¬ Nonempty (ActionEquiv (ρ.comp (generalizedFitting G).subtype) (unitaryThree F J)) :=
  unitary_excluded_of_small_actor (generalizedFitting G) h.faithful h.irreducible F n hn hd J t
    (fun h1 => by
      have hh := congrArg orderOf h1
      rw [orderOf_one] at hh
      omega) hr
end CFSG.Quasithin.ChapterB.SmallRatioClassification
