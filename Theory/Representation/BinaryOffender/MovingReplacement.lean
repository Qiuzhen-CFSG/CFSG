module
public import Theory.Representation.BinaryOffender.TimmesfeldCentralizer
public import Theory.Representation.BinaryOffender.QuasisimpleNoncore
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# Replacement preserving movement of a fixed-free component

A best offender moving a normal quasisimple component has a quadratic
replacement that still moves it, provided the component fixes no vector.
Indeed, if the displacement centralizer centralizes the component, each
of its displacement spaces is component-invariant and fixed by the original
offender. Commutator generation then makes that space component-fixed.
Faithfulness would make the nontrivial replacement trivial.

A companion quotient test detects movement from any nontrivial elementary
two-image when the reduced component is the generalized Fitting subgroup
and the reduced actor has trivial two-core. Together these results construct
quadratic offenders in the original radical image of a nonbinary MS pair;
they do not assume that an offender lies inside the covering component.
Source: GLS2, Theorem 26.23(i); Aschbacher--Smith B.1.4--5 and C.1.34,
printed pp.68--70,136--137.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A replacement centralizer cannot centralize a fixed-free factor moved by the original actor. -/
theorem displacementCentralizer_not_centralizing
    (ρ : Representation (ZMod 2) G V) (K A : Subgroup G)
    (hf : Function.Injective ρ) (hfix : fixedSpace ρ K = ⊥)
    (hgen : ⁅K,A⁆ = K) (hA : IsElementaryTwo A)
    (hne : displacementCentralizer ρ A ≠ ⊥) :
    ¬ displacementCentralizer ρ A ≤ centralizer (K : Set G) := by
  intro hc
  apply hne
  apply bot_unique
  intro d hd
  have hcomm (a : G) (ha : a ∈ A) (v : V) :
      ρ a (ρ d v-v) = ρ d v-v := by
    apply sub_eq_zero.mp
    rw [displacement_commute ρ hA ha hd.1,hd.2 a ha v,sub_self]
  let W := LinearMap.range (ρ d - 1)
  have hK : K ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    rintro k hk v ⟨w,rfl⟩
    refine ⟨ρ k w,?_⟩
    change ρ d (ρ k w) - ρ k w = ρ k (ρ d w-w)
    rw [map_sub,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      mem_centralizer_iff.mp (hc hd) k hk]
  have hAn : A ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    rintro a ha v ⟨w,rfl⟩
    change ρ a (ρ d w-w) ∈ W
    rw [hcomm a ha w]
    exact ⟨w,rfl⟩
  let H := K ⊔ A
  let I := invariantSubspace ρ H W (sup_le hK hAn)
  let σ := I.toRepresentation
  have hAk : A.subgroupOf H ≤ σ.ker := by
    intro a ha
    apply LinearMap.ext
    rintro ⟨v,w,rfl⟩
    exact Subtype.ext (hcomm a.val ha w)
  have hg : ⁅K.subgroupOf H,A.subgroupOf H⁆ = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right),hgen]
  have hKk : K.subgroupOf H ≤ σ.ker := by
    rw [←hg]
    exact (commutator_mono le_rfl hAk).trans (commutator_le_right _ _)
  have hdρ : ρ d = ρ 1 := by
    rw [map_one]
    apply LinearMap.ext
    intro v
    have hz : ρ d v-v ∈ fixedSpace ρ K := by
      intro k
      exact congrArg Subtype.val (LinearMap.congr_fun
        (hKk (show (⟨k,mem_sup_left k.property⟩ : H) ∈ K.subgroupOf H from k.property))
        (⟨ρ d v-v,⟨v,rfl⟩⟩ : W))
    rw [hfix,Submodule.mem_bot] at hz
    exact sub_eq_zero.mp hz
  exact hf hdρ

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- The quadratic replacement of a best offender still moves a fixed-free
normal component whenever the original offender does. -/
theorem IsBestOffender.quadratic_replacement_moving_component
    (ρ : Representation (ZMod 2) G V) (K A : Subgroup G)
    [K.Normal] [IsQuasisimple K]
    (hf : Function.Injective ρ) (hfix : fixedSpace ρ K = ⊥)
    (hA : IsBestOffender ρ A) (hAC : ¬ A ≤ centralizer (K : Set G)) :
    IsBestOffender ρ (displacementCentralizer ρ A) ∧
      IsQuadratic ρ (displacementCentralizer ρ A) ∧
      ¬ displacementCentralizer ρ A ≤ centralizer (K : Set G) := by
  have hcomp : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  have hgen : ⁅K,A⁆ = K := by
    rcases hcomp.commutator_dichotomy A with hz | he
    · exact (hAC (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hz))).elim
    · exact le_antisymm (commutator_le_left _ _)
        ((le_iSup_conjugates K A).trans_eq he.symm)
  exact ⟨hA.displacementCentralizer_isBestOffender ρ,
    displacementCentralizer_isQuadratic ρ A,
    displacementCentralizer_not_centralizing ρ K A hf hfix hgen hA.1
      (hA.displacementCentralizer_ne_bot ρ)⟩

end Representation.BinaryOffender

namespace Representation.BinaryOffender
open scoped IsMulCommutative
variable {G H : Type*} [Group G] [Group H] [Finite H]

/-- An elementary two-subgroup surviving a core-free quotient moves its
full generalized Fitting preimage component. -/
theorem elementary_not_centralizing_of_reduced_image
    (B : Subgroup G) (f : G →* H)
    (hfit : generalizedFitting H = B.map f) (hcore : pCore 2 H = ⊥)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hne : A.map f ≠ ⊥) :
    ¬ A ≤ centralizer (B : Set G) := by
  intro hc
  let C := centralizer (generalizedFitting H : Set H)
  have hAC : A.map f ≤ C := by
    change A.map f ≤ centralizer (generalizedFitting H : Set H)
    rw [hfit]
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    rw [←map_mul,←map_mul,hc ha b hb]
  have hCF : C ≤ generalizedFitting H := centralizer_generalizedFitting_le H
  let : IsMulCommutative C := ⟨⟨fun a b => Subtype.ext
    (a.property b (hCF b.property)).symm⟩⟩
  have hF : C ≤ fittingSubgroup H := le_sSup ⟨inferInstance,inferInstance⟩
  have hAO : A.map f ≤ pPrimeCore 2 H :=
    hAC.trans (hF.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))
  have hp : IsPGroup 2 (A.map f) := (IsElementaryAbelian.isPGroup 2 A).map f
  obtain ⟨m,hm⟩ := hp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (A.map f)) (Nat.card (pPrimeCore 2 H)) := by
    rw [hm]
    exact (pPrimeCore_coprime_card (p := 2) (G := H)).pow_left m
  exact hne (le_bot_iff.mp ((le_inf le_rfl hAO).trans
    (disjoint_of_coprime_natCard hcop).le_bot))
end Representation.BinaryOffender
