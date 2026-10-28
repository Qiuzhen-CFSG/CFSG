module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Decomposition.CanonicalFactors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.ModuleAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.PrimeCoreAction
public import CFSG.Quasithin.ChapterD.Section02.Defs
public import Theory.Representation.BinaryGroupAction
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# A canonical five-commutator from a minimal cubic offender

Restrict the actual binary module to J = P*A. The given Q-member stays in Q,
so the finite global cubic minimum in J has an inclusion-minimal actor B.
Faithfulness of the two-complement on P* ensures that B moves the five-core,
which is exactly P* inside J. Solvability gives F*(J) = F(J). The universal
D.2.13(1–2) input therefore makes D = [P*,B] cyclic of order five with actual
support of order sixteen. Its image lies in F(H*) because P* is a normal
five-subgroup there.

This supplies a direct alternative to the offender-generated, Fitting-moved,
indecomposable reduction in D.2.17 for the factor-only application. There is no
claim that H* itself satisfies those D.2.17 hypotheses. The importing assembly
uses normality of the canonical family and Frattini irreducibility to show that
this one commutator already forces generation of the supplied P*.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), D.2.1 and
D.2.13(1–2), printed pp.178 and 184–185; 13.8.8(2) and 13.8.13, pp.949–951.
The universal D.2.13 theorem remains an explicit earlier-source input, owned
by the Chapter D development.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Three.Supercritical.Offenders ChapterD
universe u

/-- The exact universal implications D.2.13(1–2), for arbitrary faithful finite
binary representations and odd prime cores. This is an earlier-source input,
not a five-factor conclusion for the Chapter 13 configuration. The full
order-five conclusion retains the ratio, actor rank, actual group isomorphism,
fixed-space complement and displacement dimension. -/
def SourceD213PrimeInput : Prop :=
  ∀ (K W : Type u) [Group K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) K W),
    Function.Injective ρ → generalizedFitting K = fittingSubgroup K →
    ∀ (p : ℕ) [Fact p.Prime], Odd p →
    ∀ B : Subgroup K, B ∈ QhatStar ρ → ⁅pCore p K, B⁆ ≠ ⊥ →
      (p = 3 ∨ p = 5) ∧ (p = 5 → cubicRatio ρ = 2 ∧ rank B = 1 ∧
      Nonempty ((⁅pCore p K, B⁆ : Subgroup K) ≃* Multiplicative (ZMod 5)) ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅pCore p K, B⁆)
        (fixedSpace ρ (⁅pCore p K, B⁆ ⊔ B)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore p K, B⁆) = 4)

private theorem solvable_fitting (K : Type*) [Group K] [Group.IsSolvable K] :
    generalizedFitting K = fittingSubgroup K := by
  have hl : componentLayer K = ⊥ := by
    apply le_bot_iff.mp
    apply sSup_le
    rintro X ⟨_, hX⟩
    let : IsQuasisimple X := hX
    by_contra hn
    have hne : X ≠ ⊥ := fun he => hn he.le
    let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
    exact Group.IsPerfect.not_isSolvable X inferInstance
  simp only [generalizedFitting, hl, sup_bot_eq]

private theorem core_join {K : Type*} [Group K] [Finite K]
    (P A : Subgroup K) [P.Normal] (hP : IsPGroup 5 P) (hA : IsPGroup 2 A) :
    pCore 5 (P ⊔ A : Subgroup K) = P.subgroupOf (P ⊔ A) := by
  let J := P ⊔ A
  let N := P.subgroupOf J
  have hN : IsPGroup 5 N := hP.comap_subtype
  have hQ : IsPGroup 2 (J ⧸ N) := isPGroup_quotient_of_sup_eq_top N (A.subgroupOf J)
    hA.comap_subtype (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  have hm : (pCore 5 J).map (QuotientGroup.mk' N) = ⊥ := by
    have h5 : IsPGroup 5 ((pCore 5 J).map (QuotientGroup.mk' N)) := pCore_isPGroup.map _
    exact disjoint_self.mp (h5.disjoint_of_coprime (hQ.to_subgroup _) (by decide))
  exact le_antisymm (by simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm)
    (le_sSup ⟨inferInstance, hN⟩)

private theorem moved_comp {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) K W) (J : Subgroup K) (B : Subgroup J) :
    subspaceCommutator (ρ.comp J.subtype) ⊤ B = subspaceCommutator ρ ⊤ (B.map J.subtype) := by
  unfold subspaceCommutator
  congr 1
  ext w
  constructor
  · rintro ⟨b, hb, v, hv, rfl⟩
    exact ⟨b, mem_map_of_mem _ hb, v, hv, rfl⟩
  · rintro ⟨b, ⟨c, hc, rfl⟩, v, hv, rfl⟩
    exact ⟨c, hc, v, hv, rfl⟩

variable {G : Type u} [Group G] [Finite G]
variable {H U Z L₁ T M Vα : Subgroup G} [(Z.subgroupOf U).Normal]
  [IsElementaryAbelian 2 U]

private theorem support_card (a : StarAction H U Z) (X : Subgroup (Source.Hstar H)) :
    Nat.card (commutatorAction (X.map a.action) (U ⧸ Z.subgroupOf U)) =
      2 ^ Module.finrank (ZMod 2) (subspaceCommutator (linearAction a) ⊤ X) := by
  let := a.starMulAction
  rw [← a.star_support_eq]
  exact Representation.BinaryGroupAction.commutator_card (linearAction a) X

/-- Localize at P*A, where the quadratic source actor A is faithful on P*.
A genuine inclusion-minimal global cubic offender in this smaller group moves
its five-core. D.2.13(2) identifies its commutator and its support on the original
module. Both are transported through the literal inclusion into H*. -/
theorem exists_canonical_five_commutator (src : SourceD213PrimeInput.{u}) (a : StarAction H U Z)
    (ha : Function.Injective a.action) (r : ReducedFive H L₁ T M Vα)
    [Group.IsSolvable H] (A : Subgroup (Source.Hstar H))
    (hA : A ∈ Q (linearAction a))
    (hf : A ⊓ centralizer (Source.starImage H r.P : Set _) = ⊥) :
    ∃ B : Subgroup (Source.Hstar H), IsPGroup 2 B ∧
      ⁅Source.starImage H r.P, B⁆ ≠ ⊥ ∧
      ⁅Source.starImage H r.P, B⁆ ∈ a.canonicalFiveFactors r.P := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P := Source.starImage H r.P
  let J := P ⊔ A
  let ρ := (linearAction a).comp J.subtype
  let _ := r.Pstar_normal
  have hP : IsPGroup 5 P := (r.P_isPGroup.comap_subtype).map _
  let _ := hA.1.2
  have hA2 : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  have hAE : IsElementaryTwo (A.subgroupOf J) := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf (show A ≤ J from le_sup_right)⟩
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le (show A ≤ J from le_sup_right), Subgroup.map_bot] at hh
    exact hA.1.1 hh
  have hQ : A.subgroupOf J ∈ Q ρ := ⟨hAE,
    quadratic_subgroupOf (linearAction a) J A hA.2.1,
    (actionRatio_subgroupOf (linearAction a) J A le_sup_right).trans_le hA.2.2⟩
  have hbound : cubicRatio ρ ≤ 2 :=
    cubicRatio_le_quadraticRatio ρ |>.trans ((Q_nonempty_iff ρ).mp ⟨_, hQ⟩)
  obtain ⟨B, hB⟩ := (QhatStar_nonempty_iff ρ).mpr hbound
  let _ := hB.1.2.1.2
  have hB2 : IsPGroup 2 B := IsElementaryAbelian.isPGroup 2 B
  have hm : ⁅pCore 5 J, B⁆ ≠ ⊥ :=
    two_subgroup_moves_primeCore_in_join P A hP (by decide) hA2 hf B hB2 hB.1.2.1.1
  obtain ⟨_, hcase⟩ := src J (Additive (U ⧸ Z.subgroupOf U)) ρ
    ((linearAction_injective a ha).comp J.subtype_injective) (solvable_fitting J) 5 (by decide) B hB hm
  obtain ⟨_, _, ⟨e⟩, _, hdim⟩ := hcase rfl
  let D := ⁅pCore 5 J, B⁆
  have hcore := core_join P A hP hA2
  have hDmap : D.map J.subtype = ⁅P, B.map J.subtype⁆ := by
    rw [show D = ⁅pCore 5 J, B⁆ from rfl, map_commutator, hcore,
      map_subgroupOf_eq_of_le (show P ≤ J from le_sup_left)]
  have hDle : D.map J.subtype ≤ P := by
    rw [hDmap]
    exact commutator_le_left _ _
  have hDcard : Nat.card (D.map J.subtype) = 5 := by
    rw [card_map_of_injective J.subtype_injective, Nat.card_congr e.toEquiv]
    exact Nat.card_zmod 5
  have hsupport : Nat.card (commutatorAction ((D.map J.subtype).map a.action)
      (U ⧸ Z.subgroupOf U)) = 16 := by
    rw [support_card, ← moved_comp, hdim]
    rfl
  have hDF : D.map J.subtype ≤ fittingSubgroup (Source.Hstar H) :=
    hDle.trans ((le_sSup ⟨r.Pstar_normal, hP⟩ : P ≤ pCore 5 _).trans (pCore_le_fitting _ 5))
  refine ⟨B.map J.subtype, hB2.map _, ?_, ?_⟩
  · rw [← hDmap]
    intro he
    exact hm ((map_injective J.subtype_injective) (he.trans (Subgroup.map_bot _).symm))
  · rw [← hDmap]
    exact ⟨hDle, hDF, hDcard, hsupport⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
