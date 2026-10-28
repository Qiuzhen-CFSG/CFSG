module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.RepeatedNatural.ComponentSeed
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.RepeatedNatural.PairAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Recognition
public import Theory.GroupTheory.PResidual.TwoThreeComparison

/-!
# Source inputs for the last binary-linear small-action contradiction

The faithful original NI/C_NI(V) ≅ S₃ action and NI outside MI force
O^{3′}(NI) outside MI: its image and the prescribed Sylow generate S₃,
and the action kernel already lies in MI. This supplies the escape used
to construct the two-perfect minimal-parabolic seed inside the original X.

The classification consumer constructs the original-U row, retains its
point-parabolic marking, identifies KI=Kc from the earlier centralization
clause, and produces the actual L₄(2) quotient and S-invariant seed required
by corrected 15.2.21(3). The S₃-square quotient proves S-reducibility.

The remaining source 15.2.21(1),(3) discharge is owned by
qt-e-152-char2-small-actions. The faithful NI action, noncontainment,
component residual and preceding T-action clauses retain their producers
qt-e-152-char2-component-models, qt-e-152-component-omega-connector and
qt-e-152-small-parabolic, with final discharge in qt-e-152-plane-uniqueness.
This module does not assert that those pending source clauses are proved.

Source: Aschbacher--Smith, 15.2.18(3), 15.2.21 and 15.2.23(a), pp.1113--1117.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 BinaryLinear.OuterCyclic
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The source's faithful S₃ action and NI outside MI force its cubic
residual outside MI. The kernel is the literal module centralizer. -/
theorem intersection_primeToResidual_not_le_partner
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ M ⊓ I ≤ Mc ⊓ I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    ¬ (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ≤ Mc ⊓ I := by
  let N := M ⊓ I
  let S := smallActionS T ZS
  have hSM : S ≤ M := (show S ≤ (T : Subgroup G) from inf_le_left).trans hsource.maximal.1.2
  have hSI : S ≤ I := (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hSN : S ≤ N := le_inf hSM hSI
  obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 S I from d.sylow_in_escape hI).restrict hSN inf_le_right
  have hpi : IsPiGroup twoThreePrimes (Equiv.Perm (Fin 3)) := by
    apply (IsPiGroup_iff _ _).mpr
    intro p hp
    have hc : Nat.card (Equiv.Perm (Fin 3)) = 2 * 3 := by
      rw [Nat.card_perm,Nat.card_fin]; rfl
    rw [hc] at hp
    rcases p.property.dvd_mul.mp hp with h | h
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left p.property.ne_one)
  have hmap : (primeToResidual 3 N ⊔ (P : Subgroup N)).map f = ⊤ := by
    rw [Subgroup.map_sup,map_primeToResidual_of_surjective 3 f hf,
      ←twoResidual_eq_primeToResidual_three hpi]
    exact pResidual_sup_sylow_eq_top (P.mapSurjective hf)
  have hgen : (primeToResidual 3 N ⊔ (P : Subgroup N)) ⊔ f.ker = ⊤ := by
    have he := congrArg (Subgroup.comap f) hmap
    simpa only [comap_map_eq,comap_top] using he
  intro hR
  apply hout
  intro x hx
  have hxgen : (⟨x,hx⟩ : N) ∈ (primeToResidual 3 N ⊔ (P : Subgroup N)) ⊔ f.ker :=
    hgen.symm ▸ mem_top _
  have hle : (primeToResidual 3 N ⊔ (P : Subgroup N)) ⊔ f.ker ≤ (Mc ⊓ I).subgroupOf N := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro r hr
      exact hR (mem_map_of_mem N.subtype hr)
    · intro s hs
      have hsS : (s : G) ∈ S := hP ▸ mem_map_of_mem N.subtype hs
      exact (le_sup_right.trans (d.residual_sup_planeSylow_le hI)) hsS
    · intro k hk
      rw [hker] at hk
      exact (d.centralizer_le_intersection hI) (centralizer_le d.geometry.plane_le hk)
  exact hle hxgen

/-- Construct the source seed from the faithful original NI action. -/
theorem minimalParabolic_seed_of_source
    (hI : PlaneEscapes Mc ZS I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (e : (X ⧸ pCore 2 X) ≃* SL(5,ZMod 2))
    (v : Fin 5 → ZMod 2) (hv : v ≠ 0)
    (hm : (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      e.toMonoidHom = MulAction.stabilizer SL(5,ZMod 2) v) :
    ∃ P : Subgroup G, smallActionS T ZS ⊓ X ⋖ P ∧ P ≤ X ∧ P ≤ M ⊓ I ∧
      smallActionS T ZS ≤ normalizer (P : Set G) ∧
      SmallActionsSource.Seed M I (smallActionS T ZS) ((pResidual 2 P).map P.subtype) ∧
      ¬ (pResidual 2 P).map P.subtype ≤ Mc ⊓ I :=
  component_minimalParabolic_seed_of_point_image d hI hXI hn hX
    (intersection_primeToResidual_not_le_partner d hI hout f hf hker) e v hv hm

/-- Literal input to corrected 15.2.21(3), constructed from the binary
branch. Original-U recognition, the point marking, the L₄(2) residual
quotient, the two-perfect seed and S-reducibility are all proved here.
The preceding Kc centralization and faithful NI action retain their source owners. -/
theorem binaryBranch_smallAction_obstruction
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hirr : IsSmallActionIrreducible (T : Subgroup G) (smallActionK H))
    (hc : smallActionKc H Mc ≤ centralizer (ZS : Set G))
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    Nonempty ((smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃* SL(4,ZMod 2)) ∧
      ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) ∧
      ∃ P : Subgroup G, smallActionS T ZS ⊓ X ⋖ P ∧ P ≤ X ∧ P ≤ M ⊓ I ∧
        smallActionS T ZS ≤ normalizer (P : Set G) ∧
        SmallActionsSource.Seed M I (smallActionS T ZS) ((pResidual 2 P).map P.subtype) ∧
        ¬ (pResidual 2 P).map P.subtype ≤ Mc ⊓ I := by
  let := U_elementary d hI hfit b.source.component.1
  obtain ⟨hKI,r,hr,_,e,v,hv,hm⟩ :=
    remaining_repeatedNatural_of_binaryBranch d hI hfit hn hout b hX hKX hpair hirr
  rw [KI_eq_Kc_of_centralizes d hI hX hc] at hKI
  exact ⟨hKI,reducible_of_symmetricThreePair d hpair,
    minimalParabolic_seed_of_source d hI b.source.component.1 hn hX hNI f hf hker
      e.groupEquiv v hv hm⟩

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
