module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.LocalSections
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure

/-!
# Local placement sufficient for the PSL₃(3) graph extension

The graph extension has trivial two-core and simple generalized Fitting
subgroup. An actor of rank at most one makes the whole group an E2 member.
For a larger actor, the remaining calculation may first conjugate it inside
the chosen Sylow subgroup, then place it in a local subgroup with an S₃
quotient and two-group kernel. The local subgroup must contain the actor's
Sylow centralizer and have the literal Sylow intersection. If it and the
ambient Sylow generate the graph extension, the E1 calculation finishes.

This is a conditional assembly for the finite placement calculation, not
an assertion that the required local subgroups have been constructed.
In particular it does not require two solvable ambient Sylow overgroups.

Source: Aschbacher--Smith, E.1.2, E.1.5, E.1.8 and E.1.14(7),
printed pp.209--211, 214.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree

variable {G : Type*} [Group G] [Finite G]

/-- A purely local placement contract. The epimorphism's kernel is not
assumed to be the two-core, and E-membership is not part of the input.
Conjugating the actor is allowed; passing to a subgroup of it is not. -/
@[expose] def LocalGeometryAt (T : Sylow 2 G) : Prop :=
  ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
    1 < Group.rank A → ∃ (g : G) (K : Subgroup G),
      let B := A.map (MulAut.conj g).toMonoidHom
      B ≤ (T : Subgroup G) ∧ B ≤ K ∧
      (T : Subgroup G) ⊓ centralizer (B : Set G) ≤ K ∧
      (∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup G).subgroupOf K) ∧
      (∃ f : K →* Equiv.Perm (Fin 3), Function.Surjective f ∧
        IsPGroup 2 f.ker ∧ ¬ B.subgroupOf K ≤ f.ker) ∧
      (T : Subgroup G) ⊔ K = ⊤

omit [Finite G] in
private theorem tau_le_of_twoCore_eq_bot (T A K : Subgroup G)
    (hcore : pCore 2 G = ⊥) (hcent : T ⊓ centralizer (A : Set G) ≤ K) :
    tau T A ≤ K := by
  intro x hx
  apply hcent
  obtain ⟨hxT, hc⟩ := mem_centralizerModulo_iff.mp hx
  refine ⟨hxT, mem_centralizer_iff.mpr ?_⟩
  intro a ha
  have h := hc a ha
  rw [hcore, mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

/-- The local epimorphism and positioning data yield the literal ambient
E1 member for a conjugate of the original actor. -/
theorem exists_conjugate_member_of_localGeometry (T : Sylow 2 G)
    (hcore : pCore 2 G = ⊥) (hgeo : LocalGeometryAt T)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hrank : 1 < Group.rank A) :
    ∃ (g : G) (K : Subgroup G),
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      IsEMemberAt 1 (T : Subgroup G) (A.map (MulAut.conj g).toMonoidHom) K ∧
      (T : Subgroup G) ⊔ K = ⊤ := by
  obtain ⟨g, K, hBT, hBK, hcent, hSyl, ⟨f, hf, hk, ha⟩, hgen⟩ :=
    hgeo A hA hAT hrank
  let _ := hA
  exact ⟨g, K, hBT,
    isEMemberAt_of_symmetricThree_quotient _ _ K (IsElementaryAbelian.map _)
      hBT hBK (tau_le_of_twoCore_eq_bot _ _ _ hcore hcent) hSyl f hf hk ha, hgen⟩

private theorem member_le_family {T A K : Subgroup G} {Ω : Set (Subgroup G)}
    (hA : A ∈ Ω) (hAT : A ≤ T) (hK : IsEMemberAt 1 T A K) :
    K ≤ eFamilySubgroup 1 T Ω := by
  change K ≤ ⨆ B : {B : Subgroup G // B ∈ Ω ∧ B ≤ T}, eSubgroup 1 T B.1
  exact le_iSup_of_le ⟨A, hA, hAT⟩ (show K ≤ eSubgroup 1 T A from le_sSup hK)

private theorem isEGeneratedAt_of_localGeometry_and_small (T : Sylow 2 G)
    (hcore : pCore 2 G = ⊥) (hgeo : LocalGeometryAt T)
    (hsmall : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → Group.rank A ≤ 1 →
        IsEMemberAt 1 (T : Subgroup G) A ⊤) : IsEGeneratedAt 1 T := by
  classical
  intro Ω hΩ
  by_cases hex : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥
  · obtain ⟨A, hA, hAT, hne⟩ := hex
    apply top_unique
    by_cases hrank : Group.rank A ≤ 1
    · exact (member_le_family hA hAT
        (hsmall A (hΩ.1 A hA) hAT hne hrank)).trans
          le_sup_left
    · obtain ⟨g, K, hBT, hK, hgen⟩ := exists_conjugate_member_of_localGeometry
        T hcore hgeo A (hΩ.1 A hA) hAT (Nat.lt_of_not_ge hrank)
      rw [← hgen]
      exact sup_le ((Subgroup.le_normalizer.trans
        (ValuesEvenClassical.RankOneUpper.normalizer_le_weakClosure_normalizer
          (T : Subgroup G) hΩ)).trans le_sup_right)
        ((member_le_family (hΩ.2 g A hA) hBT hK).trans le_sup_left)
  · have hW : weakClosure (T : Subgroup G) Ω = ⊥ :=
      ValuesEvenClassical.RankOneUpper.weakClosure_eq_bot_of_members_eq_bot _ _
        (fun A hA hAT => by
          by_contra hne
          exact hex ⟨A, hA, hAT, hne⟩)
    rw [hW, normalizer_eq_top, sup_top_eq]

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- The small-actor branch has no local placement premise. -/
theorem isEMemberAt_top_of_rank_le_one (T : Sylow 2 (graphExtension F))
    (A : Subgroup (graphExtension F)) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup (graphExtension F))) (hne : A ≠ ⊥)
    (hrank : Group.rank A ≤ 1) : IsEMemberAt 1 (T : Subgroup _) A ⊤ :=
  ValuesEvenClassical.RankOneUpper.isEMemberAt_top_of_simple_generalizedFitting
    (Group.IsPerfect.not_isMulCommutative (generalizedFitting (graphExtension F)))
    T (generalizedFitting_sup_sylow F T) T A hA hAT hne hrank

/-- Final E-generation assembly from the local placement calculation.
Conjugation invariance preserves the original family in the large-actor
branch. Empty families are handled by their trivial weak closure. -/
theorem isEGeneratedAt_of_localGeometry (T : Sylow 2 (graphExtension F))
    (hgeo : LocalGeometryAt T) : IsEGeneratedAt 1 T :=
  isEGeneratedAt_of_localGeometry_and_small T (twoCore_eq_bot F) hgeo
    (isEMemberAt_top_of_rank_le_one F T)

/-- It suffices to do the finite placement calculation at one Sylow subgroup. -/
theorem isEGenerated_one_of_localGeometry
    (hgeo : ∃ T : Sylow 2 (graphExtension F), LocalGeometryAt T) :
    IsEGenerated 1 (graphExtension F) := by
  obtain ⟨T, hT⟩ := hgeo
  exact (isEGeneratedAt_of_localGeometry F T hT).isEGenerated

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree
