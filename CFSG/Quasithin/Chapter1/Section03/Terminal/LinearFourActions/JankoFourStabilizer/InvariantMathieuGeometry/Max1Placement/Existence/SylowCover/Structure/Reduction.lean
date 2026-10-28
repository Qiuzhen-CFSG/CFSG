module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Contracts
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow
public import Theory.GroupTheory.MinimalNormalPCore
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!+# The central Sylow involution inside an arbitrary J₄ overgroup

Let S be an ambient Sylow two-subgroup contained in M. The certified center
of S has order two, including when S is restricted to M. Every nontrivial
normal two-subgroup of M contains this center: restrict the normal subgroup
to S, use the nontrivial intersection with Z(S), and use |Z(S)| = 2.

Consequently the normal closure in M of this center is contained in every
nontrivial normal two-subgroup. It is itself nontrivial. If O₂(M) is
nontrivial, choose an elementary minimal normal subgroup inside O₂(M);
the closure lies in it and is therefore elementary. The converse follows
from normality, giving an exact two-core criterion. When elementary, the
closure is a minimal normal subgroup, with all normality relative to M.

The remaining J₄ inputs are deliberately separate: nontrivial two-cores
for all maximal Sylow overgroups, and the order spectrum of this explicitly
defined closure when it is elementary. Neither input is proved here.
Even characteristic, which tests two-local subgroups, does not by itself
supply the first input for arbitrary maximal subgroups.

Source context: Aschbacher–Smith A.3.12, printed pp.47–48, refers the
sporadic Sylow-overgroup step to Aschbacher, *Overgroups of Sylow subgroups
in sporadic groups*, Memoirs AMS 60 (1986), no.343. Kleidman–Wilson,
*The maximal subgroups of J₄* (1988), pp.484–510, gives the corresponding
maximal-subgroup analysis. The deductions here are finite-group arguments
using the certified concrete Sylow center, not an assumed subgroup table.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The normal closure is taken in the overgroup M, after restricting S to M. -/
@[expose] def centralClosure (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model)
    (hSM : S.toSubgroup ≤ M) : Subgroup M :=
  normalClosure ((center (S.subtype hSM)).map (S.subtype hSM).toSubgroup.subtype : Set M)

instance centralClosure_normal (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model)
    (hSM : S.toSubgroup ≤ M) : (centralClosure S M hSM).Normal := by
  unfold centralClosure
  infer_instance

/-- The concrete Sylow-center certificate also applies after restricting to M. -/
theorem restricted_sylow_center_card (S : Sylow 2 Janko4.Model)
    (M : Subgroup Janko4.Model) (hSM : S.toSubgroup ≤ M) :
    Nat.card (center (S.subtype hSM)) = 2 := by
  let e : S.subtype hSM ≃* S := subgroupOfEquivOfLe hSM
  rw [Nat.card_congr (centerCongr e).toEquiv]
  obtain ⟨P⟩ := Sylow.nonempty (p := 2)
    (G := centralizer ({Janko4.a} : Set Janko4.Model))
  obtain ⟨T, hT⟩ := Janko4.OuterReduction.OddIndex.centralizer_sylow_is_ambient P
  rw [Nat.card_congr (centerCongr (S.equiv T)).toEquiv]
  rw [hT, ← card_map_of_injective
    (((P : Subgroup (centralizer ({Janko4.a} : Set Janko4.Model))).map
      (centralizer ({Janko4.a} : Set Janko4.Model)).subtype).subtype_injective),
    Janko4.OuterReduction.OddIndex.centralizer_sylow_center, Nat.card_zpowers,
    Janko4.orderOf_a]

private theorem center_le_of_normal {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hc : Nat.card (center S) = 2)
    (E : Subgroup G) [E.Normal] (hp : IsPGroup 2 E) (hne : E ≠ ⊥) :
    (center S).map S.toSubgroup.subtype ≤ E := by
  have hES : E ≤ S.toSubgroup := hp.le_sylow_of_normal S
  let A := E.subgroupOf S.toSubgroup
  have hA : A ≠ ⊥ := by
    intro h
    apply hne
    change E.subgroupOf S.toSubgroup = ⊥ at h
    rw [← map_subgroupOf_eq_of_le hES, h, Subgroup.map_bot]
  have hI := center_inf_ne_bot_of_normal S.isPGroup' A hA
  have hdiv : Nat.card (center S ⊓ A : Subgroup S) ∣ 2 :=
    (card_dvd_of_le (show center S ⊓ A ≤ center S from inf_le_left)).trans hc.dvd
  have hIc : Nat.card (center S ⊓ A : Subgroup S) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact (hI (eq_bot_of_card_eq _ h)).elim
    · exact h
  have heq : center S ⊓ A = center S :=
    eq_of_le_of_card_ge inf_le_left (by rw [hIc, hc])
  have hZA : center S ≤ A := heq.symm.le.trans inf_le_right
  rintro x ⟨s, hs, rfl⟩
  exact hZA hs

/-- The central involution survives in its normal closure in every overgroup. -/
theorem centralClosure_ne_bot (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model)
    (hSM : S.toSubgroup ≤ M) : centralClosure S M hSM ≠ ⊥ := by
  intro h
  have hZ : (center (S.subtype hSM)).map (S.subtype hSM).toSubgroup.subtype = ⊥ :=
    le_bot_iff.mp (h ▸ le_normalClosure)
  have hZ' := (map_eq_bot_iff_of_injective _
    (S.subtype hSM).toSubgroup.subtype_injective).mp hZ
  have hc := restricted_sylow_center_card S M hSM
  rw [hZ', card_bot] at hc
  omega

/-- Every nontrivial normal two-subgroup contains the same explicit closure. -/
theorem centralClosure_le_normal_two_subgroup (S : Sylow 2 Janko4.Model)
    (M : Subgroup Janko4.Model) (hSM : S.toSubgroup ≤ M)
    (E : Subgroup M) [E.Normal] (hp : IsPGroup 2 E) (hne : E ≠ ⊥) :
    centralClosure S M hSM ≤ E :=
  normalClosure_le_normal (center_le_of_normal (S.subtype hSM)
    (restricted_sylow_center_card S M hSM) E hp hne)

/-- A nontrivial two-core supplies elementary structure without assuming
an elementary normal witness in the task's hypotheses. -/
theorem centralClosure_elementary_of_twoCore_ne_bot (S : Sylow 2 Janko4.Model)
    (M : Subgroup Janko4.Model) (hSM : S.toSubgroup ≤ M) (hcore : pCore 2 M ≠ ⊥) :
    IsElementaryAbelian 2 (centralClosure S M hSM) := by
  obtain ⟨E, hEn, hEne, _, hEe, _⟩ := exists_minimal_normal_le_pCore hcore
  let := hEn
  let := hEe
  exact IsElementaryAbelian.of_le (centralClosure_le_normal_two_subgroup S M hSM E
    (IsElementaryAbelian.isPGroup 2 E) hEne)

/-- For these actual Sylow overgroups, the two-core obstruction is exactly
the obstruction to elementary structure of the canonical closure. -/
theorem twoCore_ne_bot_iff_centralClosure_elementary (S : Sylow 2 Janko4.Model)
    (M : Subgroup Janko4.Model) (hSM : S.toSubgroup ≤ M) :
    pCore 2 M ≠ ⊥ ↔ IsElementaryAbelian 2 (centralClosure S M hSM) := by
  refine ⟨centralClosure_elementary_of_twoCore_ne_bot S M hSM, ?_⟩
  intro he hcore
  let := he
  have hle : centralClosure S M hSM ≤ pCore 2 M :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 (centralClosure S M hSM)⟩
  exact centralClosure_ne_bot S M hSM (le_bot_iff.mp (hcore ▸ hle))

/-- An elementary canonical closure has no proper nontrivial M-normal subgroup. -/
theorem centralClosure_minimal (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model)
    (hSM : S.toSubgroup ≤ M) [IsElementaryAbelian 2 (centralClosure S M hSM)]
    (E : Subgroup M) [E.Normal] (hle : E ≤ centralClosure S M hSM) :
    E = ⊥ ∨ E = centralClosure S M hSM := by
  by_cases hne : E = ⊥
  · exact Or.inl hne
  · let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hle
    exact Or.inr (le_antisymm hle (centralClosure_le_normal_two_subgroup S M hSM E
      (IsElementaryAbelian.isPGroup 2 E) hne))

/-- Missing exhaustive exclusion of maximal Sylow overgroups with trivial two-core. -/
@[expose] def MaximalTwoCoreNontrivial : Prop :=
  ∀ (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model),
    IsCoatom M → S.toSubgroup ≤ M → pCore 2 M ≠ ⊥

/-- Independent order calculation for an already elementary canonical closure.
This is a conditional contract, not a classification theorem asserted here. -/
@[expose] def CentralClosureOrderSpectrum : Prop :=
  ∀ (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model),
    IsCoatom M → ∀ (hSM : S.toSubgroup ≤ M),
      IsElementaryAbelian 2 (centralClosure S M hSM) →
      Nat.card (centralClosure S M hSM) = 2 ∨
        Nat.card (centralClosure S M hSM) = 8 ∨
        Nat.card (centralClosure S M hSM) = 2048

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
