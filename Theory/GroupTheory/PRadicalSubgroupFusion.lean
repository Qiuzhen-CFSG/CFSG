module

public import Theory.GroupTheory.ConjugationFamilyWeakClosure
public import Theory.PGroupCore

/-!
# Subgroup fusion through nontrivial p-radical subgroups

Huppert's extremal conjugation family can be reduced to its nontrivial
p-radical members. If an extremal subgroup `U` is not p-radical, the p-core
of its normalizer is a strictly larger subgroup of the fixed Sylow subgroup.
Every element normalizing `U` also normalizes that core. Induction on subgroup
index therefore replaces the step by steps through larger subgroups.

This gives subgroup fusion, including exact conjugating elements for nontrivial
subgroups, rather than only element or character fusion. For groups of Lie
type, the remaining structural input is the Borel--Tits identification of
nontrivial p-radical subgroups with unipotent radicals of parabolics.

Source: the p-core reduction in the Alperin fusion theorem; the Lie-type
application is Aschbacher--Smith, Lemma I.2.5, printed p. 414.
-/

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

namespace SubgroupFusion

variable {G : Type*} [Group G]

/-- Enlarging a conjugation family preserves subgroup fusion control. -/
public theorem ControlsFusion.mono {P : Subgroup G} {family larger : Subgroup G → Prop}
    (hf : ControlsFusion P family) (hinc : ∀ U, family U → larger U) :
    ControlsFusion P larger := by
  intro A hAP g hg
  obtain ⟨h, hd, heq⟩ := hf A hAP g hg
  refine ⟨h, ?_, heq⟩
  clear heq
  induction hd with
  | one => exact .one
  | tail _ hU hUP hAU hh ih => exact .tail ih (hinc _ hU) hUP hAU hh

/-- The p-core of a subgroup's normalizer, embedded in the ambient group. -/
@[expose] public def normalizerPCore (p : ℕ) (U : Subgroup G) : Subgroup G :=
  (pCore p (Subgroup.normalizer (U : Set G))).map
    (Subgroup.normalizer (U : Set G)).subtype

/-- A p-subgroup is contained in the p-core of its normalizer. -/
public theorem le_normalizerPCore {p : ℕ} (U : Subgroup G)
    (hU : IsPGroup p U) : U ≤ normalizerPCore p U := by
  have hsub : IsPGroup p (U.subgroupOf (Subgroup.normalizer (U : Set G))) :=
    hU.of_equiv (Subgroup.subgroupOfEquivOfLe U.le_normalizer).symm
  have hle : U.subgroupOf (Subgroup.normalizer (U : Set G)) ≤
      pCore p (Subgroup.normalizer (U : Set G)) :=
    le_sSup ⟨inferInstance, hsub⟩
  have hmap := Subgroup.map_mono
    (f := (Subgroup.normalizer (U : Set G)).subtype) hle
  simpa only [normalizerPCore, Subgroup.map_subgroupOf_eq_of_le U.le_normalizer] using hmap

/-- Normalizing `U` also normalizes the embedded core of its normalizer. -/
public theorem normalizer_le_normalizerPCore_normalizer (p : ℕ) (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (normalizerPCore p U : Set G) := by
  intro g hg
  apply Subgroup.le_normalizer_map (Subgroup.normalizer (U : Set G)).subtype
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩, ?_, rfl⟩
  exact (Subgroup.normalizer_eq_top (H :=
    pCore p (Subgroup.normalizer (U : Set G)))).symm ▸ Subgroup.mem_top _

variable [Finite G] {p : ℕ} [Fact p.Prime]

/-- Extremality places the normalizer p-core in the fixed Sylow subgroup. -/
public theorem normalizerPCore_le_sylow {S : Sylow p G} {U : Subgroup G}
    (hU : HuppertExtremal S U) : normalizerPCore p U ≤ (S : Subgroup G) := by
  obtain ⟨T, hT⟩ := hU.exists_sylow_normalizer
  have hle : pCore p (Subgroup.normalizer (U : Set G)) ≤
      (T : Subgroup (Subgroup.normalizer (U : Set G))) :=
    pCore_isPGroup.le_sylow_of_normal T
  have hmap := Subgroup.map_mono
    (f := (Subgroup.normalizer (U : Set G)).subtype) hle
  rw [hT] at hmap
  exact hmap.trans inf_le_left

/-- If an extremal subgroup's normalizer contains an ambient Sylow subgroup,
it contains the fixed Sylow subgroup. This applies when the normalizer is a
parabolic subgroup in defining characteristic. -/
public theorem extremal_le_normalizer_of_contains_sylow
    {S : Sylow p G} {U : Subgroup G} (hU : HuppertExtremal S U)
    (P : Sylow p G) (hP : (P : Subgroup G) ≤ Subgroup.normalizer (U : Set G)) :
    (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨T, hT⟩ := hU.exists_sylow_normalizer
  have hcard : Nat.card (T : Subgroup (Subgroup.normalizer (U : Set G))) =
      Nat.card (S : Subgroup G) := by
    calc
      _ = Nat.card (P.subtype hP) := by
        rw [T.card_eq_multiplicity, (P.subtype hP).card_eq_multiplicity]
      _ = Nat.card (P : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
      _ = Nat.card (S : Subgroup G) := by
        rw [P.card_eq_multiplicity, S.card_eq_multiplicity]
  have hmapcard := Subgroup.card_map_of_injective (K := (T : Subgroup _))
    (f := (Subgroup.normalizer (U : Set G)).subtype) Subtype.coe_injective
  rw [hT, hcard] at hmapcard
  have heq : (S : Subgroup G) ⊓ Subgroup.normalizer (U : Set G) =
      (S : Subgroup G) := Subgroup.eq_of_le_of_card_ge inf_le_left hmapcard.ge
  exact heq ▸ inf_le_right

/-- The nontrivial extremal p-radical subgroups of a fixed Sylow subgroup. -/
@[expose] public def PRadicalFamily (S : Sylow p G) (U : Subgroup G) : Prop :=
  U ≠ ⊥ ∧ HuppertExtremal S U ∧ normalizerPCore p U ≤ U

/-- The inequality in the family definition is exactly p-radicality. -/
public theorem PRadicalFamily.normalizerPCore_eq {S : Sylow p G} {U : Subgroup G}
    (hU : PRadicalFamily S U) : normalizerPCore p U = U :=
  le_antisymm hU.2.2 (le_normalizerPCore U (S.isPGroup'.to_le hU.2.1.1))

/-- Nontrivial subgroups have exact decompositions through p-radical members. -/
public theorem pRadical_conjugation_decomposition (S : Sylow p G)
    {A : Subgroup G} (hAS : A ≤ (S : Subgroup G)) (hA : A ≠ ⊥)
    {g : G} (hg : rightConjugate A g ≤ (S : Subgroup G)) :
    HuppertConjugationDecomposition (S : Subgroup G) (PRadicalFamily S) A g := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ A : Subgroup G, A ≤ (S : Subgroup G) → A ≠ ⊥ →
      Nat.card (S : Subgroup G) - Nat.card A = n →
      ∀ g : G, rightConjugate A g ≤ (S : Subgroup G) →
        HuppertConjugationDecomposition (S : Subgroup G) (PRadicalFamily S) A g
  suffices motive (Nat.card (S : Subgroup G) - Nat.card A) from this A hAS hA rfl g hg
  apply Nat.strong_induction_on
  intro k ih A hAS hA hk g hg
  have hlarger : ∀ V : Subgroup G, Nat.card A < Nat.card V →
      V ≤ (S : Subgroup G) → V ≠ ⊥ → ∀ n : G,
      rightConjugate V n ≤ (S : Subgroup G) →
        HuppertConjugationDecomposition (S : Subgroup G) (PRadicalFamily S) V n := by
    intro V hcard hVS hV
    have hbound := Subgroup.card_le_of_le hVS
    exact ih (Nat.card (S : Subgroup G) - Nat.card V) (by omega) V hVS hV rfl
  have hd := HuppertExtremal.conjugation_decomposition S hAS hg
  induction hd with
  | one => exact .one
  | @tail g h U hd hU hUS hAU hh ihstep =>
    have hUbot : U ≠ ⊥ := by
      intro hbot
      have hcur : rightConjugate A g = ⊥ := le_bot_iff.mp (hbot ▸ hAU)
      have hback := congrArg (fun V : Subgroup G => V.conjBy g) hcur
      apply hA
      change (A.conjBy g⁻¹).conjBy g = (⊥ : Subgroup G).conjBy g at hback
      rw [Subgroup.conjBy_inv'] at hback
      simpa only [Subgroup.conjBy, Subgroup.map_bot] using hback
    by_cases hrad : normalizerPCore p U ≤ U
    · exact .tail (ihstep (hAU.trans hUS)) ⟨hUbot, hU, hrad⟩ hUS hAU hh
    · let V := normalizerPCore p U
      have hUV : U < V :=
        lt_of_le_not_ge (le_normalizerPCore U (S.isPGroup'.to_le hUS)) hrad
      have hVS : V ≤ (S : Subgroup G) := normalizerPCore_le_sylow hU
      have hVbot : V ≠ ⊥ := by
        intro hbot
        exact hUbot (le_bot_iff.mp (hbot ▸ hUV.le))
      have hcard : Nat.card A < Nat.card V := by
        have heq : Nat.card A = Nat.card (rightConjugate A g) :=
          (Subgroup.card_map_of_injective (K := A)
            (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective).symm
        have hle := Subgroup.card_le_of_le hAU
        have hlt : Nat.card U < Nat.card V := by
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hUV.le) ?_
          intro heq
          exact hUV.ne (Subgroup.eq_of_le_of_card_ge hUV.le heq.ge)
        omega
      have hhV : h ∈ Subgroup.normalizer (V : Set G) :=
        normalizer_le_normalizerPCore_normalizer p U hh
      have hVh : rightConjugate V h ≤ (S : Subgroup G) := by
        change V.map (MulAut.conj h⁻¹) ≤ (S : Subgroup G)
        rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp
          ((Subgroup.normalizer (V : Set G)).inv_mem hhV)]
        exact hVS
      have hdec := hlarger V hcard hVS hVbot h hVh
      exact (ihstep (hAU.trans hUS)).trans (hdec.mono (hAU.trans hUV.le))

/-- Nontrivial p-radical subgroups control subgroup fusion in every finite group. -/
public theorem pRadical_controlsFusion (S : Sylow p G) :
    ControlsFusion (S : Subgroup G) (PRadicalFamily S) := by
  intro A hAS g hg
  by_cases hA : A = ⊥
  · subst A
    refine ⟨1, .one, ?_⟩
    simp only [rightConjugate, Subgroup.conjBy, Subgroup.map_bot]
  · exact ⟨g, pRadical_conjugation_decomposition S hAS hA hg, rfl⟩

/-- Identifying the nontrivial p-radical candidates suffices to control fusion. -/
public theorem controlsFusion_of_pRadical_identification (S : Sylow p G)
    (family : Subgroup G → Prop)
    (hidentify : ∀ U, PRadicalFamily S U → family U) :
    ControlsFusion (S : Subgroup G) family :=
  (pRadical_controlsFusion S).mono hidentify

end SubgroupFusion
