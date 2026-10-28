module

public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.Ambient
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.Roots
public import Theory.GroupTheory.ConjugacyFamilySpan
public import Mathlib.GroupTheory.Nilpotent

/-!
# A concrete elementary family in the positive Ree model

Take the conjugates of the additive long-root group in the genuine exceptional
fixed-point carrier. The literal root matrices prove elementarity and order q.
The positive-root Sylow contains a member, so the weak closure is nontrivial.
In a simple positive-parameter carrier its normalizer is proper: otherwise the
weak closure would be the whole perfect group inside a two-group.

Sylow conjugacy aligns a model equivalence with a specified source Sylow.
The family, weak closure and normalizer are then transported literally.
These are preparatory results for E.1.14(1), printed p.214 of
`refs/quasithin.pdf`, citing Aschbacher (1982), Lemma 4.7. They do not assert
that the E-members of predecessor rank normalize this weak closure.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
open Subgroup ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry

/-- The full ambient conjugacy orbit of the actual additive long-root group. -/
def rootFamily (m : ℕ) : Set (Subgroup (Model m)) :=
  Set.range fun g : Model m => (longRootGroup m).map (MulAut.conj g).toMonoidHom

/-- The marked positive-root Sylow, using the proved fixed Bruhat odd index. -/
def modelSylow (m : ℕ) : Sylow 2 (Model m) :=
  sylowOfOddIndex m
    (OuterLocal.LargeAutomorphisms.unipotent_index_odd_of_standard (canonicalLocalBlockInput m)
      (LargeLocalSeeds.FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput m)))

@[simp] theorem modelSylow_coe (m : ℕ) :
    (modelSylow m : Subgroup (Model m)) = unipotent m := rfl

/-- The prospective trapping subgroup, with no confinement built into its definition. -/
def modelNormalizer (m : ℕ) : Subgroup (Model m) :=
  normalizer (weakClosure (unipotent m) (rootFamily m) : Set (Model m))

theorem longRoot_elementary (m : ℕ) : IsElementaryAbelian 2 (longRootGroup m) where
  toIsMulCommutative := ⟨⟨by
    intro x y
    apply Subtype.ext
    obtain ⟨a, ha⟩ := (mem_longRootGroup m x.val).mp x.property
    obtain ⟨b, hb⟩ := (mem_longRootGroup m y.val).mp y.property
    change x.val * y.val = y.val * x.val
    rw [← ha, ← hb, ← longRootElement_add, ← longRootElement_add, add_comm]⟩⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    obtain ⟨t, ht⟩ := (mem_longRootGroup m x.val).mp x.property
    change x.val ^ 2 = 1
    rw [← ht]
    exact longRootElement_sq m t

theorem root_mem_family (m : ℕ) : longRootGroup m ∈ rootFamily m := by
  refine ⟨1, ?_⟩
  simp only [map_one]
  exact Subgroup.map_id _

theorem rootFamily_conjugationInvariant (m : ℕ) :
    SubgroupFamily.ConjugationInvariant (rootFamily m) := by
  rintro A ⟨g, rfl⟩ h
  refine ⟨h * g, ?_⟩
  rw [map_map]
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem rootFamily_elementary (m : ℕ) : IsElementaryFamily (rootFamily m) := by
  constructor
  · rintro A ⟨g, rfl⟩
    let := longRoot_elementary m
    exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  · intro g A hA
    exact rootFamily_conjugationInvariant m A hA g

theorem card_longRoot (m : ℕ) : Nat.card (longRootGroup m) = 2 ^ (2 * m + 1) := by
  let e := MonoidHom.ofInjective (f := longRootHom m) (longRootElement_injective m)
  exact (Nat.card_congr e.toEquiv).symm.trans (field_card m)

theorem card_family_member {m : ℕ} {A : Subgroup (Model m)}
    (hA : A ∈ rootFamily m) : Nat.card A = 2 ^ (2 * m + 1) := by
  obtain ⟨g, rfl⟩ := hA
  rw [card_map_of_injective (MulAut.conj g).injective, card_longRoot]

theorem root_le_weakClosure (m : ℕ) :
    longRootGroup m ≤ weakClosure (unipotent m) (rootFamily m) :=
  le_sSup ⟨root_mem_family m, longRootGroup_le_unipotent m⟩

theorem weakClosure_ne_bot (m : ℕ) :
    weakClosure (unipotent m) (rootFamily m) ≠ ⊥ := by
  intro h
  have hr : longRootGroup m = ⊥ := bot_unique (h ▸ root_le_weakClosure m)
  have hc := card_longRoot m
  rw [hr, Subgroup.card_bot] at hc
  have hp : 1 < 2 ^ (2 * m + 1) := Nat.one_lt_pow (by omega) (by decide)
  omega

/-- The whole Borel normalizes the weak closure of the concrete family. -/
theorem borel_le_modelNormalizer (m : ℕ) : borel m ≤ modelNormalizer m := by
  rw [← unipotent_normalizer_eq_borel]
  exact SubgroupFamily.normalizer_le_span_normalizer
    (rootFamily_conjugationInvariant m) (unipotent m)

theorem unipotent_le_modelNormalizer (m : ℕ) : unipotent m ≤ modelNormalizer m :=
  (unipotent m).le_normalizer.trans
    (SubgroupFamily.normalizer_le_span_normalizer (rootFamily_conjugationInvariant m) _)

/-- This properness uses inherited source simplicity, not a new model classification. -/
theorem modelNormalizer_ne_top {m : ℕ} (hm : 0 < m) [IsSimpleGroup (Model m)] :
    modelNormalizer m ≠ ⊤ := by
  intro hn
  let W := weakClosure (unipotent m) (rootFamily m)
  have hW : W ≠ ⊥ := weakClosure_ne_bot m
  have hnormal : W.Normal := normalizer_eq_top_iff.mp hn
  rcases hnormal.eq_bot_or_eq_top with hb | ht
  · exact hW hb
  · have hu : unipotent m = ⊤ := top_unique (ht ▸ weakClosure_le (unipotent m) _)
    have hp := unipotent_isPGroup m
    rw [hu] at hp
    let : Group.IsPerfect (Model m) := ⟨DerivedCarrier.derived_eq_top hm⟩
    exact Group.IsPerfect.not_isNilpotent (Model m) (hp.of_equiv Subgroup.topEquiv).isNilpotent

variable {G : Type*} [Group G] [Finite G]

/-- Adjust a full model equivalence so its image of T is the fixed positive subgroup. -/
theorem exists_aligned_equiv {m : ℕ} (T : Sylow 2 G) (e : G ≃* Model m) :
    ∃ a : G ≃* Model m, (T : Subgroup G).map a.toMonoidHom = unipotent m := by
  let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model m) S (modelSylow m)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hh := congrArg Sylow.toSubgroup hg
  change ((T : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
  rw [map_map, modelSylow_coe] at hh
  exact hh

/-- The literal inverse image of the concrete model family. -/
def family {m : ℕ} (a : G ≃* Model m) : Set (Subgroup G) :=
  {A | A.map a.toMonoidHom ∈ rootFamily m}

/-- The literal inverse image of the model weak-closure normalizer. -/
def overgroup {m : ℕ} (a : G ≃* Model m) : Subgroup G :=
  (modelNormalizer m).comap a.toMonoidHom

omit [Finite G] in
theorem family_elementary {m : ℕ} (a : G ≃* Model m) :
    IsElementaryFamily (family a) := (rootFamily_elementary m).comap_equiv a

omit [Finite G] in
theorem map_weakClosure {m : ℕ} (T : Sylow 2 G) (a : G ≃* Model m)
    (ha : (T : Subgroup G).map a.toMonoidHom = unipotent m) :
    (weakClosure (T : Subgroup G) (family a)).map a.toMonoidHom =
      weakClosure (unipotent m) (rootFamily m) := by
  rw [family, map_weakClosure_equiv, ha]

omit [Finite G] in
theorem normalizer_eq_overgroup {m : ℕ} (T : Sylow 2 G) (a : G ≃* Model m)
    (ha : (T : Subgroup G).map a.toMonoidHom = unipotent m) :
    normalizer (weakClosure (T : Subgroup G) (family a) : Set G) = overgroup a := by
  apply (Subgroup.map_injective (f := a.toMonoidHom) a.injective)
  rw [map_normalizer_eq_of_bijective _ a.bijective, map_weakClosure T a ha,
    overgroup, map_comap_eq_self_of_surjective (f := a.toMonoidHom) a.surjective]
  rfl

omit [Finite G] in
theorem overgroup_ne_top {m : ℕ} (hm : 0 < m) [IsSimpleGroup (Model m)]
    (a : G ≃* Model m) : overgroup a ≠ ⊤ := by
  intro h
  apply modelNormalizer_ne_top hm
  have hh := congrArg (Subgroup.map a.toMonoidHom) h
  simpa only [overgroup, map_comap_eq_self_of_surjective (f := a.toMonoidHom) a.surjective,
    map_top_of_surjective a.toMonoidHom a.surjective] using hh

/-- The source hypotheses construct an aligned literal family and proper
weak-closure normalizer; the two E-member branches are still separate. -/
theorem exists_source_family (T : Sylow 2 G) (L : Subgroup G) [IsSimpleGroup L]
    (hL : L = Theory.GroupTheory.generalizedFitting G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ} (hm : 0 < m)
    (e : L ≃* commutator (Model m)) :
    ∃ a : G ≃* Model m,
      (T : Subgroup G).map a.toMonoidHom = unipotent m ∧
      IsElementaryFamily (family a) ∧ overgroup a ≠ ⊤ ∧
      normalizer (weakClosure (T : Subgroup G) (family a) : Set G) = overgroup a := by
  let : IsSimpleGroup (Model m) := (e.trans (DerivedCarrier.derivedEquiv hm)).symm.isSimpleGroup
  obtain ⟨a, ha⟩ := exists_aligned_equiv T (positiveAmbientEquiv T L hL hgen hm e)
  exact ⟨a, ha, family_elementary a, overgroup_ne_top hm a, normalizer_eq_overgroup T a ha⟩

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
