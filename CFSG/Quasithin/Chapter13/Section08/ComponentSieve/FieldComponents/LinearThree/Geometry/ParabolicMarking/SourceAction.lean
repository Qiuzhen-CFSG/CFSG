module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.SourceGeneration
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The literal source seed and its conjugation action

The inclusion V₃ ≤ U_H induces an injective map V₃/V₁ → U_H/V₁.
Its additive image is already a binary subspace, so taking its linear span
adds no vectors. We identify that section with `Geometry.seedSpace` and
transport its order and its full four-group automorphism action. A two-group
cannot have this action: a nonzero fixed vector and transitivity would force
the seed to have at most two elements. The source centralizer identity also
makes the actual H/O₂(H) representation faithful.

The input `SeedAction` records the earlier action on the literal V₃/V₁,
including its conjugation formula; it is not an unrelated representation or
an assumed cyclic-vector conclusion. These are conditional source adapters,
not the compatible parabolic marking or Lemma 13.8.19 itself.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation
13.2.1 (printed p.877), the standing setup of §13.8 (p.946), and the first
paragraph of the proof of 13.8.19 (p.953).
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

def seedHom : V₃ →* Source.Utilde H V₃ V₁ :=
  (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))).comp
    (Subgroup.inclusion (le_conjugateSpanBy V₃ H))

omit [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))] in
theorem seedHom_ker : (seedHom H V₃ V₁).ker = V₁.subgroupOf V₃ := by
  ext v
  exact QuotientGroup.eq_one_iff _

theorem seedSpace_eq_image : seedSpace H V₃ V₁ =
    AddSubgroup.toZModSubmodule 2 (seedHom H V₃ V₁).range.toAddSubgroup := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    exact ⟨v, rfl⟩
  · rintro v ⟨w, hw⟩
    exact Submodule.subset_span ⟨w, congrArg Additive.ofMul hw⟩

theorem mem_seedSpace_iff (v : Additive (Source.Utilde H V₃ V₁)) :
    v ∈ seedSpace H V₃ V₁ ↔ ∃ w : V₃, seedVector H V₃ V₁ w = v := by
  rw [seedSpace_eq_image]
  rfl

variable [(V₁.subgroupOf V₃).Normal]

/-- The inclusion of the literal section V₃/V₁ in U_H/V₁. -/
def seedSectionHom : V₃ ⧸ V₁.subgroupOf V₃ →* Source.Utilde H V₃ V₁ :=
  QuotientGroup.lift (V₁.subgroupOf V₃) (seedHom H V₃ V₁)
    (seedHom_ker H V₃ V₁).ge

omit [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))] in
theorem seedSectionHom_injective : Function.Injective (seedSectionHom H V₃ V₁) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (seedHom_ker H V₃ V₁).symm

/-- Every vector in the linear seed is already a single source coset. -/
noncomputable def seedSectionEquiv :
    V₃ ⧸ V₁.subgroupOf V₃ ≃ seedSpace H V₃ V₁ :=
  Equiv.ofBijective (fun q => ⟨Additive.ofMul (seedSectionHom H V₃ V₁ q), by
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf V₃) q
    exact Submodule.subset_span ⟨v, rfl⟩⟩) ⟨by
      intro q r h
      apply seedSectionHom_injective H V₃ V₁
      exact congrArg (fun v : seedSpace H V₃ V₁ => v.val.toMul) h, by
      rintro ⟨v, hv⟩
      obtain ⟨w, rfl⟩ := (mem_seedSpace_iff H V₃ V₁ v).mp hv
      exact ⟨QuotientGroup.mk' (V₁.subgroupOf V₃) w, rfl⟩⟩

@[simp] theorem seedSectionEquiv_mk (v : V₃) :
    (seedSectionEquiv H V₃ V₁ (QuotientGroup.mk' (V₁.subgroupOf V₃) v)).val =
      seedVector H V₃ V₁ v := rfl

theorem seedSectionEquiv_eq_zero_iff (q : V₃ ⧸ V₁.subgroupOf V₃) :
    (seedSectionEquiv H V₃ V₁ q).val = 0 ↔ q = 1 := by
  change seedSectionHom H V₃ V₁ q = 1 ↔ q = 1
  exact (seedSectionHom_injective H V₃ V₁).eq_iff' (map_one _)

theorem seed_card_of_section (hcard : Nat.card (V₃ ⧸ V₁.subgroupOf V₃) = 4) :
    Nat.card (seedSpace H V₃ V₁) = 4 :=
  (Nat.card_congr (seedSectionEquiv H V₃ V₁)).symm.trans hcard


/-- The source orders |V₃| = 8 and |V₁| = 2 give four seed vectors. -/
theorem seed_card_of_source_orders (h13 : V₁ ≤ V₃)
    (h1 : Nat.card V₁ = 2) (h3 : Nat.card V₃ = 8) :
    Nat.card (seedSpace H V₃ V₁) = 4 := by
  apply seed_card_of_section
  have hd : Nat.card (V₁.subgroupOf V₃) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h13).toEquiv).trans h1
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (V₁.subgroupOf V₃)
  rw [h3, hd] at hc
  omega

/-- The earlier statement that L₁T induces the full automorphism group of
V₃/V₁, with its actual conjugation formula, before identifying any parabolic. -/
structure SeedAction (P : Subgroup G) (hP : P ≤ normalizer (V₃ : Set G)) where
  action : P →* MulAut (V₃ ⧸ V₁.subgroupOf V₃)
  surjective : Function.Surjective action
  conjugation : ∀ (p : P) (v : V₃),
    action p (QuotientGroup.mk' (V₁.subgroupOf V₃) v) =
      QuotientGroup.mk' (V₁.subgroupOf V₃)
        ⟨p.val * v.val * p.val⁻¹,
          (mem_normalizer_iff.mp (hP p.property) v.val).mp v.property⟩

variable {H V₃ V₁}

theorem seedSectionEquiv_action (act : SourceAction H V₃ V₁)
    {P : Subgroup G} {hP : P ≤ normalizer (V₃ : Set G)}
    (a : SeedAction V₃ V₁ P hP) (hPH : P ≤ H)
    (p : P) (q : V₃ ⧸ V₁.subgroupOf V₃) :
    (seedSectionEquiv H V₃ V₁ (a.action p q)).val =
      act.representation (QuotientGroup.mk' (pCore 2 H) ⟨p.val, hPH p.property⟩)
        (seedSectionEquiv H V₃ V₁ q).val := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf V₃) q
  rw [a.conjugation, seedSectionEquiv_mk, seedSectionEquiv_mk]
  exact (act.conjugation ⟨p.val, hPH p.property⟩
    ⟨v.val, le_conjugateSpanBy V₃ H v.property⟩).symm

theorem seed_transitive (act : SourceAction H V₃ V₁)
    [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]
    {P : Subgroup G} {hP : P ≤ normalizer (V₃ : Set G)}
    (a : SeedAction V₃ V₁ P hP) (hPH : P ≤ H) :
    ∀ u ∈ seedSpace H V₃ V₁, u ≠ 0 →
      ∀ v ∈ seedSpace H V₃ V₁, v ≠ 0 →
        ∃ p ∈ Source.starImage H P, act.representation p u = v := by
  classical
  intro u hu hun v hv hvn
  obtain ⟨x, hx⟩ := (seedSectionEquiv H V₃ V₁).surjective ⟨u, hu⟩
  obtain ⟨y, hy⟩ := (seedSectionEquiv H V₃ V₁).surjective ⟨v, hv⟩
  have hxval : (seedSectionEquiv H V₃ V₁ x).val = u := congrArg Subtype.val hx
  have hyval : (seedSectionEquiv H V₃ V₁ y).val = v := congrArg Subtype.val hy
  have hxn : x ≠ 1 := by
    intro he
    exact hun (hxval.symm.trans ((seedSectionEquiv_eq_zero_iff H V₃ V₁ x).mpr he))
  have hyn : y ≠ 1 := by
    intro he
    exact hvn (hyval.symm.trans ((seedSectionEquiv_eq_zero_iff H V₃ V₁ y).mpr he))
  let f : MulAut (V₃ ⧸ V₁.subgroupOf V₃) :=
    IsKleinFour.mulEquiv (Equiv.swap x y) (Equiv.swap_apply_of_ne_of_ne hxn.symm hyn.symm)
  obtain ⟨p, hp⟩ := a.surjective f
  refine ⟨QuotientGroup.mk' (pCore 2 H) ⟨p.val, hPH p.property⟩,
    ⟨⟨p.val, hPH p.property⟩, p.property, rfl⟩, ?_⟩
  rw [← hxval, ← seedSectionEquiv_action act a hPH p x, hp]
  change (seedSectionEquiv H V₃ V₁ (Equiv.swap x y x)).val = v
  simpa only [Equiv.swap_apply_left] using hyval


/-- All seed hypotheses used by `cyclic_seed`, deduced from the earlier
four-group section and its full conjugation action. -/
theorem source_seed_inputs (act : SourceAction H V₃ V₁)
    [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]
    {P : Subgroup G} {hP : P ≤ normalizer (V₃ : Set G)}
    (a : SeedAction V₃ V₁ P hP) (hPH : P ≤ H) :
    Nat.card (seedSpace H V₃ V₁) = 4 ∧
    (∀ p ∈ Source.starImage H P, ∀ v ∈ seedSpace H V₃ V₁,
      act.representation p v ∈ seedSpace H V₃ V₁) ∧
    (∀ u ∈ seedSpace H V₃ V₁, u ≠ 0 →
      ∀ v ∈ seedSpace H V₃ V₁, v ≠ 0 →
        ∃ p ∈ Source.starImage H P, act.representation p u = v) :=
  ⟨seed_card_of_section H V₃ V₁ IsKleinFour.card_four,
    seedSpace_invariant H V₃ V₁ act P hP, seed_transitive act a hPH⟩


/-- The full seed action prevents the source parabolic image from being a
two-group. A two-group fixes a nonzero seed vector, whereas transitivity
would then fix all three nonzero vectors individually. -/
theorem seed_image_not_two [Finite G] (act : SourceAction H V₃ V₁)
    [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]
    {P : Subgroup G} {hP : P ≤ normalizer (V₃ : Set G)}
    (a : SeedAction V₃ V₁ P hP) (hPH : P ≤ H) :
    ¬ IsPGroup 2 (Source.starImage H P) := by
  classical
  intro hp
  obtain ⟨hc, hs, ht⟩ := source_seed_inputs act a hPH
  obtain ⟨m, hm, hmn, hfixed⟩ := fixed_seed act.representation
    (Source.starImage H P) hp (seedSpace H V₃ V₁) hc hs
  let D := seedSpace H V₃ V₁
  let m' : D := ⟨m, hm⟩
  let : Fintype D := Fintype.ofFinite D
  have hall : (Finset.univ : Finset D) ⊆ {0, m'} := by
    intro v _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hv : v.val = 0
    · exact Or.inl (Subtype.ext hv)
    · right
      obtain ⟨p, hp, he⟩ := ht m hm hmn v.val v.property hv
      exact Subtype.ext (he.symm.trans (hfixed p hp))
  have hle := Finset.card_le_card hall
  have hpair : ({0, m'} : Finset D).card ≤ 2 := by
    calc
      _ ≤ ({m'} : Finset D).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  have hcard : Fintype.card D = 4 := (Nat.card_eq_fintype_card).symm.trans hc
  simp only [Finset.card_univ] at hle
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
variable {G : Type*} [Group G]
variable {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Faithfulness follows from the source equality Q_H = C_H(U_H/V₁).
The hypothesis concerns conjugation in H, before passing to H/O₂(H). -/
theorem faithful_of_source_centralizer (act : SourceAction H V₃ V₁)
    (hcentralizer : ∀ h : H,
      (∀ u : Source.UH H V₃,
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (conjugateUH H V₃ h u) =
          QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) → h ∈ pCore 2 H) :
    Function.Injective act.representation := by
  apply (MonoidHom.ker_eq_bot_iff act.representation).mp
  apply le_bot_iff.mp
  intro g hg
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
  apply (QuotientGroup.eq_one_iff h).mpr
  apply hcentralizer h
  intro u
  have he := congrArg (fun f => f (Additive.ofMul
    (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)))
    (MonoidHom.mem_ker.mp hg)
  rw [act.conjugation] at he
  exact congrArg Additive.toMul he
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
