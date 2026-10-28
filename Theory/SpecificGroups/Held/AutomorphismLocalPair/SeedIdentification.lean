module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.Representative
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

/-!
# Identification of the canonical Held seed

The normal elementary subgroups of order 64 in the fixed four-word representative
are exactly catalogue rows 20 and 21. The intrinsic enumeration gives the list of
possible rows. Its normal-form surjection, together with the checked lower bound
1024 on the representative's order, is bijective, so the certified member lists
give exact row cardinalities. Only the last two rows have 64 members.

For those two rows, kernel checks on the faithful four-point base certify that
every member squares to one and that the four representative generators conjugate
the row generators back into the row. Closure and finiteness extend these checks
to elementary abelianness and intrinsic normality. Thus the join defining the
canonical seed is their literal ambient join, and their normalizers agree.

This discharges the seed premise of the invariant local-pair assembly; the
centralizer and generation certificates are separate results.
Source: Aschbacher--Smith, printed p.526; GLS3 Table 5.3p; the retained ATLAS
HeG1-p2058B0 word data in `MaximalNormalizerCatalogue/IntrinsicEnumeration/source/`.
-/

public section

namespace Held.AutomorphismLocalPair
open Subgroup LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue
open IntrinsicEnumeration ExtensionChecks

private def conjugatesCheck (j : Fin 22) : Bool :=
  (List.finRange 4).all (fun k => (generatorWords j).all (fun w =>
    memberAction (some j) (generatorAction k * wordAction w * (generatorAction k)⁻¹)))

private theorem conjugatesCheck_sound (j : Fin 22) (hc : conjugatesCheck j = true)
    (k : Fin 4) (w : List ℤ) (hw : w ∈ generatorWords j) :
    let g : representative := ⟨generator k, generator_mem k⟩
    g * word w * g⁻¹ ∈ entry j := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp hc k (List.mem_finRange k)) w hw
  apply (memberCheck_eq_true certified_members (some j) _).mp
  simpa only [memberAction, memberCheck, sameAction, same, generatorAction_eq,
    wordAction_eq, normalFormAction_eq, Subgroup.coe_mul, Subgroup.coe_inv,
    map_mul, map_inv] using h

private theorem normal_of_check (j : Fin 22) (hc : conjugatesCheck j = true) :
    (entry j).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  have ht : closure (representative.subtype ⁻¹' Set.range generator) = ⊤ :=
    closure_preimage_eq_top (Set.range generator)
  rw [← ht]
  apply (closure_le _).mpr
  intro g hg
  obtain ⟨k, hk⟩ := hg
  have hg : g = (⟨generator k, generator_mem k⟩ : representative) := Subtype.ext hk.symm
  subst g
  apply mem_normalizer_fintype
  intro x hx
  have hle : (entry j).map
      (MulAut.conj (⟨generator k, generator_mem k⟩ : representative)).toMonoidHom ≤ entry j := by
    rw [entry, MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro _ ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact conjugatesCheck_sound j hc k w hw
  exact hle ⟨x, hx, rfl⟩

private theorem elementary_of_check (j : Fin 22)
    (hc : (members (some j)).all squareAction = true) : IsElementaryAbelian 2 (entry j) := by
  have hp (x : entry j) : x ^ 2 = 1 := by
    obtain ⟨m, hm, he⟩ := (certified_members (some j) x).mp x.property
    apply Subtype.ext
    change (x : representative) ^ 2 = 1
    rw [← he, pow_two]
    apply same_eq_true.mp
    have h := List.all_eq_true.mp hc m hm
    simpa only [squareAction, sameAction, same, normalFormAction_eq, Subgroup.coe_mul,
      Subgroup.coe_one, map_mul, map_one] using h
  exact {
    toIsMulCommutative := ⟨⟨fun x y =>
      (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hp z)) x y).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

private theorem entry_card (j : Fin 22) : Nat.card (entry j) = (members (some j)).toFinset.card := by
  classical
  have hinj : Function.Injective normalForm := by
    apply (normalForm_surjective.bijective_of_nat_card_le ?_).1
    simpa only [Nat.card_fin] using
      InnerNormalizer.representative_card_ge_of_orbit_labels
        InnerNormalizer.orbitSizeLabel_eq_card_orbit
  let f : (members (some j)).toFinset → entry j := fun m =>
    ⟨normalForm m, (certified_members (some j) _).mpr ⟨m, List.mem_toFinset.mp m.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · intro x
      obtain ⟨m, hm, he⟩ := (certified_members (some j) x).mp x.property
      exact ⟨⟨m, List.mem_toFinset.mpr hm⟩, Subtype.ext he⟩
  rw [← Nat.card_eq_finsetCard]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

set_option maxRecDepth 4096 in
private theorem checks20 :
    (members (some 20)).all squareAction = true ∧ conjugatesCheck 20 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem checks21 :
    (members (some 21)).all squareAction = true ∧ conjugatesCheck 21 = true := by
  decide +kernel

private theorem entry_card_filter (j : Fin 22) :
    Nat.card (entry j) = 64 ↔ j = 20 ∨ j = 21 := by
  rw [entry_card]
  have h : ∀ j : Fin 22,
      (members (some j)).toFinset.card = 64 ↔ j = 20 ∨ j = 21 := by decide +kernel
  exact h j

private theorem row20_family :
    (entry 20).Normal ∧ IsElementaryAbelian 2 (entry 20) ∧ Nat.card (entry 20) = 64 :=
  ⟨normal_of_check 20 checks20.2, elementary_of_check 20 checks20.1,
    (entry_card_filter 20).mpr (Or.inl rfl)⟩

private theorem row21_family :
    (entry 21).Normal ∧ IsElementaryAbelian 2 (entry 21) ∧ Nat.card (entry 21) = 64 :=
  ⟨normal_of_check 21 checks21.2, elementary_of_check 21 checks21.1,
    (entry_card_filter 21).mpr (Or.inr rfl)⟩

/-- Exactly the two literal rows are intrinsically normal elementary subgroups of order 64. -/
theorem representative_normal_elementary_order64_iff (E : Subgroup representative) :
    E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 64 ↔
      E = entry 20 ∨ E = entry 21 := by
  constructor
  · rintro ⟨hn, he, hc⟩
    have hne : E ≠ ⊥ := by
      intro h
      subst E
      simp at hc
    obtain ⟨j, rfl⟩ := intrinsicEnumeration representative_isPGroup E hne hn he
    rcases (entry_card_filter j).mp hc with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact row20_family
    · exact row21_family

/-- Identify the canonical invariant join using the complete intrinsic enumeration. -/
theorem representative_largeSeed : largeSeed representative = representativeLargeSeed := by
  have hj : normalElementaryOrderJoin 2 64 representative = entry 20 ⊔ entry 21 := by
    apply le_antisymm
    · simp only [normalElementaryOrderJoin, iSup_le_iff]
      intro E hn he hc
      rcases (representative_normal_elementary_order64_iff E).mp ⟨hn, he, hc⟩ with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le
        (le_normalElementaryOrderJoin 2 64 representative (entry 20)
          row20_family.1 row20_family.2.1 row20_family.2.2)
        (le_normalElementaryOrderJoin 2 64 representative (entry 21)
          row21_family.1 row21_family.2.1 row21_family.2.2)
  rw [largeSeed, hj, Subgroup.map_sup]
  rfl

/-- The actual normalizer consumer, on the unchanged Held carrier and subgroup maps. -/
theorem representative_largeLocal : largeLocal representative = representativeLargeLocal := by
  rw [largeLocal, representative_largeSeed]
  rfl

end Held.AutomorphismLocalPair
