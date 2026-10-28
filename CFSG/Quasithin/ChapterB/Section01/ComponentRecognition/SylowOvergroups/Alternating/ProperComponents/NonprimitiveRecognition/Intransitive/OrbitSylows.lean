module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.OrbitImages
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

/-!
# Sylow subgroups in the literal natural orbit images

Restrict the given Sylow subgroup to the setwise stabilizer of an orbit.
That stabilizer's image contains every even permutation of the orbit,
by extension fixing the complement. Intersecting its Sylow image with
the normal alternating subgroup supplies an alternating Sylow subgroup
inside the literal image of the original overgroup.

If the complement has at least two points, parity can be adjusted there,
and the stabilizer maps onto the full symmetric group on the orbit.
A seven-point orbit cannot have a singleton complement: that would give
a Sylow subgroup of A₈ fixing a point, although a point stabilizer has
even index eight. Thus seven-point orbit images contain symmetric Sylow
subgroups. `Intransitive` consumes both Sylow conclusions in its induction.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), final paragraph.
-/

public section
open Subgroup Equiv MulAction Theory.GroupTheory
open scoped Classical Pointwise
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

private theorem sylow_image_contains_normal_sylow {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (S : Sylow 2 G) (f : G →* H)
    (R N : Subgroup H) [N.Normal] (hR : (S : Subgroup G).map f ≤ R)
    (hN : N ≤ f.range) :
    ∃ T : Sylow 2 N, (T : Subgroup N) ≤ R.subgroupOf N := by
  let Q := S.mapSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  obtain ⟨T, hT⟩ := Q.exists_subgroupOf_eq_of_normal (N.subgroupOf f.range)
  let e : N.subgroupOf f.range ≃* N := subgroupOfEquivOfLe hN
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro t ht
  change t ∈ (T : Subgroup _).map e.toMonoidHom at ht
  obtain ⟨x, hx, rfl⟩ := ht
  rw [hT] at hx
  change x.val ∈ (S : Subgroup G).map f.rangeRestrict at hx
  obtain ⟨g, hg, hge⟩ := hx
  have he : f g = (e x).val := congrArg Subtype.val hge
  change (e x).val ∈ R
  rw [← he]
  exact hR (mem_map_of_mem f hg)

private theorem orbit_stabilizer_le {m : ℕ}
    (X : Subgroup (alternatingGroup (Fin m))) (a : Fin m) :
    X ≤ stabilizer (alternatingGroup (Fin m)) (orbit X a) := by
  intro g hg
  exact smul_orbit (⟨g, hg⟩ : X) a

private theorem orbit_alternating_sylow {m : ℕ}
    (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))) (hS : (S : Subgroup _) ≤ X)
    (a : Fin m) :
    ∃ T : Sylow 2 (alternatingGroup (orbit X a)),
      (T : Subgroup (alternatingGroup (orbit X a))) ≤
        (alternatingOrbitImage X a).subgroupOf (alternatingGroup (orbit X a)) := by
  classical
  let Y := stabilizer (alternatingGroup (Fin m)) (orbit X a)
  have hXY : X ≤ Y := orbit_stabilizer_le X a
  let f : Y →* Perm (orbit X a) := toPermHom Y (orbit X a)
  have hR : ((S.subtype (hS.trans hXY) : Sylow 2 Y) : Subgroup Y).map f ≤
      alternatingOrbitImage X a := by
    rintro g ⟨s, hs, rfl⟩
    refine ⟨⟨s.val, hS hs⟩, ?_⟩
    rfl
  have hN : alternatingGroup (orbit X a) ≤ f.range := by
    intro g hg
    refine ⟨⟨⟨Perm.ofSubtype g, ?_⟩, ?_⟩, ?_⟩
    · simpa [Perm.mem_alternatingGroup] using hg
    · exact Perm.ofSubtype_mem_stabilizer g
    · apply Equiv.ext
      intro x
      apply Subtype.ext
      change Perm.ofSubtype g (x : Fin m) = (g x : Fin m)
      simp
  exact sylow_image_contains_normal_sylow (S.subtype (hS.trans hXY)) f _ _ hR hN

private theorem orbit_symmetric_sylow {m : ℕ}
    (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))) (hS : (S : Subgroup _) ≤ X)
    (a : Fin m) (hc : (orbit X a)ᶜ.Nontrivial) :
    ∃ T : Sylow 2 (Perm (orbit X a)), (T : Subgroup (Perm (orbit X a))) ≤ alternatingOrbitImage X a := by
  classical
  let Y := stabilizer (alternatingGroup (Fin m)) (orbit X a)
  have hXY : X ≤ Y := orbit_stabilizer_le X a
  let f : Y →* Perm (orbit X a) := toPermHom Y (orbit X a)
  refine ⟨(S.subtype (hS.trans hXY)).mapSurjective (f := f)
    (alternatingGroup.stabilizer.surjective_toPerm hc), ?_⟩
  rintro g ⟨s, hs, rfl⟩
  exact ⟨⟨s.val, hS hs⟩, rfl⟩

/-- Every orbit of an intransitive natural action has strictly smaller degree. -/
theorem alternating_orbit_degree_lt {m : ℕ}
    (X : Subgroup (alternatingGroup (Fin m)))
    (hnt : ¬ IsPretransitive X (Fin m)) (a : Fin m) :
    Nat.card (orbit X a) < m := by
  have hn : orbit X a ≠ Set.univ := fun h =>
    hnt ((isPretransitive_iff_orbit_eq_univ a).mpr h)
  simpa only [Nat.card_coe_set_eq, Nat.card_fin] using Set.ncard_lt_card hn

private theorem orbit_seven_complement_nontrivial {m : ℕ} (hm : 6 ≤ m)
    (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))) (hS : (S : Subgroup _) ≤ X)
    (hnt : ¬ IsPretransitive X (Fin m)) (a : Fin m)
    (h7 : Nat.card (orbit X a) = 7) : (orbit X a)ᶜ.Nontrivial := by
  classical
  by_contra hc
  have hc' : (orbit X a)ᶜ.Subsingleton := Set.not_nontrivial_iff.mp hc
  have hlt := alternating_orbit_degree_lt X hnt a
  have hcard : m = 8 := by
    have hsum := Set.ncard_add_ncard_compl (orbit X a)
    have hle := Set.ncard_le_one_iff_subsingleton.mpr hc'
    rw [← Nat.card_coe_set_eq, h7, Nat.card_fin] at hsum
    omega
  subst m
  obtain ⟨b, hb⟩ := Set.nonempty_compl.mpr (fun he =>
    hnt ((isPretransitive_iff_orbit_eq_univ a).mpr he))
  have hfix : X ≤ stabilizer (alternatingGroup (Fin 8)) b := by
    intro x hx
    apply hc' _ hb
    change (⟨x, hx⟩ : X) • b ∉ orbit X a
    intro hx'
    change (⟨x, hx⟩ : X) • b ∈ orbit X a at hx'
    have h : (⟨x, hx⟩ : X)⁻¹ • ((⟨x, hx⟩ : X) • b) ∈ orbit X a :=
      mapsTo_smul_orbit (⟨x, hx⟩ : X)⁻¹ a hx'
    exact hb (by simpa only [inv_smul_smul] using h)
  let : IsPretransitive (alternatingGroup (Fin 8)) (Fin 8) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 8) (by norm_num)
  have hind : (stabilizer (alternatingGroup (Fin 8)) b).index = 8 := by
    simpa using index_stabilizer_of_transitive (G := alternatingGroup (Fin 8)) b
  exact S.not_dvd_index (dvd_trans (by rw [hind]; decide)
    (index_dvd_of_le (hS.trans hfix)))

/-- The literal orbit image contains an alternating Sylow subgroup; at degree
seven, it contains a symmetric Sylow subgroup as well. The latter fact is what
prevents the exceptional smaller-degree model from surviving the induction. -/
theorem alternating_orbit_sylow_control {m : ℕ} (hm : 6 ≤ m)
    (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))) (hS : (S : Subgroup _) ≤ X)
    (hnt : ¬ IsPretransitive X (Fin m)) (a : Fin m) :
    (∃ T : Sylow 2 (alternatingGroup (orbit X a)),
      (T : Subgroup (alternatingGroup (orbit X a))) ≤
        (alternatingOrbitImage X a).subgroupOf (alternatingGroup (orbit X a))) ∧
    (Nat.card (orbit X a) = 7 → ∃ T : Sylow 2 (Perm (orbit X a)),
      (T : Subgroup (Perm (orbit X a))) ≤ alternatingOrbitImage X a) := by
  refine ⟨orbit_alternating_sylow S X hS a, ?_⟩
  intro h7
  exact orbit_symmetric_sylow S X hS a
    (orbit_seven_complement_nontrivial hm S X hS hnt a h7)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
