module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Embedding
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Geometry

/-!
# Atlas parabolics as derived intersections in the binary Ree group

The canonical embedding sends the eight positive Parrott generators into the
positive root subgroup and the two reflections to the specified Suzuki and
linear Weyl lifts. These root membership statements first give the three
subgroup inclusions. Every Ree subgroup containing the positive subgroup meets
the derived group in index two: the positive subgroup has order 4096, which
does not divide the derived group's order. The already proved local orders
then turn the inclusions into equalities.

Restricting `atlasDerivedEquiv` gives an isomorphism of the actual inclusion
amalgams, with middle group the Ree Borel intersected with the derived group.
All three component maps retain the canonical ambient embedding, and both
inclusion squares commute. The argument uses the proved full-Ree projections
and orders; it requires no Tits quotient calculation or automorphism coverage.

Source: Parrott (1972), §5, printed p.683, with its root-word conventions;
Aschbacher--Smith, F.1.11--12, printed pp.262--264. This comparison does not
assert the disputed first-core package printed in F.1.12(I)(9).
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.DerivedTits.Realization
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open ReeF4.Parabolics.Binary.FixedGeometry
open Theory.GroupTheory

private theorem pair_mem_positive (i : Fin 4) : pairElement i ∈ splitUnipotent 0 := by
  rw [pairElement_eq]
  apply Subgroup.mul_mem
  · exact Subgroup.subset_closure ⟨_, 1,
      ((rootBlocks .positive).roots (.inl (i, 0))).property, rfl⟩
  · exact Subgroup.subset_closure ⟨_, 1,
      ((rootBlocks .positive).roots (.inl (i, 1))).property, rfl⟩

private theorem quartet_mem_positive (i : Fin 4) :
    quartetElement i ∈ splitUnipotent 0 := by
  rw [quartetElement_eq]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · exact Subgroup.subset_closure ⟨_, 1,
        ((rootBlocks .positive).roots (.inr (i, 0))).property, rfl⟩
    · exact Subgroup.subset_closure ⟨_, 1,
        ((rootBlocks .positive).roots (.inr (i, 1))).property, rfl⟩
  · exact Subgroup.subset_closure ⟨_, 1,
      ((rootBlocks .positive).roots (.inr (i, 3))).property, rfl⟩

private theorem u_mem_positive (i : Fin 8) : u i ∈ splitUnipotent 0 := by
  fin_cases i <;> simp [u, pair_mem_positive, quartet_mem_positive]

/-- The eight positive Parrott words lie in the positive Ree root subgroup. -/
theorem atlas_sylow_map_le : ExceptionalParabolics.S.map atlasEmbedding ≤ S := by
  rw [Subgroup.map_le_iff_le_comap, ExceptionalParabolics.S,
    atlas1600SylowTwoSubgroup_eq]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    change toSplitGroup 0 (atlasEmbedding _) ∈ splitUnipotent 0 <;>
    rw [atlasEmbedding_generator_matrix]
  all_goals
    simp only [assignment]
    first
    | exact u_mem_positive _
    | exact (splitUnipotent 0).mul_mem (u_mem_positive _) (u_mem_positive _)
    | exact (splitUnipotent 0).mul_mem (u_mem_positive _)
        ((splitUnipotent 0).inv_mem (u_mem_positive _))

/-- The first reflection is the Suzuki Weyl lift in the first root seed. -/
theorem atlas_first_map_le : ExceptionalParabolics.first.map atlasEmbedding ≤ first := by
  rw [ExceptionalParabolics.first, Subgroup.map_sup]
  apply sup_le (atlas_sylow_map_le.trans sylow_le_first)
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro x (rfl : x = atlas1600ParrottAssignment .r1)
  change atlasEmbedding (atlas1600ParrottAssignment .r1) ∈ first
  have he : atlasEmbedding (atlas1600ParrottAssignment .r1) = weylLift 0 .suzuki := by
    apply toSplitGroup_injective 0
    rw [atlasEmbedding_generator_matrix, toSplitGroup_weylLift]
    rfl
  rw [he]
  exact weylLift_mem_seed 0 .suzuki

/-- The second reflection is the linear Weyl lift in the second root seed. -/
theorem atlas_second_map_le : ExceptionalParabolics.second.map atlasEmbedding ≤ second := by
  rw [ExceptionalParabolics.second, Subgroup.map_sup]
  apply sup_le (atlas_sylow_map_le.trans sylow_le_second)
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro x (rfl : x = atlas1600ParrottAssignment .r8)
  change atlasEmbedding (atlas1600ParrottAssignment .r8) ∈ second
  have he : atlasEmbedding (atlas1600ParrottAssignment .r8) = weylLift 0 .linear := by
    apply toSplitGroup_injective 0
    rw [atlasEmbedding_generator_matrix, toSplitGroup_weylLift]
    rfl
  rw [he]
  exact weylLift_mem_seed 0 .linear

/-- Order of the full Suzuki-side parabolic, from its proved core and projection. -/
theorem first_card : Nat.card first = 20480 := by
  have hq : Nat.card (first ⧸ pCore 2 first) = 20 :=
    (Nat.card_congr firstCoreQuotientEquiv.toEquiv).trans
      BenderSuzuki.MatrixGroups.suzukiZero_card
  rw [(pCore 2 first).card_eq_card_quotient_mul_card_subgroup, hq, first_core_card]

/-- Order of the full linear-side parabolic, from its proved core and projection. -/
theorem second_card : Nat.card second = 12288 := by
  have hl : Nat.card (LargeLocalSeeds.LinearQuotient 0) = 6 := by
    have h := Atlas.ExceptionalSupport.card_psl_mul (F := CoefficientField 0) 2
    simpa [← Nat.card_eq_fintype_card, field_card, Fin.prod_univ_succ] using h
  have hq : Nat.card (second ⧸ pCore 2 second) = 6 :=
    (Nat.card_congr secondCoreQuotientEquiv.toEquiv).trans hl
  rw [(pCore 2 second).card_eq_card_quotient_mul_card_subgroup, hq, second_core_card]

private theorem sylow_not_le_derived : ¬ S ≤ commutator (Model 0) := by
  intro h
  have hd := Subgroup.card_dvd_of_le h
  have hc : Nat.card (commutator (Model 0)) = 17971200 :=
    (Nat.card_congr atlasDerivedEquiv.toEquiv).symm.trans atlas1600Group_card
  rw [sylow_card, hc] at hd
  norm_num at hd

private theorem derived_relIndex (P : Subgroup (Model 0)) (hP : S ≤ P) :
    (commutator (Model 0)).relIndex P = 2 := by
  have hd := Subgroup.relIndex_dvd_index_of_normal (commutator (Model 0)) P
  rw [derived_index] at hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
  · exact (sylow_not_le_derived (hP.trans (Subgroup.relIndex_eq_one.mp h))).elim
  · exact h

private theorem card_inter_derived (P : Subgroup (Model 0)) (hP : S ≤ P) :
    Nat.card (P ⊓ commutator (Model 0) : Subgroup (Model 0)) * 2 = Nat.card P := by
  have h := (commutator (Model 0)).subgroupOf P |>.card_mul_index
  have hc : Nat.card ((commutator (Model 0)).subgroupOf P) =
      Nat.card (P ⊓ commutator (Model 0) : Subgroup (Model 0)) := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hc, show ((commutator (Model 0)).subgroupOf P).index = 2 from
    derived_relIndex P hP] at h
  exact h

private theorem map_le_derived (H : Subgroup Atlas1600Group) :
    H.map atlasEmbedding ≤ commutator (Model 0) := by
  rw [← atlasEmbedding_range]
  exact H.map_le_range atlasEmbedding

/-- Literal ambient comparison of the two marked Sylow subgroups. -/
theorem atlas_sylow_map :
    ExceptionalParabolics.S.map atlasEmbedding = S ⊓ commutator (Model 0) := by
  apply Subgroup.eq_of_le_of_card_ge (le_inf atlas_sylow_map_le (map_le_derived _))
  have h := card_inter_derived S le_rfl
  rw [sylow_card] at h
  rw [Subgroup.card_map_of_injective atlasEmbedding_injective,
    ExceptionalParabolics.sylow_card]
  omega

/-- The Atlas first parabolic is exactly the first Ree derived intersection. -/
theorem atlas_first_map :
    ExceptionalParabolics.first.map atlasEmbedding = first ⊓ commutator (Model 0) := by
  apply Subgroup.eq_of_le_of_card_ge (le_inf atlas_first_map_le (map_le_derived _))
  have h := card_inter_derived first sylow_le_first
  rw [first_card] at h
  rw [Subgroup.card_map_of_injective atlasEmbedding_injective,
    ExceptionalParabolics.first_card]
  omega

/-- The Atlas second parabolic is exactly the second Ree derived intersection. -/
theorem atlas_second_map :
    ExceptionalParabolics.second.map atlasEmbedding = second ⊓ commutator (Model 0) := by
  apply Subgroup.eq_of_le_of_card_ge (le_inf atlas_second_map_le (map_le_derived _))
  have h := card_inter_derived second sylow_le_second
  rw [second_card] at h
  rw [Subgroup.card_map_of_injective atlasEmbedding_injective,
    ExceptionalParabolics.second_card]
  omega

private theorem map_atlasDerivedEquiv {H : Subgroup Atlas1600Group}
    {K : Subgroup (Model 0)}
    (h : H.map atlasEmbedding = K ⊓ commutator (Model 0)) :
    H.map atlasDerivedEquiv.toMonoidHom = K.subgroupOf (commutator (Model 0)) := by
  apply Subgroup.map_injective (commutator (Model 0)).subtype_injective
  rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
  exact h

/-- The Sylow comparison in the carrier of the derived group. -/
theorem atlas_sylow_map_derived :
    ExceptionalParabolics.S.map atlasDerivedEquiv.toMonoidHom =
      S.subgroupOf (commutator (Model 0)) :=
  map_atlasDerivedEquiv atlas_sylow_map

/-- The first parabolic comparison in the carrier of the derived group. -/
theorem atlas_first_map_derived :
    ExceptionalParabolics.first.map atlasDerivedEquiv.toMonoidHom =
      first.subgroupOf (commutator (Model 0)) :=
  map_atlasDerivedEquiv atlas_first_map

/-- The second parabolic comparison in the carrier of the derived group. -/
theorem atlas_second_map_derived :
    ExceptionalParabolics.second.map atlasDerivedEquiv.toMonoidHom =
      second.subgroupOf (commutator (Model 0)) :=
  map_atlasDerivedEquiv atlas_second_map

/-- The Atlas overlap maps onto the actual Ree Borel inside the derived group. -/
theorem atlas_overlap_map_derived :
    ExceptionalParabolics.overlap.map atlasDerivedEquiv.toMonoidHom =
      B.subgroupOf (commutator (Model 0)) := by
  rw [ExceptionalParabolics.overlap_eq_sylow, borel_eq_sylow]
  exact atlas_sylow_map_derived

/-- The two Ree parabolics and their Borel, all restricted to the derived group. -/
def derivedAmalgam : RankTwoAmalgam
    (first.subgroupOf (commutator (Model 0)))
    (B.subgroupOf (commutator (Model 0)))
    (second.subgroupOf (commutator (Model 0))) :=
  RankTwoAmalgam.ofSubgroups _ _ _
    (Subgroup.subgroupOf_mono _ borel_le_first)
    (Subgroup.subgroupOf_mono _ borel_le_second)

/-- The canonical ambient equivalence restricts to an isomorphism of marked amalgams. -/
def atlasAmalgamIso : RankTwoAmalgam.Iso ExceptionalParabolics.amalgam derivedAmalgam :=
  RankTwoAmalgam.ofSubgroupsIso atlasDerivedEquiv inf_le_left inf_le_right
    (Subgroup.subgroupOf_mono _ borel_le_first)
    (Subgroup.subgroupOf_mono _ borel_le_second)
    atlas_first_map_derived atlas_overlap_map_derived atlas_second_map_derived

/-- The left component is the specified embedding on ambient elements. -/
@[simp] theorem atlasAmalgamIso_left_coe (x : ExceptionalParabolics.first) :
    ((atlasAmalgamIso.left x : commutator (Model 0)) : Model 0) =
      atlasEmbedding x := rfl

/-- The middle component is the same specified ambient embedding. -/
@[simp] theorem atlasAmalgamIso_middle_coe (x : ExceptionalParabolics.overlap) :
    ((atlasAmalgamIso.middle x : commutator (Model 0)) : Model 0) =
      atlasEmbedding x := rfl

/-- The right component is the same specified ambient embedding. -/
@[simp] theorem atlasAmalgamIso_right_coe (x : ExceptionalParabolics.second) :
    ((atlasAmalgamIso.right x : commutator (Model 0)) : Model 0) =
      atlasEmbedding x := rfl

/-- Compatibility with the literal left subgroup inclusion. -/
theorem atlasAmalgamIso_left_commutes (x : ExceptionalParabolics.overlap) :
    atlasAmalgamIso.left (ExceptionalParabolics.amalgam.left x) =
      derivedAmalgam.left (atlasAmalgamIso.middle x) :=
  atlasAmalgamIso.left_commutes x

/-- Compatibility with the literal right subgroup inclusion. -/
theorem atlasAmalgamIso_right_commutes (x : ExceptionalParabolics.overlap) :
    atlasAmalgamIso.right (ExceptionalParabolics.amalgam.right x) =
      derivedAmalgam.right (atlasAmalgamIso.middle x) :=
  atlasAmalgamIso.right_commutes x

end Tits.ExceptionalParabolics.FullRee
