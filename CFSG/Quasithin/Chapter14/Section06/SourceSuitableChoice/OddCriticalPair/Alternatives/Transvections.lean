module
public import Theory.Representation.BinaryOffender.DihedralDisplacement
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.PlanePermutation
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Dimensions

/-!
# Transvections in the exchanged-factor action

A transvection cannot interchange two disjoint moved summands of dimension
at least two. It therefore lies in the index-two product of the dihedral
factors. A nontrivial component and the dihedral conjugate-generation bound
force both summands to have dimension two, giving p = 3 and dimension four.

Source: Aschbacher--Smith, original 14.6.13, printed p.1031.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer OrthogonalSource Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

private theorem eq_of_le_index_two {K : Type*} [Group K]
    (D S : Subgroup K) (hi : D.index = 2) (hle : D ≤ S) (hne : S ≠ ⊤) : S = D := by
  have hdiv : S.index ∣ D.index := index_dvd_of_le hle
  rw [hi] at hdiv
  have hsi : S.index = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
    (fun hh => hne (index_eq_one.mp hh))
  have hrel := relIndex_mul_index hle
  rw [hi,hsi] at hrel
  exact le_antisymm (relIndex_eq_one.mp (by omega)) hle

omit [Finite G] in
theorem exchanged_actor_mem_of_first_plane_stable
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    {t : H ⧸ pCore 2 H}
    (ht : t ∈ subspaceStabilizer a.representation
      (subspaceCommutator a.representation ⊤ (actorImage H H1))) :
    t ∈ actorImage H H0 := by
  let A := subspaceCommutator a.representation ⊤ (actorImage H H1)
  let B := subspaceCommutator a.representation ⊤ (actorImage H H2)
  let S := subspaceStabilizer a.representation A
  let D := actorImage H H0
  have hDS : D ≤ S :=
    subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial))
      (actorImage_normalizes H1 H0 (d.first_le.trans d.zero_le) d.normalizes_first)
  have hi : D.index = 2 := by
    have hQ : (QuotientGroup.mk' (pCore 2 H)).ker ≤ H0.subgroupOf H := by
      rw [QuotientGroup.ker_mk']
      intro x hx
      exact d.first_le (d.core_le_first (mem_map_of_mem H.subtype hx))
    exact ((H0.subgroupOf H).index_map_eq (QuotientGroup.mk'_surjective _) hQ).trans d.index
  have hne : S ≠ ⊤ := by
    intro hS
    obtain ⟨x,hx,_,hex⟩ := d.exchanged
    let y : H := ⟨x⁻¹,H.inv_mem (hTH hx)⟩
    let q := QuotientGroup.mk' (pCore 2 H)
    have hy : q y ∈ S := hS ▸ mem_top _
    have hm : A.map (a.representation (q y)) = A := (subspace_map_eq_iff _ _ _).mpr hy
    have he := actorImage_conjugate H1 (d.first_le.trans d.zero_le) y
    change actorImage H (H1.map (MulAut.conj x⁻¹).toMonoidHom) = _ at he
    rw [hex] at he
    have hAB : B = A := by
      change subspaceCommutator a.representation ⊤ (actorImage H H2) = A
      rw [he, ← moved_map_conjugate]
      exact hm
    have hz : A = ⊥ := by
      have hd : Disjoint A B := d.disjoint
      rw [hAB] at hd
      exact disjoint_self.mp hd
    have hd := d.first_dimension
    change (p = 3 ∧ (Module.finrank (ZMod 2) A = 2 ∨ Module.finrank (ZMod 2) A = 4)) ∨
      (p = 5 ∧ Module.finrank (ZMod 2) A = 4) at hd
    rw [hz,finrank_bot] at hd
    omega
  have heq : S = D := eq_of_le_index_two D S hi hDS hne
  change t ∈ D
  rw [← heq]
  exact ht

theorem exchanged_transvection_preserves_planes
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    {t : H ⧸ pCore 2 H}
    (hr : Module.finrank (ZMod 2) (LinearMap.range
      (a.representation t - LinearMap.id)) ≤ 1) :
    (subspaceCommutator a.representation ⊤ (actorImage H H1)).map (a.representation t) =
      subspaceCommutator a.representation ⊤ (actorImage H H1) ∧
    (subspaceCommutator a.representation ⊤ (actorImage H H2)).map (a.representation t) =
      subspaceCommutator a.representation ⊤ (actorImage H H2) := by
  rcases exchanged_spaces_permuted a T hTH p H0 H1 H2 d t with hh | hh
  · exact hh
  · have hb := finrank_le_fixedCodim_of_disjoint_map a.representation
      (subspaceCommutator a.representation ⊤ (actorImage H H1)) (mem_zpowers t)
      (by rw [hh.1]; exact d.disjoint)
    rw [fixedCodim_zpowers_eq_displacement_rank] at hb
    have hd := d.first_dimension
    omega

theorem exchanged_moved_four_of_transvection
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    {t : H ⧸ pCore 2 H} (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range
      (a.representation t - LinearMap.id)) ≤ 1) :
    p = 3 ∧ Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4 := by
  have hstab := (exchanged_transvection_preserves_planes a T hTH p H0 H1 H2 d hr).1
  have hD := exchanged_actor_mem_of_first_plane_stable a T hTH p H0 H1 H2 d
    ((subspace_map_eq_iff _ _ _).mp hstab)
  have hjoin : actorImage H H0 = actorImage H H1 ⊔ actorImage H H2 := by
    unfold actorImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup (d.first_le.trans d.zero_le)
      (d.second_le.trans d.zero_le), d.join_eq]
  have hc : actorImage H H1 ≤ centralizer (actorImage H H2 : Set _) := by
    intro x hx y hy
    exact (d.actors_commute x hx y hy).symm
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (actorImage H H1) (actorImage H H2) d.actors_disjoint hc
  obtain ⟨⟨x,y⟩,hxy⟩ := e.surjective ⟨t,hjoin ▸ hD⟩
  have htxy : (x : H ⧸ pCore 2 H) * y = t := (he x y).symm.trans (congrArg Subtype.val hxy)
  have hx2y2 : (x : H ⧸ pCore 2 H)^2 * (y : H ⧸ pCore 2 H)^2 = 1 := by
    rw [← (d.actors_commute x x.property y y.property).mul_pow, htxy, ht2]
  have hs := disjoint_iff_mul_eq_one.mp d.actors_disjoint
    ((actorImage H H1).pow_mem x.property 2)
    ((actorImage H H2).pow_mem y.property 2) hx2y2
  have hx2 : x ^ 2 = 1 := Subtype.ext hs.1
  have hy2 : y ^ 2 = 1 := Subtype.ext hs.2
  have hbound : Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H H1)) ≤ 2 ∨
      Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H H2)) ≤ 2 := by
    by_cases hx : x = 1
    · have hy : y ≠ 1 := by
        intro hy
        apply ht
        simpa only [hx,hy,Subgroup.coe_one,one_mul] using htxy.symm
      have hry : Module.finrank (ZMod 2)
          (LinearMap.range (a.representation y - LinearMap.id)) ≤ 1 := by
        have hx0 : (x : H ⧸ pCore 2 H) = 1 := congrArg Subtype.val hx
        have hyt := htxy
        rw [hx0,one_mul] at hyt
        rw [hyt]
        exact hr
      exact Or.inr ((dihedral_moved_le_twice_displacement a.representation d.prime
        _ d.second_model.some y hy hy2).trans (by omega))
    · have hrx := displacement_left_le_of_disjoint_moved a.representation
        _ _ d.disjoint x.property y.property
      rw [htxy] at hrx
      exact Or.inl ((dihedral_moved_le_twice_displacement a.representation d.prime
        _ d.first_model.some x hx hx2).trans (by omega))
  have hdim := exchanged_moved_dimension a T hTH p H0 H1 H2 d
  have heq := exchanged_dimensions_eq a T hTH p H0 H1 H2 d
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (subspaceCommutator a.representation ⊤ (actorImage H H1))
    (subspaceCommutator a.representation ⊤ (actorImage H H2))
  rw [d.split,d.disjoint.eq_bot,finrank_bot,add_zero] at hsum
  omega
end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
