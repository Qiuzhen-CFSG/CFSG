module

public import Theory.SpecificGroups.Suzuki.TwoConjugateWitness.RootPair
public import Theory.SpecificGroups.Suzuki.ElementaryNormalizer
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Prescribed Sylow geometry for Suzuki two-conjugate witnesses

Conjugate the prescribed ambient Sylow subgroup to the concrete root group,
construct the Weyl pair there, and transport the same pair back. A subgroup
containing a nontrivial elementary part of the original Sylow has precisely
the original Sylow intersection as a Sylow subgroup. Partition uniqueness
identifies its normalizer with the original Borel intersection.

Source: Aschbacher--Smith, E.2.7, printed p.218, Bender-group paragraph.
-/

public section
noncomputable section
namespace BenderSuzuki.MatrixGroups
open Subgroup PFAppendixIII

private theorem pair_map {G D : Type*} [Group G] [Group D]
    (f : G →* D) (V : Subgroup G) (g : G) :
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f =
      V.map f ⊔ (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup, map_map, map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv]

/-- A prescribed ambient Sylow subgroup gives an internal two-conjugate
pair that is nonsolvable and escapes that Sylow's normalizer. -/
theorem suzuki_exists_internal_elementary_pair {m : ℕ} (hm : 0 < m)
    (S : Sylow 2 (SuzukiMatrixGroup m))
    (V : Subgroup (SuzukiMatrixGroup m)) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hcard : 2 < Nat.card V) :
    ∃ g : SuzukiMatrixGroup m,
      g ∈ V ⊔ V.map (MulAut.conj g).toMonoidHom ∧
      g ∉ normalizer (S : Set (SuzukiMatrixGroup m)) ∧
      ¬ Group.IsSolvable (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup _) := by
  obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) S R
  let e := MulAut.conj c
  have hS : (S : Subgroup (SuzukiMatrixGroup m)).map e.toMonoidHom = SuzukiRootSubgroup m := by
    rw [← hR, ← hc]
    rfl
  let U := V.map e.toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hUR : U ≤ SuzukiRootSubgroup m := by rw [← hS]; exact map_mono hVS
  have hUcard : 2 < Nat.card U := by
    rw [card_map_of_injective e.injective]
    exact hcard
  have hUne : U ≠ ⊥ := by intro h; rw [h, card_bot] at hUcard; omega
  let g := e.symm (suzukiWeyl m)
  let H := V ⊔ V.map (MulAut.conj g).toMonoidHom
  have hmap : H.map e.toMonoidHom =
      U ⊔ U.map (MulAut.conj (suzukiWeyl m)).toMonoidHom := by
    rw [pair_map]
    simp only [g, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl
  have hw : e g ∈ H.map e.toMonoidHom := by
    rw [hmap]
    simpa only [g, MulEquiv.apply_symm_apply] using suzuki_weyl_mem_elementary_pair hm U hUR hUne
  refine ⟨g, ?_, ?_, ?_⟩
  · exact (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hw
  · intro hg
    have hN := mem_map_of_mem e.toMonoidHom hg
    have hNeq := map_normalizer_eq_of_bijective (S : Subgroup (SuzukiMatrixGroup m))
      (f := e.toMonoidHom) e.bijective
    rw [S.coe_coe, hS, suzukiRootSubgroup_normalizer m hm] at hNeq
    rw [hNeq] at hN
    have he : suzukiWeyl m • suzukiOvoidInfinity m = suzukiOvoidInfinity m := by
      simpa only [g, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff] using hN
    exact suzukiOvoidInfinity_ne_zero m ((suzukiWeyl_smul_infinity m).symm.trans he).symm
  · intro hsol
    let : Group.IsSolvable H := hsol
    let d := H.equivMapOfInjective e.toMonoidHom e.injective
    have hs : Group.IsSolvable (H.map e.toMonoidHom) :=
      Group.isSolvable_of_surjective (f := d.toMonoidHom) d.surjective
    rw [hmap] at hs
    exact suzuki_elementary_pair_not_isSolvable hm U hUR hUcard hs

/-- In a subgroup containing a nontrivial elementary part of a prescribed
Suzuki Sylow subgroup, its intersection is Sylow and the corresponding
normalizer is exactly the original ambient normalizer intersection. -/
theorem suzuki_subgroup_sylow_normalizer {m : ℕ} (hm : 0 < m)
    (S : Sylow 2 (SuzukiMatrixGroup m)) (H V : Subgroup (SuzukiMatrixGroup m))
    [IsElementaryAbelian 2 V] (hVS : V ≤ S) (hVH : V ≤ H) (hne : V ≠ ⊥) :
    (∃ P : Sylow 2 H, (P : Subgroup H) = (S : Subgroup _).subgroupOf H) ∧
      normalizer ((S : Subgroup _).subgroupOf H : Set H) =
        (normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf H := by
  obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) R S
  have hS : (S : Subgroup (SuzukiMatrixGroup m)) =
      (SuzukiRootSubgroup m).map (MulAut.conj c).toMonoidHom := by
    rw [← hR, ← hc]
    rfl
  obtain ⟨t, htV, ht⟩ := V.bot_or_exists_ne_one.resolve_left hne
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htV) ht
  have hfix := (suzukiRootSubgroup_conjugate_fixed_iff hm c t
    (hS ▸ hVS htV) ht (c • suzukiOvoidInfinity m)).mpr rfl
  let a : suzukiInvolutionSubaction H :=
    ⟨c • suzukiOvoidInfinity m, ⟨t, hVH htV⟩,
      (Subgroup.orderOf_coe ⟨t, hVH htV⟩).symm.trans ht2, hfix⟩
  constructor
  · obtain ⟨P, hP⟩ := suzukiSubgroup_root_intersection_isSylow hm H a c rfl
    exact ⟨P, by rwa [← hS] at hP⟩
  · have hPart : SuzukiPartitionMember m (S : Subgroup _) :=
      (suzukiPartitionMember_iff m _).mpr (Or.inl ⟨c, hS⟩)
    have hinter : (S : Subgroup _) ⊓ H ≠ ⊥ := by
      intro he
      exact ht (mem_bot.mp (he ▸ (show t ∈ (S : Subgroup _) ⊓ H from ⟨hVS htV, hVH htV⟩)))
    have hN := hPart.normalizer_le hm (A := (S : Subgroup _) ⊓ H) inf_le_left hinter
    rw [← inf_subgroupOf_right (S : Subgroup _) H,
      ← subgroupOf_normalizer_eq inf_le_right]
    apply le_antisymm
    · exact comap_mono hN
    · intro x hx
      exact inf_normalizer_le_normalizer_inf ⟨hx, H.le_normalizer x.property⟩

end BenderSuzuki.MatrixGroups
end
