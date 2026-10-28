module

public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ActionCatalogue
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers

/-!
# The partition normalizer of an A₄ three-prime residual in A₇

Let A₇ ≤ J ≤ S₇ and let Y ≤ A₇ be isomorphic to A₄. If Y is the
three-prime residual of B = N_J(Y), then its actual seven-point action is
conjugate to the paired model. Consequently N_S₇(Y) is the centralizer of a
triple transposition t, and B is the stabilizer in J of its three pairs and
singleton. We retain the literal action equation g(t(a)) = t(g(a)).

The action catalogue supplies three possible embeddings. Transporting the
relative normalizer and its residual along the same conjugation eliminates
the natural and diagonal embeddings: their residuals contain an additional
independent tail three-cycle. The paired normalizer calculation then supplies
t, transported back to the original coordinates. This argument does not need
the additional source hypothesis that B contains a Sylow two-subgroup of J.

Source: the A₇ paragraph of Aschbacher–Smith 15.3.43, printed p.1140, with
1.1.5(3)(d), printed pp.501–502 (combined manuscript, 1 March 2004). The actual
A₄ equivalence is supplied separately by `residual_mulEquiv_alternating_four`
from the normal moving four-group and two-core index. No classification
configuration or non-A₄ premise is used in these intrinsic calculations.
-/

public section

open Equiv Subgroup
namespace AlternatingSeven.ThreeResidualLocals

private theorem map_ambient_primePowerGenerated
    {G H : Type*} [Group G] [Group H] (p : ℕ) (K : Subgroup G) (e : G ≃* H) :
    ((primePowerGenerated p K).map K.subtype).map e.toMonoidHom =
      (primePowerGenerated p (K.map e.toMonoidHom)).map (K.map e.toMonoidHom).subtype := by
  rw [map_primePowerGenerated_subtype, map_primePowerGenerated_subtype,
    MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, n, hn⟩, rfl⟩
    exact ⟨mem_map.mpr ⟨x, hx, rfl⟩, n, by rw [← map_pow, hn, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, n, hn⟩
    refine ⟨x, ⟨hx, n, ?_⟩, rfl⟩
    apply e.injective
    simpa using hn

private theorem map_centralizer_singleton
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (t : G) :
    (centralizer ({t} : Set G)).map e.toMonoidHom =
      centralizer ({e t} : Set H) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa using congrArg e h
  · intro h
    apply e.injective
    simpa using h

/-- Only the paired action can equal the three-prime residual of its relative normalizer. -/
theorem residual_a4_conjugate_paired
    (J Y B : Subgroup Perm7) (hJ : alternatingGroup (Fin 7) ≤ J)
    (hY : Y ≤ alternatingGroup (Fin 7))
    (hB : B = J ⊓ normalizer (Y : Set Perm7))
    (hres : Y = (primePowerGenerated 3 B).map B.subtype)
    (e : Y ≃* alternatingGroup (Fin 4)) :
    ∃ g : Perm7, Y.map (MulAut.conj g).toMonoidHom = pairedFour := by
  obtain ⟨g, hg⟩ := a4_subgroup_conjugate_model Y hY e
  let c := MulAut.conj g
  let J' := J.map c.toMonoidHom
  have hJ' : alternatingGroup (Fin 7) ≤ J' := by
    have h := map_mono (f := c.toMonoidHom) hJ
    have hc : (alternatingGroup (Fin 7)).map c.toMonoidHom =
        alternatingGroup (Fin 7) := Normal.map_conj_eq _ g
    rwa [hc] at h
  have hB' : B.map c.toMonoidHom = J' ⊓ normalizer (Y.map c.toMonoidHom : Set Perm7) := by
    rw [hB, map_inf _ _ _ c.injective, map_equiv_normalizer_eq]
  have hres' : Y.map c.toMonoidHom =
      (primePowerGenerated 3 (J' ⊓ normalizer (Y.map c.toMonoidHom : Set Perm7) :
        Subgroup Perm7)).map (J' ⊓ normalizer (Y.map c.toMonoidHom : Set Perm7)).subtype := by
    calc
      _ = ((primePowerGenerated 3 B).map B.subtype).map c.toMonoidHom :=
        congrArg (fun K : Subgroup Perm7 => K.map c.toMonoidHom) hres
      _ = _ := by rw [map_ambient_primePowerGenerated, hB']
  rcases hg with hn | hd | hp
  · change Y.map c.toMonoidHom = naturalFour at hn
    rw [hn] at hres'
    exact False.elim (natural_threeResidual_ne J' hJ' hres'.symm)
  · change Y.map c.toMonoidHom = diagonalFour at hd
    rw [hd] at hres'
    exact False.elim (diagonal_threeResidual_ne J' hJ' hres'.symm)
  · exact ⟨g, hp⟩

/-- The normalizer of an A₄ residual preserves a partition into three pairs and a singleton. -/
theorem residual_a4_normalizer_eq_centralizer
    (J Y B : Subgroup Perm7) (hJ : alternatingGroup (Fin 7) ≤ J)
    (hY : Y ≤ alternatingGroup (Fin 7))
    (hB : B = J ⊓ normalizer (Y : Set Perm7))
    (hres : Y = (primePowerGenerated 3 B).map B.subtype)
    (e : Y ≃* alternatingGroup (Fin 4)) :
    ∃ t : Perm7, t.cycleType = {2, 2, 2} ∧
      normalizer (Y : Set Perm7) = centralizer ({t} : Set Perm7) := by
  obtain ⟨g, hg⟩ := residual_a4_conjugate_paired J Y B hJ hY hB hres e
  let c := MulAut.conj g
  refine ⟨c.symm pairing, ?_, ?_⟩
  · change (g⁻¹ * pairing * g).cycleType = {2, 2, 2}
    simpa only [inv_inv] using (Perm.cycleType_conj (σ := pairing) (τ := g⁻¹)).trans
      pairing_cycleType
  · apply map_injective (f := c.toMonoidHom) c.injective
    rw [map_equiv_normalizer_eq, hg, pairedFour_normalizer_eq,
      map_centralizer_singleton, c.apply_symm_apply]

/-- The requested relative normalizer is the centralizer of an actual triple transposition. -/
theorem residual_a4_relativeNormalizer_eq_centralizer
    (J Y B : Subgroup Perm7) (hJ : alternatingGroup (Fin 7) ≤ J)
    (hY : Y ≤ alternatingGroup (Fin 7))
    (hB : B = J ⊓ normalizer (Y : Set Perm7))
    (hres : Y = (primePowerGenerated 3 B).map B.subtype)
    (e : Y ≃* alternatingGroup (Fin 4)) :
    ∃ t : Perm7, t.cycleType = {2, 2, 2} ∧
      B = J ⊓ centralizer ({t} : Set Perm7) := by
  obtain ⟨t, ht, hN⟩ := residual_a4_normalizer_eq_centralizer J Y B hJ hY hB hres e
  exact ⟨t, ht, by rw [hB, hN]⟩

/-- The same witness identifies the block stabilizer and its actual action equation. -/
theorem residual_a4_partition_geometry
    (J Y B : Subgroup Perm7) (hJ : alternatingGroup (Fin 7) ≤ J)
    (hY : Y ≤ alternatingGroup (Fin 7))
    (hB : B = J ⊓ normalizer (Y : Set Perm7))
    (hres : Y = (primePowerGenerated 3 B).map B.subtype)
    (e : Y ≃* alternatingGroup (Fin 4)) :
    ∃ t : Perm7, t.cycleType = {2, 2, 2} ∧ t ^ 2 = 1 ∧
      t.partition.parts = {2, 2, 2, 1} ∧
      B = J ⊓ pairPartitionStabilizer t ∧
      (∀ a : Fin 7, MulAction.orbit (zpowers t) a = ({a, t a} : Set (Fin 7))) ∧
      (∀ g : Perm7, g ∈ B ↔ g ∈ J ∧ ∀ a, g (t a) = t (g a)) := by
  obtain ⟨t, ht, hC⟩ := residual_a4_relativeNormalizer_eq_centralizer J Y B hJ hY hB hres e
  have ht2 := sq_eq_one_of_cycleType_three_twos t ht
  have hP : B = J ⊓ pairPartitionStabilizer t := by
    rw [hC, centralizer_eq_pairPartitionStabilizer t ht2]
  refine ⟨t, ht, ht2, partition_parts_of_cycleType_three_twos t ht, hP,
    orbit_eq_pair_of_cycleType_three_twos t ht, ?_⟩
  intro g
  rw [hP, mem_inf, mem_pairPartitionStabilizer_iff t g ht2]

end AlternatingSeven.ThreeResidualLocals
