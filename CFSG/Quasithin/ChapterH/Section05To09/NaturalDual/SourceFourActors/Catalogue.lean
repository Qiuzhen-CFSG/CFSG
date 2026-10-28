module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors.Marking
/-!
# The three source E₁₆ classes for the given Sylow

Pullback through the Sylow-compatible comparison supplies actual source
subgroups, conjugators and eight-point orbit partitions. Maximal elementary
order and uniqueness in the marked inner Sylow prove the literal source
Thompson equality, using the elementary convention of section 0.6.1.

Source: Aschbacher–Smith, H.9.3(3), printed pp.391–392.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 4 M V) (T : Sylow 2 M)
noncomputable def actor (i : Fin 3) : Subgroup M := pull S T (BinaryNaturalDual.FourActors.PermutationCatalogue.actor i)
noncomputable abbrev A0 := actor S T 0
noncomputable abbrev A1 := actor S T 1
noncomputable abbrev A2 := actor S T 2
noncomputable def B1 : Subgroup M := A1 S T ⊓ componentLayer M
noncomputable def B2 : Subgroup M := A2 S T ⊓ componentLayer M
noncomputable def r : M := (group S T).symm BinaryNaturalDual.FourActors.r

@[simp] theorem actor_map (i : Fin 3) :
    (actor S T i).map (group S T).toMonoidHom = BinaryNaturalDual.FourActors.PermutationCatalogue.actor i := pull_map S T _
@[simp] theorem B1_map : (B1 S T).map (group S T).toMonoidHom = BinaryNaturalDual.FourActors.B1 := by
  rw [B1, Subgroup.map_inf _ _ _ (group S T).injective, actor_map, layer_map]; rfl
@[simp] theorem B2_map : (B2 S T).map (group S T).toMonoidHom = BinaryNaturalDual.FourActors.B2 := by
  rw [B2, Subgroup.map_inf _ _ _ (group S T).injective, actor_map, layer_map]; rfl
@[simp] theorem r_map : group S T (r S T) = BinaryNaturalDual.FourActors.r := (group S T).apply_symm_apply _

theorem actor_elementary (i : Fin 3) : IsElementaryAbelian 2 (actor S T i) := by
  have h := (BinaryNaturalDual.FourActors.PermutationCatalogue.actor_elementary i).map (group S T).symm.toMonoidHom
  rw [Subgroup.map_equiv_eq_comap_symm' (group S T).symm] at h
  exact h

theorem actor_card (i : Fin 3) : Nat.card (actor S T i) = 16 := by
  rw [← Subgroup.card_map_of_injective (f := (group S T).toMonoidHom) (group S T).injective,
    actor_map, BinaryNaturalDual.FourActors.PermutationCatalogue.actor_card]

theorem map_conj (A : Subgroup M) (a : M) :
    (A.map (MulAut.conj a).toMonoidHom).map (group S T).toMonoidHom =
      (A.map (group S T).toMonoidHom).map (MulAut.conj (group S T a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext b
  simp

theorem actor_conjugate_iff (i j : Fin 3) :
    (∃ a : M, (actor S T i).map (MulAut.conj a).toMonoidHom = actor S T j) ↔ i = j := by
  constructor
  · rintro ⟨a,ha⟩
    apply (BinaryNaturalDual.FourActors.PermutationCatalogue.actor_conjugate_iff i j).mp
    refine ⟨group S T a, ?_⟩
    rw [← actor_map S T i, ← map_conj, ha, actor_map]
  · rintro rfl
    refine ⟨1, ?_⟩
    have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by ext x; simp
    rw [he, Subgroup.map_id]

theorem actor_exhaustion (E : Subgroup M) (hE : IsElementaryAbelian 2 E)
    (hcard : Nat.card E = 16) :
    ∃! i : Fin 3, ∃ a : M, E.map (MulAut.conj a).toMonoidHom = actor S T i := by
  let := hE.map (group S T).toMonoidHom
  have hc : Nat.card (E.map (group S T).toMonoidHom) = 16 :=
    (Subgroup.card_map_of_injective (group S T).injective).trans hcard
  obtain ⟨i,⟨a,ha⟩,hi⟩ := BinaryNaturalDual.FourActors.PermutationCatalogue.existsUnique_actor_conjugate (E.map (group S T).toMonoidHom) hc
  refine ⟨i, ⟨(group S T).symm a, ?_⟩, ?_⟩
  · apply Subgroup.map_injective (f := (group S T).toMonoidHom) (group S T).injective
    rw [map_conj, MulEquiv.apply_symm_apply, ha, actor_map]
  · rintro j ⟨b,hb⟩
    apply hi j
    refine ⟨group S T b, ?_⟩
    rw [← map_conj, hb, actor_map]

/-- Orbits in the actual eight-point action of the original group. -/
def orbit (A : Subgroup M) (x : Fin 8) : Set (Fin 8) :=
  {y | ∃ a ∈ A, permutation S T a x = y}

theorem actor_orbit (i : Fin 3) (x : Fin 8) :
    orbit S T (actor S T i) x = {y | BinaryNaturalDual.FourActors.PermutationCatalogue.blockLabel i y = BinaryNaturalDual.FourActors.PermutationCatalogue.blockLabel i x} := by
  rw [← BinaryNaturalDual.FourActors.PermutationCatalogue.actor_orbit i x]
  ext y
  rw [BinaryNaturalDual.FourActors.PermutationCatalogue.actorOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨a,ha,hy⟩
    exact ⟨⟨permutation S T a, ⟨group S T a,ha,rfl⟩⟩, hy⟩
  · rintro ⟨⟨_,a,ha,rfl⟩,hy⟩
    refine ⟨(group S T).symm a, ?_, ?_⟩
    · change group S T ((group S T).symm a) ∈ BinaryNaturalDual.FourActors.PermutationCatalogue.actor i
      simpa using ha
    · change BinaryNaturalDual.FourActors.permutationEquiv a x = y at hy
      change BinaryNaturalDual.FourActors.permutationEquiv (group S T ((group S T).symm a)) x = y
      rw [MulEquiv.apply_symm_apply]; exact hy

theorem A0_le_layer : A0 S T ≤ componentLayer M := by
  intro a ha
  exact (group_inner_iff S T a).mp (BinaryNaturalDual.FourActors.A0_le_inner ha)

theorem outer_actors : ¬ A1 S T ≤ componentLayer M ∧ ¬ A2 S T ≤ componentLayer M := by
  constructor
  · intro h
    have hm := Subgroup.map_mono (f := (group S T).toMonoidHom) h
    rw [actor_map, layer_map] at hm
    exact BinaryNaturalDual.FourActors.A1_not_le_inner hm
  · intro h
    have hm := Subgroup.map_mono (f := (group S T).toMonoidHom) h
    rw [actor_map, layer_map] at hm
    exact BinaryNaturalDual.FourActors.A2_not_le_inner hm

/-- The source elementary-maximal-order convention, on the GIVEN T₁. -/
theorem elementaryThompson_eq_A0 :
    Stellmacher.elementaryAbelianMaxJ (S.naturalSylowNormalizer T) = A0 S T := by
  let := S.finite_group
  have hle : A0 S T ≤ S.naturalSylowNormalizer T := by
    apply (Subgroup.map_le_map_iff_of_injective (f := (group S T).toMonoidHom) (group S T).injective).mp
    rw [actor_map, naturalSylow_map]
    exact BinaryNaturalDual.FourActors.PermutationCatalogue.A0_le_T0_inner
  have family : Stellmacher.elementaryAbelianMaxSubgroups (S.naturalSylowNormalizer T) =
      {A0 S T} := by
    ext E
    change (E ≤ S.naturalSylowNormalizer T ∧ IsElementaryAbelian 2 E ∧
      ∀ B : Subgroup M, B ≤ S.naturalSylowNormalizer T → IsElementaryAbelian 2 B →
        Nat.card B ≤ Nat.card E) ↔ E = A0 S T
    constructor
    · rintro ⟨hE,he,hm⟩
      let := he.map (group S T).toMonoidHom
      apply Subgroup.map_injective (f := (group S T).toMonoidHom) (group S T).injective
      rw [actor_map]
      apply BinaryNaturalDual.FourActors.PermutationCatalogue.T0_inner_elementary_eq_A0_of_card_ge
      · rw [← naturalSylow_map S T]
        exact Subgroup.map_mono hE
      · rw [Subgroup.card_map_of_injective (group S T).injective]
        simpa only [actor_card] using hm (A0 S T) hle (actor_elementary S T 0)
    · rintro rfl
      refine ⟨hle, actor_elementary S T 0, ?_⟩
      intro B hB he
      let := he.map (group S T).toMonoidHom
      rw [actor_card, ← Subgroup.card_map_of_injective (f := (group S T).toMonoidHom)
        (group S T).injective]
      apply BinaryNaturalDual.FourActors.PermutationCatalogue.T0_inner_elementary_card_le
      rw [← naturalSylow_map S T]
      exact Subgroup.map_mono hB
  rw [Stellmacher.elementaryAbelianMaxJ, family, sSup_singleton]
end CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
