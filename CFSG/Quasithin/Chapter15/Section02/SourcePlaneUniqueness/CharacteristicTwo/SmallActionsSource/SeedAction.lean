module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.CubicSeeds
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.Reduction
public import Theory.SpecificGroups.SymmetricThree.CubicSelection

/-!
# The actual action image of an arbitrary corrected seed

Every outside seed has the cubic two-residual of the literal NI as its
image on V. That image is nonnormal in the whole M-action by the preceding
normalizer obstruction. A Sylow three-subgroup of the seed has order three
and maps onto this same residual, providing an actual cubic subgroup for
the cyclic-star rank argument. No equality of the seed itself with a
canonical residual is used.

The S₃ identification of the actual NI image is the earlier 15.2.18(3)
input, owned by qt-e-152-component-omega-connector. Final discharge remains
with qt-e-152-plane-uniqueness.
Source: Aschbacher--Smith 15.2.21(3), printed p.1114, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open PlaneUniquenessPreceding.OmegaAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I Y : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

omit d in
/-- Every Sylow three-subgroup of a corrected seed has order three. -/
theorem Seed.sylow_three_card (s : Seed M I (smallActionS T ZS) Y)
    (P : Sylow 3 Y) : Nat.card P = 3 := by
  have hc := s.core_quotient_card (T.isPGroup'.to_le inf_le_left)
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  have hY : Nat.card Y = 3 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 Y),hc,hn]
  rw [P.card_eq_multiplicity,hY,
    Nat.factorization_mul (by decide) (pow_ne_zero _ (by decide)), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]

/-- The image of every outside seed is the actual cubic residual of NI. -/
theorem Seed.action_image_eq_residual
    (hI : PlaneEscapes Mc ZS I) (s : Seed M I (smallActionS T ZS) Y)
    (hout : ¬ Y ≤ Mc ⊓ I)
    (e : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    (Y.subgroupOf M).map (action hsource) = residualImage hsource I := by
  let A := intersectionImage hsource I
  let R := residualImage hsource I
  let B := (Y.subgroupOf M).map (action hsource)
  have hBR : B ≤ R := by
    have h := map_mono (f := action hsource)
      (comap_mono (f := M.subtype) (embedded_pResidual_mono 2 s.le_NI))
    rw [(pResidual_eq_top_iff 2 Y).mpr s.perfect,
      ←MonoidHom.range_eq_map,range_subtype] at h
    change B ≤ residualImage hsource I
    rw [residualImage_eq]
    exact h
  have hRc : Nat.card R = 3 := by
    have he := congrArg (fun K : Subgroup (Equiv.Perm (Fin 3)) => Nat.card K)
      (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective)
    rw [card_map_of_injective e.injective,
      Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card] at he
    exact (card_map_of_injective A.subtype_injective).trans he
  have hBne : B ≠ ⊥ := by
    intro hb
    apply hout
    refine le_inf ?_ (s.le_NI.trans inf_le_right)
    intro y hy
    have hm := mem_map_of_mem (action hsource)
      (show (⟨y,s.le_NI.trans inf_le_left hy⟩ : M) ∈ Y.subgroupOf M from hy)
    have hk : (⟨y,s.le_NI.trans inf_le_left hy⟩ : M) ∈ (action hsource).ker := by
      change (action hsource) _ ∈ B at hm
      rw [hb] at hm
      exact hm
    rw [action_ker] at hk
    exact ((centralizer_le d.geometry.plane_le).trans
      ((d.centralizer_le_intersection hI).trans inf_le_left)) hk
  have hd : Nat.card B ∣ 3 := hRc ▸ card_dvd_of_le hBR
  have hBc : Nat.card B = 3 := ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
    (fun hh => hBne (card_eq_one.mp hh))
  exact eq_of_le_of_card_ge hBR (by rw [hBc,hRc])

/-- In particular, the image of an arbitrary outside seed is not normal in M's action. -/
theorem Seed.action_image_not_normal
    (hI : PlaneEscapes Mc ZS I) (s : Seed M I (smallActionS T ZS) Y)
    (hout : ¬ Y ≤ Mc ⊓ I)
    (e : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    ¬ ((Y.subgroupOf M).map (action hsource)).Normal := by
  rw [s.action_image_eq_residual d hI hout e]
  exact residualImage_not_normal d hI (fun h => hout (s.le_NI.trans h))
omit d in
private theorem sylow_map_eq_range_of_cubic {D : Type*} [Group D]
    (f : Y →* D) (hc : Nat.card f.range = 3) (P : Sylow 3 Y) :
    (P : Subgroup Y).map f = f.range := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let Q := P.mapSurjective f.rangeRestrict_surjective
  have hQ : Nat.card Q = 3 := by
    rw [Q.card_eq_multiplicity,hc]
    norm_num [Nat.prime_three.factorization]
  have htop : (Q : Subgroup f.range) = ⊤ :=
    eq_of_le_of_card_ge le_top (by rw [card_top,hc,hQ])
  have hh := congrArg (map f.range.subtype) htop
  rw [←MonoidHom.range_eq_map,range_subtype] at hh
  change ((P : Subgroup Y).map f.rangeRestrict).map f.range.subtype = f.range at hh
  rw [map_map] at hh
  exact hh

/-- A Sylow cubic in the original seed has precisely the nonnormal NI residual image. -/
theorem Seed.exists_cubic_action_lift
    (hI : PlaneEscapes Mc ZS I) (s : Seed M I (smallActionS T ZS) Y)
    (hout : ¬ Y ≤ Mc ⊓ I)
    (e : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    ∃ B : Subgroup M, B ≤ Y.subgroupOf M ∧ Nat.card B = 3 ∧
      B.map (action hsource) = residualImage hsource I := by
  let j : Y →* M := inclusion (s.le_NI.trans inf_le_left)
  let f := (action hsource).comp j
  let P : Sylow 3 Y := Sylow.nonempty.some
  have hj : j.range = Y.subgroupOf M := by
    ext x
    exact ⟨fun ⟨y,hy⟩ => hy ▸ y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  have hf : f.range = residualImage hsource I := by
    rw [MonoidHom.range_comp,hj,s.action_image_eq_residual d hI hout e]
  have hc : Nat.card f.range = 3 := by
    rw [hf,card_map_of_injective (intersectionImage hsource I).subtype_injective]
    have he := congrArg (fun K : Subgroup (Equiv.Perm (Fin 3)) => Nat.card K)
      (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective)
    rwa [card_map_of_injective e.injective,
      Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card] at he
  refine ⟨(P : Subgroup Y).map j,?_,?_,?_⟩
  · exact (map_le_range j _).trans_eq hj
  · rw [card_map_of_injective (inclusion_injective _),s.sylow_three_card P]
  · rw [map_map,sylow_map_eq_range_of_cubic f hc P,hf]
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
