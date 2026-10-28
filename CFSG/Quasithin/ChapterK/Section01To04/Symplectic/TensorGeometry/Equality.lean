module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Descent
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Equality.PlaneRoots
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Equality.ActorRank
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Equality.PointRoots.SubgroupBound
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Equality actors for the descended symplectic tensor

Root intersections compute the fixed space of a plane-radical subgroup of
rank greater than 4s. Its binary fixed dimension is 4s, so ratio at most two
forces the entire rank-6s radical. The common-root and native involution
arguments supply the strict actor rank bound. The corrected point fixed-space
bound excludes the point radical without claiming equality with its fixed line.

Every small-ratio actor in the literally marked Sylow is therefore the
transported plane radical. Conjugate placement proves the global lower bound
of two for every elementary actor and hence for the cubic ratio. The earlier
outer-placement and Sylow-fixer premises remain explicit here and are
discharged in `Equality.Source` using the genuine source hypotheses.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

public section
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair

namespace CFSG.Quasithin.ChapterK.Symplectic
variable {D V F : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) [ρ.IsIrreducible] [Field F]
  [Algebra (SchurField ρ) F]

/-- Descent for a subgroup of the plane radical meeting the root directions.
This computes the fixed space of that subgroup, not only that of the full radical. -/
theorem TensorIdentification.plane_subgroup_fixed_finrank {s : ℕ}
    (h : TensorIdentification ρ F s) {A : Subgroup (Sp F)}
    (hA : A ≤ planeRadical) (hr : 4 * s < rank A) :
    Module.finrank (ZMod 2) (fixedSpace ρ (A.map h.groupEquiv.symm.toMonoidHom)) =
      4 * s := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hne : h.sigma.toRingEquiv ≠ RingEquiv.refl F := by
    intro he
    apply h.sigma_ne
    ext t
    exact DFunLike.congr_fun he t
  rw [h.fixed_finrank ρ, TensorGeometry.Equality.plane_subgroup_tensor_fixed_finrank
    h.field_card h.sigma.toRingEquiv hne hA (by omega)]
  omega

/-- The plane branch of the equality argument: the root calculation forces
codimension 12s, so the small-ratio hypothesis forces the entire rank-6s radical. -/
theorem TensorIdentification.plane_subgroup_eq_of_small {s : ℕ}
    (h : TensorIdentification ρ F s) {A : Subgroup (Sp F)}
    (hA : A ≤ planeRadical) (hr : 4 * s < rank A)
    (he : IsElementaryTwo A)
    (hsmall : fixedCodim ρ (A.map h.groupEquiv.symm.toMonoidHom) ≤ 2 * rank A) :
    A = planeRadical := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfix := h.plane_subgroup_fixed_finrank ρ hA hr
  have hdim := fixedCodim_add_finrank ρ (A.map h.groupEquiv.symm.toMonoidHom)
  rw [hfix, h.binary_finrank] at hdim
  apply Subgroup.eq_of_le_of_card_ge hA
  rw [card_planeRadical, h.field_card, ← pow_mul, he.card_eq_two_pow_rank]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  omega

end CFSG.Quasithin.ChapterK.Symplectic


namespace CFSG.Quasithin.ChapterK.Symplectic
open Representation Representation.BinaryOffender
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- Literal subgroup transport for the plane branch of K.3.4.2. The strict
rank and plane-placement hypotheses are discharged in the equality endpoint. -/
theorem tensor_plane_actor_eq_of_small {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ L)
    (hplane : (A.subgroupOf L).map h.groupEquiv.toMonoidHom ≤ planeRadical)
    (hr : 4 * s < rank A) (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    A = planeRadical.map (L.subtype.comp h.groupEquiv.symm.toMonoidHom) := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let B := (A.subgroupOf L).map h.groupEquiv.toMonoidHom
  have hback : B.map h.groupEquiv.symm.toMonoidHom = A.subgroupOf L := by
    simp [B, Subgroup.map_map]
  have hBr : rank B = rank A := by
    dsimp [B]
    rw [rank_map_injective _ h.groupEquiv.injective, rank_subgroupOf hAL]
  have hBe : IsElementaryTwo B := by
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hz
    have hzero : A.subgroupOf L = ⊥ := by
      rw [← hback, hz, Subgroup.map_bot]
    apply hA.1
    rw [← Subgroup.map_subgroupOf_eq_of_le hAL, hzero, Subgroup.map_bot]
  have hcod : fixedCodim (ρ.comp L.subtype) (B.map h.groupEquiv.symm.toMonoidHom) =
      fixedCodim ρ A := by
    rw [hback, fixedCodim_subgroupOf ρ hAL]
  have he := h.plane_subgroup_eq_of_small (ρ.comp L.subtype) hplane
    (by rwa [hBr]) hBe (by rwa [hcod, hBr])
  rw [← Subgroup.map_map, ← he, hback, Subgroup.map_subgroupOf_eq_of_le hAL]

omit [Finite G] in
/-- The marked Sylow places the original actor in one of the two actual radicals.
Only the elementary subgroup geometry is reused from the natural-plus-graph
development; this statement makes no assertion about tensor fixed spaces. -/
theorem tensor_marked_actor_placement {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s) (T : Sylow 2 G)
    (hT : ((T : Subgroup G).subgroupOf L).map h.groupEquiv.toMonoidHom = unipotent)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ L) (hAT : A ≤ T) :
    (A.subgroupOf L).map h.groupEquiv.toMonoidHom ≤ SymplecticConjugatePair.pointRadical ∨
      (A.subgroupOf L).map h.groupEquiv.toMonoidHom ≤ planeRadical := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 :=
    charP_of_injective_algebraMap (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let B := (A.subgroupOf L).map h.groupEquiv.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hB : B ≤ unipotent := by
    rw [← hT]
    exact Subgroup.map_mono (fun g hg => hAT hg)
  let : IsElementaryAbelian 2 (B.subgroupOf unipotent) :=
    IsElementaryAbelian.subgroupOf hB
  rcases elementary_le_wing (B.subgroupOf unipotent) with hp | hl
  · left
    rw [pointRadical_eq_wing]
    change B ≤ _
    rw [← Subgroup.map_subgroupOf_eq_of_le hB]
    exact Subgroup.map_mono hp
  · right
    rw [planeRadical_eq_wing]
    change B ≤ _
    rw [← Subgroup.map_subgroupOf_eq_of_le hB]
    exact Subgroup.map_mono hl

end CFSG.Quasithin.ChapterK.Symplectic

namespace CFSG.Quasithin.ChapterK.Symplectic
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- Unmarked actors are conjugate into an actual radical. The point bound
excludes that branch, while the plane calculation forces rank 6s and
codimension 12s. All transport uses the original binary representation. -/
theorem tensor_large_actor_numerics {s : ℕ} (hs : 0 < s)
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ L)
    (hr : 4 * s < rank A) (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    rank A = 6 * s ∧ fixedCodim ρ A = 12 * s := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 :=
    charP_of_injective_algebraMap (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let B := (A.subgroupOf L).map h.groupEquiv.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hback : B.map h.groupEquiv.symm.toMonoidHom = A.subgroupOf L := by
    simp [B, Subgroup.map_map]
  have hBr : rank B = rank A := by
    dsimp [B]
    rw [rank_map_injective _ h.groupEquiv.injective, rank_subgroupOf hAL]
  have hBe : IsElementaryTwo B := by
    refine ⟨?_, inferInstance⟩
    intro hz
    have hzero : A.subgroupOf L = ⊥ := by
      rw [← hback, hz, Subgroup.map_bot]
    apply hA.1
    rw [← Subgroup.map_subgroupOf_eq_of_le hAL, hzero, Subgroup.map_bot]
  let τ := (ρ.comp L.subtype).comp h.groupEquiv.symm.toMonoidHom
  have hc (C : Subgroup (Sp F)) :
      fixedCodim (ρ.comp L.subtype) (C.map h.groupEquiv.symm.toMonoidHom) =
        fixedCodim τ C := by
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (ρ.comp L.subtype)
      (C.map h.groupEquiv.symm.toMonoidHom)) =
        Module.finrank (ZMod 2) (_ ⧸ fixedSpace
          ((ρ.comp L.subtype).comp h.groupEquiv.symm.toMonoidHom) C)
    exact congrArg (fun U : Submodule (ZMod 2) V =>
      Module.finrank (ZMod 2) (V ⧸ U))
      (Representation.BinaryOffender.fixedSpace_comp_map (ρ.comp L.subtype)
        h.groupEquiv.symm.toMonoidHom C).symm
  have hcB : fixedCodim τ B = fixedCodim ρ A := by
    rw [← hc, hback, fixedCodim_subgroupOf ρ hAL]
  obtain ⟨g, hpoint | hplane⟩ := elementary_conjugate_radical h.field_card (by omega) B
  · have hC := h.point_subgroup_not_small (ρ.comp L.subtype) hs hpoint
      (by rwa [rank_map_conj, hBr])
    rw [hc, fixedCodim_map_conj, hcB, rank_map_conj, hBr] at hC
    omega
  · have he := h.plane_subgroup_eq_of_small (ρ.comp L.subtype) hplane
      (by rwa [rank_map_conj, hBr]) (hBe.map_conj g) (by
        rwa [hc, fixedCodim_map_conj, hcB, rank_map_conj, hBr])
    have hCr : rank (B.map (MulAut.conj g).toMonoidHom) = 6 * s := by
      rw [he, rank_planeRadical h.field_card]
      omega
    have hCf := h.plane_subgroup_fixed_finrank (ρ.comp L.subtype) hplane
      (by rwa [rank_map_conj, hBr])
    have hCd := fixedCodim_add_finrank (ρ.comp L.subtype)
      ((B.map (MulAut.conj g).toMonoidHom).map h.groupEquiv.symm.toMonoidHom)
    rw [hCf, h.binary_finrank, hc, fixedCodim_map_conj, hcB] at hCd
    rw [rank_map_conj, hBr] at hCr
    exact ⟨hCr, by omega⟩
end CFSG.Quasithin.ChapterK.Symplectic

namespace CFSG.Quasithin.ChapterK.Symplectic
open scoped ENNReal
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]
  {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
  (hplace : ∀ A, IsElementaryTwo A → fixedCodim ρ A ≤ 2 * rank A → A ≤ L)
  (hfix : ∀ (T : Sylow 2 G) (j : G) (hjL : j ∈ L), j ∈ T → orderOf j = 2 →
    ¬ IsB1 (h.groupEquiv ⟨j, hjL⟩) →
    rank (subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T) ≤ s)

include hs hplace hfix

/-- Every small-ratio elementary actor in the literally marked Sylow is the
transported plane radical. The common-root and fixer argument supplies the
strict rank bound, and the corrected point bound excludes the other radical. -/
theorem tensor_marked_actor_eq_of_small (T : Sylow 2 G)
    (hT : ((T : Subgroup G).subgroupOf L).map h.groupEquiv.toMonoidHom = unipotent)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAT : A ≤ T)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    A = planeRadical.map (L.subtype.comp h.groupEquiv.symm.toMonoidHom) := by
  have hAL := hplace A hA hsmall
  have hr := tensor_actor_rank_gt_four_mul ρ L hs h hfix hA hAL hsmall
  rcases tensor_marked_actor_placement ρ L h T hT hA hAL hAT with hp | hl
  · exact (tensor_point_actor_exclusion ρ L h hs hAL hr hsmall hp).elim
  · exact tensor_plane_actor_eq_of_small ρ L h hA hAL hl hr hsmall

/-- Ratio formulation of the exact marked-Sylow equality statement. -/
theorem tensor_marked_actor_eq_of_ratio_le_two (T : Sylow 2 G)
    (hT : ((T : Subgroup G).subgroupOf L).map h.groupEquiv.toMonoidHom = unipotent)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAT : A ≤ T)
    (hsmall : actionRatio ρ A ≤ 2) :
    A = planeRadical.map (L.subtype.comp h.groupEquiv.symm.toMonoidHom) := by
  exact tensor_marked_actor_eq_of_small ρ L hs h hplace hfix T hT hA hAT
    ((actionRatio_le_nat_iff ρ hA 2).mp hsmall)

/-- The lower ratio bound holds for every elementary actor. Conjugate
placement, rather than a marking assumption on the actor, supplies the
radical geometry used here. -/
theorem tensor_actionRatio_ge_two {A : Subgroup G} (hA : IsElementaryTwo A) :
    2 ≤ actionRatio ρ A := by
  have hc : 2 * rank A ≤ fixedCodim ρ A := by
    by_cases hsmall : fixedCodim ρ A ≤ 2 * rank A
    · have hAL := hplace A hA hsmall
      have hr := tensor_actor_rank_gt_four_mul ρ L hs h hfix hA hAL hsmall
      obtain ⟨hrank, hcod⟩ := tensor_large_actor_numerics ρ L hs h hA hAL hr hsmall
      omega
    · omega
  have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast hA.rank_pos.ne'
  rw [actionRatio, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (by simp))]
  exact_mod_cast hc

/-- K.3.4.2's lower cubic-ratio bound; the explicit earlier-source premises
are outer-actor placement and the non-b₁ fixed-space fixer bound. -/
theorem tensor_cubicRatio_ge_two : 2 ≤ cubicRatio ρ := by
  exact le_iInf fun A => le_iInf fun hA =>
    tensor_actionRatio_ge_two ρ L hs h hplace hfix hA.1

end CFSG.Quasithin.ChapterK.Symplectic
