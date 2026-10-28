module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.NormalTransport

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

/-!
# The actual quotient point parabolic

Correcting representatives by the actual O₂(H) identifies the image of an
involution-line normalizer with its point stabilizer in U/Z. An equivariant
comparison of the whole quotient with the natural module or its cover then
constructs the A₆ or S₆ point-parabolic model. In the cover, both duad orbits
are allowed and the zero and constant vectors are explicitly excluded.
No abstract actor isomorphism or dimension assertion substitutes for the
module comparison, and the full central kernel is retained.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, final
paragraph of 13.8.1, printed pp.968–969.
-/

public section
open Subgroup Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
variable {G : Type*} [Group G] {H U Z : Subgroup G} [(Z.subgroupOf U).Normal]

theorem symmetric_model_of_orbit
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* S6) (i : Duad → U ⧸ Z.subgroupOf U)
    (hi : Function.Injective i) (he : ∀ g d, i (e g • d) = a.action g (i d))
    (y : Duad) (hy : QuotientGroup.mk' (Z.subgroupOf U) u = i y) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* duadStabilizer) := by
  let : MulAction (Source.Hstar H) (U ⧸ Z.subgroupOf U) := MulAction.compHom _ a.action
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq S6 (0 : Duad) y
  have hs : Source.starImage H (normalizer (A : Set G)) =
      MulAction.stabilizer (Source.Hstar H) (i (h • (0 : Duad))) := by
    rw [normalizer_image_eq_stabilizer a A hA u hu hu1 hZ hcomm hm, hh]
    ext g
    change a.action g (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' (Z.subgroupOf U) u ↔ a.action g (i y) = i y
    rw [hy]
  exact ⟨(MulEquiv.subgroupCongr hs).trans (embeddedDuadPointModel e i hi he h)⟩

theorem alternating_model_of_orbit
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* A6) (i : Duad → U ⧸ Z.subgroupOf U)
    (hi : Function.Injective i) (he : ∀ g d, i (e g • d) = a.action g (i d))
    (y : Duad) (hy : QuotientGroup.mk' (Z.subgroupOf U) u = i y) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* a6DuadStabilizer) := by
  let : MulAction (Source.Hstar H) (U ⧸ Z.subgroupOf U) := MulAction.compHom _ a.action
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq A6 (0 : Duad) y
  have hs : Source.starImage H (normalizer (A : Set G)) =
      MulAction.stabilizer (Source.Hstar H) (i (h • (0 : Duad))) := by
    rw [normalizer_image_eq_stabilizer a A hA u hu hu1 hZ hcomm hm, hh]
    ext g
    change a.action g (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' (Z.subgroupOf U) u ↔ a.action g (i y) = i y
    rw [hy]
  exact ⟨(MulEquiv.subgroupCongr hs).trans (embeddedEvenDuadPointModel e i hi he h)⟩



open BinaryPermutation Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

/-- Transport a concrete point orbit through coordinates on the full quotient. -/
theorem symmetric_model_of_coordinates {W : Type*}
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* S6) (f : (U ⧸ Z.subgroupOf U) ≃ W)
    (i : Duad → W) (hi : Function.Injective i)
    (he : ∀ g d, f (a.action g (f.symm (i d))) = i (e g • d))
    (y : Duad) (hy : f (QuotientGroup.mk' (Z.subgroupOf U) u) = i y) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* duadStabilizer) := by
  refine symmetric_model_of_orbit a A hA u hu hu1 hZ hcomm hm e (fun d => f.symm (i d))
    (f.symm.injective.comp hi) ?_ y ?_
  · intro g d
    apply f.injective
    exact (f.apply_symm_apply _).trans (he g d).symm
  · apply f.injective
    exact hy.trans (f.apply_symm_apply _).symm

/-- Every nonzero natural point gives the actual point parabolic. -/
theorem symmetric_model_of_natural
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* S6)
    (f : (U ⧸ Z.subgroupOf U) ≃ natural (Fin 6))
    (he : ∀ g v, f (a.action g v) = naturalRepresentation (Fin 6) (e g) (f v))
    (hpoint : f (QuotientGroup.mk' (Z.subgroupOf U) u) ≠ 0) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* duadStabilizer) := by
  obtain ⟨y, hy⟩ := natural_cases _ hpoint
  apply symmetric_model_of_coordinates a A hA u hu hu1 hZ hcomm hm e f naturalDuad
    naturalDuad_injective _ y hy.symm
  intro g d
  rw [he, f.apply_symm_apply, naturalDuad_map]

/-- In the whole cover, every point outside its constant line gives the same
point-parabolic type. Both weight-two and weight-four orbits are retained. -/
theorem symmetric_model_of_cover
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* S6)
    (f : (U ⧸ Z.subgroupOf U) ≃ core (Fin 6))
    (he : ∀ g v, f (a.action g v) = coreRepresentation (Fin 6) (e g) (f v))
    (hzero : f (QuotientGroup.mk' (Z.subgroupOf U) u) ≠ 0)
    (hone : f (QuotientGroup.mk' (Z.subgroupOf U) u) ≠ coverOne) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* duadStabilizer) := by
  rcases cover_cases (f (QuotientGroup.mk' (Z.subgroupOf U) u)) with hz | ho | ⟨y, hy | hy⟩
  · exact (hzero hz).elim
  · exact (hone ho).elim
  · apply symmetric_model_of_coordinates a A hA u hu hu1 hZ hcomm hm e f coverDuad
      coverDuad_injective _ y hy
    intro g d
    rw [he, f.apply_symm_apply, coverDuad_map]
  · apply symmetric_model_of_coordinates a A hA u hu hu1 hZ hcomm hm e f complementaryDuad
      complementaryDuad_injective _ y hy
    intro g d
    rw [he, f.apply_symm_apply, complementaryDuad_map]

/-- Transport a concrete point orbit through coordinates on the full quotient. -/
theorem alternating_model_of_coordinates {W : Type*}
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* A6) (f : (U ⧸ Z.subgroupOf U) ≃ W)
    (i : Duad → W) (hi : Function.Injective i)
    (he : ∀ g d, f (a.action g (f.symm (i d))) = i (e g • d))
    (y : Duad) (hy : f (QuotientGroup.mk' (Z.subgroupOf U) u) = i y) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* a6DuadStabilizer) := by
  refine alternating_model_of_orbit a A hA u hu hu1 hZ hcomm hm e (fun d => f.symm (i d))
    (f.symm.injective.comp hi) ?_ y ?_
  · intro g d
    apply f.injective
    exact (f.apply_symm_apply _).trans (he g d).symm
  · apply f.injective
    exact hy.trans (f.apply_symm_apply _).symm

/-- Every nonzero natural point gives the actual point parabolic. -/
theorem alternating_model_of_natural
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* A6)
    (f : (U ⧸ Z.subgroupOf U) ≃ natural (Fin 6))
    (he : ∀ g v, f (a.action g v) = naturalRepresentation (Fin 6) (e g).val (f v))
    (hpoint : f (QuotientGroup.mk' (Z.subgroupOf U) u) ≠ 0) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* a6DuadStabilizer) := by
  obtain ⟨y, hy⟩ := natural_cases _ hpoint
  apply alternating_model_of_coordinates a A hA u hu hu1 hZ hcomm hm e f naturalDuad
    naturalDuad_injective _ y hy.symm
  intro g d
  rw [he, f.apply_symm_apply, naturalDuad_map]
  rfl

/-- In the whole cover, every point outside its constant line gives the same
point-parabolic type. Both weight-two and weight-four orbits are retained. -/
theorem alternating_model_of_cover
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* A6)
    (f : (U ⧸ Z.subgroupOf U) ≃ core (Fin 6))
    (he : ∀ g v, f (a.action g v) = coreRepresentation (Fin 6) (e g).val (f v))
    (hzero : f (QuotientGroup.mk' (Z.subgroupOf U) u) ≠ 0)
    (hone : f (QuotientGroup.mk' (Z.subgroupOf U) u) ≠ coverOne) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* a6DuadStabilizer) := by
  rcases cover_cases (f (QuotientGroup.mk' (Z.subgroupOf U) u)) with hz | ho | ⟨y, hy | hy⟩
  · exact (hzero hz).elim
  · exact (hone ho).elim
  · apply alternating_model_of_coordinates a A hA u hu hu1 hZ hcomm hm e f coverDuad
      coverDuad_injective _ y hy
    intro g d
    rw [he, f.apply_symm_apply, coverDuad_map]
    rfl
  · apply alternating_model_of_coordinates a A hA u hu hu1 hZ hcomm hm e f complementaryDuad
      complementaryDuad_injective _ y hy
    intro g d
    rw [he, f.apply_symm_apply, complementaryDuad_map]
    rfl

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
