module

public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification
public import Theory.Representation.OrthogonalFourMinusRankOne.NormalizerRank
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.ElementaryAbelian.Injective

/-!
# The inner near-offender bound for the orthogonal alternative

Every nontrivial elementary subgroup of the actual Hermitian SL₂ action
satisfies rank(A) + s ≤ codim C_V(A). Sylow transport preserves both sides.
Inside the canonical root group, the quadratic actors lie in a fixed-field
line and the other actors have fixed codimension 3s. Thus an inner actor
cannot be a near-offender when s > 1.

This is H.1.1(3), retaining arbitrary elementary inner actors and the actual
Hermitian representation. It makes no assertion that every near-offender
in the full normalizer is cyclic. Source: Aschbacher–Smith, printed p.378,
applied in the proof of 6.1.4, printed p.664.
-/

public noncomputable section

open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.FourOffender
open Representation Representation.BinaryOffender
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus.FiniteModel Matrix.SpecialLinearGroup

variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
local notation "H" => SL2.BinarySmall.hermitian s
local notation "SL" => Matrix.SpecialLinearGroup (Fin 2) (Field s)

theorem inner_rank_add_degree_le_fixedCodim
    (A : Subgroup SL) (hA : IsElementaryTwo A) :
    rank A + s ≤ fixedCodim H A := by
  obtain ⟨g, B, hBU, hB, rfl⟩ := elementary_root_transport s A hA
  rw [rank_map_conj, fixedCodim_map_conj]
  by_cases hq : IsQuadratic H B
  · obtain ⟨u, hu, hBl⟩ := (quadratic_iff_le_rootLine s B hBU hB.1).mp hq
    have hr : rank B ≤ s :=
      (inner_rank_mono s hBl).trans_eq (rootLine_calculation s hu).2.2.1
    rw [quadratic_fixedCodim s B hBU hB.1 hq]
    omega
  · have hr : rank B ≤ 2 * s := (inner_rank_mono s hBU).trans_eq (upper_rank s)
    rw [(nonquadratic_root_calculation s B hBU hB.1 hq).2.1]
    omega

theorem inner_not_near_offender (hs : 1 < s)
    (A : Subgroup SL) (hA : IsElementaryTwo A) :
    ¬ fixedCodim H A ≤ rank A + 1 := by
  have hb := inner_rank_add_degree_le_fixedCodim s A hA
  omega

/-- A near-offender in the whole binary normalizer cannot lie in the
literal image of the Hermitian component when its half-degree exceeds one. -/
theorem normalizer_near_offender_not_inner (hs : 1 < s)
    (A : Subgroup (linearNormalizer H)) (hA : IsElementaryTwo A)
    (hnear : fixedCodim (normalizerRepresentation H) A ≤ rank A + 1) :
    ¬ A ≤ (actionImage H).subgroupOf (linearNormalizer H) := by
  intro hi
  let f : SL →* linearNormalizer H := (SL2.BinarySmall.hermitian s).asGroupHom.codRestrict _
    (fun g => (actionImage H).le_normalizer ⟨g, rfl⟩)
  have hf : Function.Injective f := by
    intro x y he
    exact hermitian_injective s (congrArg (fun z : linearNormalizer H => z.val.val) he)
  let B := A.comap f
  have hmap : B.map f = A := by
    apply le_antisymm (map_comap_le _ _)
    intro a ha
    obtain ⟨g, hg⟩ := hi ha
    have he : f g = a := Subtype.ext hg
    exact ⟨g, by change f g ∈ A; rwa [he], he⟩
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo B := by
    refine ⟨?_, IsElementaryAbelian.comap_of_injective f hf A⟩
    intro hb
    apply hA.1
    rw [← hmap, hb, Subgroup.map_bot]
  have hr : rank B = rank A := by
    rw [← rank_map_injective f hf B, hmap]
  have hc : fixedCodim H B = fixedCodim (normalizerRepresentation H) A := by
    rw [← hmap]
    exact fixedCodim_map_equivariant H (normalizerRepresentation H) f
      (LinearEquiv.refl _ _) (fun _ _ => rfl) B
  exact inner_not_near_offender s hs B hB (by rwa [hc, hr])

end CFSG.Quasithin.Chapter6.Source.FourOffender
