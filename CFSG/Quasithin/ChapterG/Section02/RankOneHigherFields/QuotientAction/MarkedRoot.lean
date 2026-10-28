module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.Basic
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.ProjectiveDefs

/-!
# The original field line and the actual quotient root group

The G.2.2 commutator bound puts the displacement of U on V in V₁,
while U centralizes V₁. The original natural coordinates therefore place
the literal U* image in the transvection group of the original F-line.
This transvection group is a two-group, so the supplied Sylow hypothesis
makes the inclusion an equality. The original g moves that same line.

The final constructor specializes every marked linear hypothesis of
G.1.5(3) to this field line and root group, using the elementary quotient
and conjugation action constructed in `Basic`. The projective orbit map
itself is a subsequent geometric construction.

Source: Aschbacher–Smith G.2.3(6), printed p.334, and G.1.5(3), printed p.328.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
open Setup QuotientAction.Projective
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g : G} (d : Hypothesis D F n g)

namespace Hypothesis
include d

/-- The source field order gives its binary characteristic. -/
theorem field_char_two : CharP F 2 := by
  let := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using d.field_card)

/-- The source commutator and centralizer bounds identify the root line. -/
theorem quotientRoot_le_pointRoot (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L) :
    d.quotientRoot hUT hstar ≤ rootGroup F d.point := by
  have hUV : ⁅D.U, D.V⁆ ≤ D.V₁ :=
    (commutator_mono le_rfl (le_conjugateSpanBy D.V D.H)).trans
      (derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf)
  rintro a ⟨u, hu, rfl⟩
  constructor
  · intro z
    let v : D.V := d.coordinates.symm (Multiplicative.ofAdd z)
    let w : D.V := ⟨(u : G) * v * (u : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT u.property) v).mp v.property⟩
    have hc : ((w * v⁻¹ : D.V) : G) ∈ D.V₁ :=
      hUV (commutator_mem_commutator hu v.property)
    have hm := (d.point_mem (w * v⁻¹)).mp hc
    have he := d.IStarProjection_equivariant hUT hstar u v
    change (d.coordinates w).toAdd = _ at he
    change Matrix.mulVec (d.quotientActionProjection hUT hstar u).val z - z ∈ d.point
    convert hm using 1
    rw [map_mul, map_inv]
    change _ = (d.coordinates w).toAdd + -(d.coordinates v).toAdd
    rw [← sub_eq_add_neg]
    rw [he]
    simp only [v, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rfl
  · intro z hz
    let v : D.V := d.coordinates.symm (Multiplicative.ofAdd z)
    have hv : (v : G) ∈ D.V₁ := (d.point_mem v).mpr (by simpa [v] using hz)
    have hc := d.setup.toBaseHypothesis.U_le_centralizer_point hu v hv
    have hw : (⟨(u : G) * v * (u : G)⁻¹,
        (mem_normalizer_iff.mp (d.I_normalizes hUT u.property) v).mp v.property⟩ : D.V) = v := by
      apply Subtype.ext
      change (u : G) * v * (u : G)⁻¹ = v
      change (v : G) * u = (u : G) * v at hc
      rw [← hc, mul_inv_cancel_right]
    have he := d.IStarProjection_equivariant hUT hstar u v
    rw [hw] at he
    change Matrix.mulVec (d.quotientActionProjection hUT hstar u).val z = z
    simpa only [v, MulEquiv.apply_symm_apply, toAdd_ofAdd,
      d.quotientActionProjection_apply hUT hstar] using he.symm

omit d [Finite G] [Finite F] in
private theorem pointRoot_isPGroup [CharP F 2] (A : Submodule F (Fin 2 → F)) :
    IsPGroup 2 (rootGroup F A) := by
  intro a
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  let γ := Representation.specialLinearNatural (k := F) 2
  have h := a.property.2 (γ a (v) - v) (a.property.1 v)
  change γ a (γ a v - v) = γ a v - v at h
  rw [map_sub] at h
  have he : γ a (γ a v) = v := by
    calc
      _ = (γ a v - v) + γ a v := (sub_eq_iff_eq_add).mp h
      _ = v := by
        ext i
        change (γ a v i - v i) + γ a v i = v i
        rw [sub_eq_add_neg, add_right_comm, CharTwo.add_self_eq_zero, zero_add, CharTwo.neg_eq]
  change γ ((a : SL(2, F)) ^ 2) v = γ 1 v
  simpa only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply] using he

/-- Sylow maximality gives the exact root group, with the original point. -/
theorem quotientRoot_eq_pointRoot (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U) :
    d.quotientRoot hUT hstar = rootGroup F d.point := by
  let := d.field_char_two
  obtain ⟨R, hR⟩ := d.quotientRoot_sylow hUT hstar hSylow
  rw [← hR]
  exact (R.is_maximal' (pointRoot_isPGroup d.point)
    (hR ▸ d.quotientRoot_le_pointRoot hUT hf hstar)).symm

/-- The original conjugator moves the original field line. -/
theorem quotient_marked_point_ne (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) :
    d.point ≠ d.point.map (Representation.specialLinearNatural 2
      (d.quotientActionProjection hUT hstar
        (⟨g, d.g_mem_I_of_star hUT hstar.ge⟩ : D.I g)⁻¹)) := by
  intro he
  apply d.setup.point_ne_bot
  apply eq_bot_iff.mpr
  intro x hx
  let v : D.V := ⟨x, d.setup.point_le hx⟩
  let l : D.L := (⟨g, d.g_mem⟩ : D.L)⁻¹
  have hm := d.conjugate_point_mem l v
  simp only [l, Subgroup.coe_inv, inv_inv] at hm
  have hv := (d.point_mem v).mp hx
  rw [he] at hv
  have hxg : x ∈ conjugate D.V₁ g := by
    apply hm.mpr
    exact hv
  exact mem_bot.mpr (disjoint_def.mp d.point_disjoint hx hxg)

/-- Every G.1.5(3) hypothesis now refers to the original field line and
the actual transvection subgroup. The marked translate still uses g⁻¹. -/
theorem exists_quotient_root_configuration (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hB : D.star D.L₁ = D.star D.L ⊓ normalizer (D.star D.U : Set D.Star))
    (hsplit : D.S g = WProduct D g) :
    letI := d.quotientIntersection_normal hUT hf
    letI := d.quotient_elementary hUT hf hstar hsplit
    ∃ (σ : Representation (ZMod 2) SL(2, F)
        (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
      (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
        (σ.comp (d.quotientActionProjection hUT hstar))),
      (∀ s : D.S g, (c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((D.S₂ g).subgroupOf (D.S g)) s)) ∧
      IsCompl (c.imageSpace (D.W g)) (c.imageSpace (conjugate (D.W g) g)) ∧
      c.imageSpace (conjugate (D.W g) g) = (c.imageSpace (D.W g)).map
        (σ (d.quotientActionProjection hUT hstar
          (⟨g, d.g_mem_I_of_star hUT hstar.ge⟩ : D.I g)⁻¹)) ∧
      (∀ a ∈ rootGroup F d.point,
        LinearMap.range (σ a - 1) ≤ c.imageSpace (D.W g) ∧
        ∀ v ∈ c.imageSpace (D.W g), σ a v = v) ∧
      ∀ a ∈ normalizer (rootGroup F d.point : Set SL(2, F)),
        (c.imageSpace (D.W g)).map (σ a) = c.imageSpace (D.W g) := by
  have he := d.quotientRoot_eq_pointRoot hUT hf hstar hSylow
  simpa only [he] using d.exists_quotient_action hUT hf hstar hB hsplit

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
