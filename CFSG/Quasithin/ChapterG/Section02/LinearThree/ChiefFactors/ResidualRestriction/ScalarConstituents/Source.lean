module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Radical
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Alignment
/-!
# Transport to the literal source residual and source layers

For n > 1 the aligned star map sends the original L₁ onto the full point
parabolic, and its GL₂ and scalar projections are surjective. The aligned
natural coordinates identify V₁ with the computed invariant line. The
previously supplied G.2.5(6–7) coordinates carry the natural and dual
flag actions copy by copy, including zero multiplicities. The scalar
characters on the natural line and dual quotient are nontrivial.

These are restriction calculations. The original MarkedLayers premises
remain explicit; this does not assert the printed chief-factor count or
resolve which layers survive intersection with L₁.

Source: Aschbacher–Smith, G.2.1 and G.2.5(6–8), printed pp.332,335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  {d : Hypothesis D F n g h} (a : PointAlignment d)

/-- The aligned star map on the literal embedded two-residual L₁. -/
def rawProjection : D.L₁ →* SL(3, F) :=
  a.projection.comp (inclusion (show D.L₁ ≤ D.L from (map_subtype_le _).trans inf_le_left))

theorem rawProjection_range (hn : 1 < n) : (rawProjection a).range = pointParabolicSL F := by
  rw [rawProjection, MonoidHom.range_comp, inclusion_range, a.residual_image,
    larger_twoResidual_eq_top F d.field_card hn, ← MonoidHom.range_eq_map, range_subtype]

/-- The genuine larger-field local projection, retaining the scalar quotient. -/
def localProjection (hn : 1 < n) : D.L₁ →* pointParabolicSL F :=
  (rawProjection a).codRestrict _ (fun x => rawProjection_range a hn ▸
    (show rawProjection a x ∈ (rawProjection a).range from ⟨x,rfl⟩))

theorem localProjection_surjective (hn : 1 < n) : Function.Surjective (localProjection a hn) := by
  intro y
  have hy : (y : SL(3,F)) ∈ (rawProjection a).range := (rawProjection_range a hn).symm ▸ y.property
  obtain ⟨x,hx⟩ := hy
  exact ⟨x,Subtype.ext hx⟩

theorem source_block_surjective (hn : 1 < n) :
    Function.Surjective ((block F).comp (localProjection a hn)) :=
  (block_surjective F).comp (localProjection_surjective a hn)

/-- The given natural coordinates after the same determinant-one basis change. -/
def alignedCoordinates : D.V ≃* Multiplicative (Fin 3 → F) :=
  d.coordinates.trans ((SpecialLinearGroup.toLin' a.basis⁻¹).toAddEquiv.toMultiplicative)

@[simp] theorem alignedCoordinates_apply (v : D.V) :
    (alignedCoordinates a v).toAdd = a.basis⁻¹.val *ᵥ (d.coordinates v).toAdd := rfl

theorem aligned_point (v : D.V) :
    (alignedCoordinates a v).toAdd ∈ naturalLine F ↔ (v : G) ∈ D.V₁ := by
  rw [d.point_mem]
  change a.basis⁻¹ • (d.coordinates v).toAdd ∈ naturalLine F ↔
    (d.coordinates v).toAdd ∈ (d.point : Set (Fin 3 → F))
  rw [a.point_eq]
  constructor
  · intro hv
    refine ⟨a.basis⁻¹ • (d.coordinates v).toAdd, (mem_naturalLine F _).mp hv, ?_⟩
    exact smul_inv_smul _ _
  · rintro ⟨w,hw,he⟩
    rw [← he, inv_smul_smul]
    exact (mem_naturalLine F _).mpr hw

theorem aligned_natural_action (hn : 1 < n) (l : D.L₁) (v : D.V) :
    (alignedCoordinates a ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq
        (((map_subtype_le _).trans inf_le_left) l.property)) v).mp v.property⟩).toAdd =
      (localProjection a hn l).val.val *ᵥ (alignedCoordinates a v).toAdd := by
  let l' : D.L := inclusion ((map_subtype_le _).trans inf_le_left) l
  have he := d.equivariant l' v
  change (d.coordinates _).toAdd = modelProjection d l' • (d.coordinates v).toAdd at he
  change a.basis⁻¹ • (d.coordinates _).toAdd =
    a.projection l' • (a.basis⁻¹ • (d.coordinates v).toAdd)
  exact (congrArg (fun w => a.basis⁻¹ • w) he).trans (a.projection_natural l' _).symm

theorem projection_dual (l : D.L) (v : Fin 3 → F) :
    (a.projection l)⁻¹.val.transpose *ᵥ (a.basis.val.transpose *ᵥ v) =
      a.basis.val.transpose *ᵥ ((modelProjection d l)⁻¹.val.transpose *ᵥ v) := by
  have he : a.basis * (a.projection l)⁻¹ = (modelProjection d l)⁻¹ * a.basis := by
    change a.basis * (a.basis⁻¹ * modelProjection d l * (a.basis⁻¹)⁻¹)⁻¹ = _
    group
  have hm := congrArg (fun x : SL(3,F) => x.val.transpose) he
  change (a.basis.val * (a.projection l)⁻¹.val).transpose =
    ((modelProjection d l)⁻¹.val * a.basis.val).transpose at hm
  rw [transpose_mul, transpose_mul] at hm
  simpa only [mulVec_mulVec] using congrArg (fun M => M *ᵥ v) hm


/-- Conjugation on any actual local element with a radical image uses the computed twist. -/
theorem source_radical_conjugation (hn : 1 < n) (l y : D.L₁) (w : Fin 2 → F)
    (hy : localProjection a hn y = radicalHom F (Multiplicative.ofAdd w)) :
    localProjection a hn (l * y * l⁻¹) =
      radicalHom F (Multiplicative.ofAdd ((scalar F (localProjection a hn l) : F) •
        ((block F (localProjection a hn l)⁻¹ : Matrix (Fin 2) (Fin 2) F).transpose *ᵥ w))) := by
  rw [map_mul, map_mul, map_inv, hy, radical_conjugation]

/-- Every odd scalar character occurs on the original local residual. -/
theorem source_scalar_surjective (hn : 1 < n) :
    Function.Surjective ((scalar F).comp (localProjection a hn)) := by
  intro z
  obtain ⟨l,hl⟩ := localProjection_surjective a hn (pointTorusHom F z)
  refine ⟨l, ?_⟩
  change scalar F (localProjection a hn l) = z
  rw [hl, scalar_torus]

/-- The scalar constituents on the natural line and dual quotient are both noncentral. -/
theorem source_scalar_characters_nontrivial (hn : 1 < n) :
    ∃ l : D.L₁, scalar F (localProjection a hn l) ≠ 1 ∧
      (scalar F (localProjection a hn l))⁻¹ ≠ 1 := by
  have hc : 4 ≤ Nat.card F := by
    rw [d.field_card]
    exact (show 4 = 2 ^ 2 by decide) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨z,hz⟩ := exists_ne (1 : Fˣ)
  obtain ⟨l,hl⟩ := source_scalar_surjective a hn z
  change scalar F (localProjection a hn l) = z at hl
  exact ⟨l, by simpa only [hl] using hz, by simpa only [hl, ne_eq, inv_eq_one] using hz⟩

section Layers
variable {hLI : D.L ≤ I D g h} {r s : ℕ}
  [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  (c : MarkedLayers d hLI r s)

def alignedUpper (q : UpperQuotient D g h) (i : Fin r) : Fin 3 → F :=
  a.basis⁻¹.val *ᵥ (c.upper q).toAdd i

def alignedLower (q : LowerQuotient D g h) (i : Fin s) : Fin 3 → F :=
  a.basis.val.transpose *ᵥ (c.lower q).toAdd i

/-- The earlier clause (7) coordinates carry precisely the computed natural action. -/
theorem upper_action (hn : 1 < n) (l : D.L₁) (v : S D g h) (i : Fin r) :
    alignedUpper a c (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (I_normalizes_core D g h
          (hLI (((map_subtype_le _).trans inf_le_left) l.property))) v).mp v.property⟩) i =
      (localProjection a hn l).val.val *ᵥ
        alignedUpper a c (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) v) i := by
  let l' : D.L := inclusion ((map_subtype_le _).trans inf_le_left) l
  have he := c.upper_equivariant l' v i
  exact (congrArg (fun w => a.basis⁻¹.val *ᵥ w) he).trans (a.projection_natural l' _).symm

/-- The earlier clause (6) coordinates carry the genuine contragredient action. -/
theorem lower_action (hn : 1 < n) (l : D.L₁) (v : S₃ D g h) (i : Fin s) :
    alignedLower a c (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (c.lower_normalizes
          (((map_subtype_le _).trans inf_le_left) l.property)) v).mp v.property⟩) i =
      (localProjection a hn l).val⁻¹.val.transpose *ᵥ
        alignedLower a c (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) v) i := by
  let l' : D.L := inclusion ((map_subtype_le _).trans inf_le_left) l
  have he := c.lower_equivariant l' v i
  rw [map_inv] at he
  exact (congrArg (fun w => a.basis.val.transpose *ᵥ w) he).trans (projection_dual a l' _).symm

/-- The natural quotient action in each of the r actual source copies. -/
theorem upper_quotient_action (hn : 1 < n) (l : D.L₁) (v : S D g h) (i : Fin r) :
    tail F (alignedUpper a c (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (I_normalizes_core D g h
          (hLI (((map_subtype_le _).trans inf_le_left) l.property))) v).mp v.property⟩) i) =
      (block F (localProjection a hn l) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        tail F (alignedUpper a c (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) v) i) := by
  rw [upper_action a c hn, natural_quotient_action]

/-- The scalar quotient in each of the s actual dual copies has character det. -/
theorem lower_quotient_action (hn : 1 < n) (l : D.L₁) (v : S₃ D g h) (i : Fin s) :
    head F (alignedLower a c (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (c.lower_normalizes
          (((map_subtype_le _).trans inf_le_left) l.property)) v).mp v.property⟩) i) =
      (↑(scalar F (localProjection a hn l))⁻¹ : F) *
        head F (alignedLower a c (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) v) i) := by
  rw [lower_action a c hn, dual_quotient_action]
end Layers
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
