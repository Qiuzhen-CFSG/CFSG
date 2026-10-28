module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Shears
public import Theory.Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces.RootPlanes
public import Theory.Representation.SL3DoubledNaturalOffenders.Displacement
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF

/-!
# Recognizing the doubled plane radical from its two coranks

Elementary subgroups of SL₃ lie in a root plane. Rank at least 2n makes
that plane full, and fixed codimension at most 2n excludes the point radical:
its fixed codimension on two identical natural copies is at least 4n.
A simultaneous basis change on both copies then constructs the actual shear
coordinates. The ambient transport identifies both numerical inputs with
the original centralizer indices, retaining every central actor.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773. These calculations
are used by the reciprocal source action, without assuming its shear output.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Matrix.PSL3.RootPlaneGeometry Matrix.PSL3Even.UnipotentGeometry
open Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace PlaneRecognition
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable [Algebra (ZMod 2) F]
abbrev ρ := SL3DoubledNaturalOffenders.representation F

omit [Finite F] [CharP F 2] in
private theorem point_fixed (v : fixedSpace (ρ (F := F)) (rootPlaneSL F true))
    (i : Fin 2) : v.val i 1 = 0 ∧ v.val i 2 = 0 := by
  have h₁ := congrArg (fun w : Shears.Space F => w i 0)
    (v.property ⟨specialLinear F ⟨1,0,0⟩, (mem_rootPlaneSL_point F _).mpr ⟨1,0,rfl⟩⟩)
  have h₂ := congrArg (fun w : Shears.Space F => w i 0)
    (v.property ⟨specialLinear F ⟨0,0,1⟩, (mem_rootPlaneSL_point F _).mpr ⟨0,1,rfl⟩⟩)
  change (matrix F ⟨1,0,0⟩).mulVec (v.val i) 0 = v.val i 0 at h₁
  change (matrix F ⟨0,0,1⟩).mulVec (v.val i) 0 = v.val i 0 at h₂
  simpa [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using And.intro h₁ h₂

omit [CharP F 2] in
theorem point_fixedCodim_lower {n : ℕ} (hF : Nat.card F = 2^n) :
    4*n ≤ fixedCodim (ρ (F := F)) (rootPlaneSL F true) := by
  let f : fixedSpace (ρ (F := F)) (rootPlaneSL F true) →ₗ[ZMod 2] (Fin 2 → F) :=
    { toFun v i := v.val i 0
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    ext i j
    fin_cases j
    · exact congrFun he i
    · exact (point_fixed v i).1.trans (point_fixed w i).1.symm
    · exact (point_fixed v i).2.trans (point_fixed w i).2.symm
  have hb := LinearMap.finrank_le_finrank_of_injective hf
  have hd := fixedCodim_add_finrank (ρ (F := F)) (rootPlaneSL F true)
  rw [SL3DoubledNaturalOffenders.finrank_space hF] at hd
  have he : Module.finrank (ZMod 2) (Fin 2 → F) = 2*n := by
    simp [Module.finrank_pi_fintype, NaturalTensor.finrank_field F hF]
  rw [he] at hb
  omega

theorem conjugate_eq_plane {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (A : Subgroup SL(3,F)) (hA : IsElementaryTwo A)
    (hr : 2*n ≤ rank A) (hc : fixedCodim (ρ (F := F)) A ≤ 2*n) :
    ∃ g : SL(3,F), A.map (MulAut.conj g).toMonoidHom = rootPlaneSL F false := by
  obtain ⟨g,b,hb⟩ := elementary_conjugate_le_rootPlane hn hF A hA
  have hrank : rank (A.map (MulAut.conj g).toMonoidHom) = 2*n :=
    le_antisymm (rank_le_of_le_rootPlane hF _ b hb) (by rwa [rank_map_conj])
  have he := eq_rootPlane_of_rank_eq hF _ (hA.map_conj g) b hb
    hrank
  cases b
  · exact ⟨g,he⟩
  · have hh := point_fixedCodim_lower hF
    rw [← he,fixedCodim_map_conj] at hh
    omega

omit [Finite F] [CharP F 2] in
private theorem line_action (p q : F) (v : Shears.Space F) :
    ρ (specialLinear F ⟨0,q,p⟩) v = Shears.shear p q v := by
  change (fun i => (matrix F ⟨0,q,p⟩).mulVec (v i)) = _
  ext i j
  fin_cases j <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Shears.shear]

variable {G : Type*} [Group G] {A B : Subgroup G}

/-- A faithful doubled marking for a subgroup of the actual natural SL₃ action.
The actor homomorphism may have the original centralizer as kernel. -/
structure NaturalAction (A B : Subgroup G) (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F] where
  normalized : A ≤ normalizer (B : Set G)
  coordinates : B ≃* Multiplicative (Shears.Space F)
  actor : A →* SL(3,F)
  equivariant : ∀ a : A, ∀ v : B,
    (coordinates (B.normalizerMonoidHom (inclusion normalized a) v)).toAdd =
      ρ (actor a) (coordinates v).toAdd

namespace NaturalAction
variable (d : NaturalAction A B F)

omit [Finite F] in
/-- A basis change in SL₃ acts identically on both copies. -/
def rebase (g : SL(3,F)) : NaturalAction A B F where
  normalized := d.normalized
  coordinates := d.coordinates.trans
    (LinearEquiv.ofBijective (ρ g) ((ρ (F := F)).apply_bijective g)).toAddEquiv.toMultiplicative
  actor := (MulAut.conj g).toMonoidHom.comp d.actor
  equivariant := by
    intro a v
    change ρ g (d.coordinates (B.normalizerMonoidHom (inclusion d.normalized a) v)).toAdd =
      ρ (g * d.actor a * g⁻¹) (ρ g (d.coordinates v).toAdd)
    rw [d.equivariant,map_mul,map_mul]
    simp only [Module.End.mul_apply]
    have hi (w : Shears.Space F) : ρ g⁻¹ (ρ g w) = w := by
      rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    rw [hi]

/-- The rank and fixed-codimension equations select the plane radical, and
surjectivity onto that radical constructs both shear coefficients. -/
theorem shearCoordinates {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hA : IsElementaryTwo d.actor.range)
    (hr : 2*n ≤ rank d.actor.range)
    (hc : fixedCodim (ρ (F := F)) d.actor.range ≤ 2*n) :
    Nonempty (ShearCoordinates A B F) := by
  obtain ⟨g,hg⟩ := conjugate_eq_plane hn hF d.actor.range hA hr hc
  let e := d.rebase g
  have he : e.actor.range = rootPlaneSL F false := by
    change ((MulAut.conj g).toMonoidHom.comp d.actor).range = _
    rw [MonoidHom.range_comp,hg]
  refine ⟨⟨e.normalized,e.coordinates,?_,?_⟩⟩
  · intro a
    obtain ⟨q,p,hp⟩ := (mem_rootPlaneSL_line F _).mp
      (he ▸ (show e.actor a ∈ e.actor.range from ⟨a,rfl⟩))
    refine ⟨p,q,fun v => ?_⟩
    rw [e.equivariant,← hp,line_action]
  · intro p q
    have hm : specialLinear F ⟨0,q,p⟩ ∈ e.actor.range := by
      rw [he]
      exact (mem_rootPlaneSL_line F _).mpr ⟨q,p,rfl⟩
    obtain ⟨a,ha⟩ := hm
    exact ⟨a,fun v => by rw [e.equivariant,ha,line_action]⟩

omit [Finite F] in
/-- Faithfulness identifies the original actor kernel, including central actors. -/
theorem actor_eq_one (a : A) : d.actor a = 1 ↔ (a : G) ∈ centralizer (B : Set G) := by
  constructor
  · intro ha v hv
    have he := d.equivariant a ⟨v,hv⟩
    rw [ha,map_one,Module.End.one_apply] at he
    have he' := d.coordinates.injective (Multiplicative.toAdd.injective he)
    have h := congrArg Subtype.val he'
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro ha
    apply SL3DoubledNaturalOffenders.representation_injective F
    rw [map_one]
    apply LinearMap.ext
    intro w
    obtain ⟨v,hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
    have he : B.normalizerMonoidHom (inclusion d.normalized a) v = v := by
      apply Subtype.ext
      change (a : G) * (v : G) * (a : G)⁻¹ = (v : G)
      rw [← ha v v.property,mul_inv_cancel_right]
    have hh := d.equivariant a v
    rw [he,hv] at hh
    exact hh.symm

omit [Finite F] in
/-- The rank of the actual natural image is the literal action corank. -/
theorem actor_rank : rank d.actor.range =
    ChapterE.subgroupCorank A (A ⊓ centralizer (B : Set G)) := by
  have hk : d.actor.ker = (centralizer (B : Set G)).subgroupOf A := by
    ext a
    exact d.actor_eq_one a
  unfold rank ChapterE.subgroupCorank
  rw [MonoidHom.range_eq_map,← relIndex_ker,hk,relIndex_top_right,
    inf_relIndex_left]
  rfl

omit [Finite F] in
/-- Model fixed vectors are exactly the ambient centralizer in B. -/
theorem fixed_iff (v : B) :
    (d.coordinates v).toAdd ∈ fixedSpace (ρ (F := F)) d.actor.range ↔
      (v : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hv a ha
    have he := (d.equivariant ⟨a,ha⟩ v).trans (hv ⟨_,⟨⟨a,ha⟩,rfl⟩⟩)
    have he' := d.coordinates.injective (Multiplicative.toAdd.injective he)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he')
  · intro hv x
    obtain ⟨a,ha⟩ := x.property
    change ρ (x : SL(3,F)) (d.coordinates v).toAdd = (d.coordinates v).toAdd
    rw [← ha,← d.equivariant]
    congr 2
    apply Subtype.ext
    change (a : G) * (v : G) * (a : G)⁻¹ = (v : G)
    rw [hv a a.property,mul_inv_cancel_right]

/-- The fixed codimension also uses the full original subgroup, not a quotient
or a chosen summand. -/
theorem fixedCodim_eq_corank [Finite G] :
    fixedCodim (ρ (F := F)) d.actor.range =
      ChapterE.subgroupCorank B (B ⊓ centralizer (A : Set G)) := by
  let U := fixedSpace (ρ (F := F)) d.actor.range
  let C := (centralizer (A : Set G)).subgroupOf B
  let e : C ≃ U :=
    { toFun v := ⟨(d.coordinates v.val).toAdd,(d.fixed_iff v.val).mpr v.property⟩
      invFun w := ⟨d.coordinates.symm (Multiplicative.ofAdd w.val),
        (d.fixed_iff _).mp (by simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using w.property)⟩
      left_inv := fun v => Subtype.ext (d.coordinates.symm_apply_apply v.val)
      right_inv := fun w => Subtype.ext (congrArg Multiplicative.toAdd
        (d.coordinates.apply_symm_apply (Multiplicative.ofAdd w.val))) }
  have hc : Nat.card C = Nat.card U := Nat.card_congr e
  have hb : Nat.card B = Nat.card (Shears.Space F) := Nat.card_congr d.coordinates.toEquiv
  have h₁ := Submodule.card_eq_card_quotient_mul_card U
  have h₂ := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have hq : Nat.card (Shears.Space F ⧸ U) = Nat.card (B ⧸ C) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C))
    calc
      _ = Nat.card (Shears.Space F) := by rw [hc,mul_comm,← h₁]
      _ = Nat.card B := hb.symm
      _ = _ := h₂
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Shears.Space F ⧸ U)
  rw [Nat.card_zmod] at hd
  unfold ChapterE.subgroupCorank
  rw [inf_relIndex_left,relIndex,index_eq_card,← hq,hd,Nat.log_pow (by decide)]
  rfl

include d in
/-- Intrinsic centralizer indices construct the reciprocal shear coordinates. -/
theorem shearCoordinates_of_coranks [Finite G] [IsElementaryAbelian 2 A]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hr : 2*n ≤ ChapterE.subgroupCorank A (A ⊓ centralizer (B : Set G)))
    (hc : ChapterE.subgroupCorank B (B ⊓ centralizer (A : Set G)) ≤ 2*n) :
    Nonempty (ShearCoordinates A B F) := by
  have hne : d.actor.range ≠ ⊥ := by
    intro he
    rw [← d.actor_rank,he,Representation.BinaryOffender.rank_bot] at hr
    omega
  let : IsElementaryAbelian 2 d.actor.range :=
    IsElementaryAbelian.of_surjective d.actor.rangeRestrict d.actor.rangeRestrict_surjective
  exact d.shearCoordinates hn hF ⟨hne,inferInstance⟩
    (d.actor_rank.symm ▸ hr) (d.fixedCodim_eq_corank.symm ▸ hc)

end NaturalAction
end PlaneRecognition
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
