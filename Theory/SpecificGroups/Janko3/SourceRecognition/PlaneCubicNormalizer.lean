module
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneTransport
public import Theory.SpecificGroups.Janko3.SourceRecognition.BaumeisterParabolics.Point

/-!
# The original plane/cubic normalizer intersection

The cubic selected by the original field embedding is a nontrivial scalar
from the base field. Its normalizer in the whole affine plane group is the
original linear complement: a normalizing element centralizes the scalar,
and the scalar has no nonzero fixed translation. Transport retains the
chosen complement and the literal cubic in G.

Source: Baumeister, A geometry for groups of J₃-type (2007), Lemma 2.11,
with G₂ and G₃ as defined before Lemmas 2.4 and 2.5.
-/

public noncomputable section
open Subgroup
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
namespace Sporadic.Janko3.SourceRecognition.PlaneTransport

private abbrev cubicUnit : Kˣ := cubicUnits (Multiplicative.ofAdd (1 : ZMod 3))

private theorem cubic_scalar : cubic = scalar cubicUnit := by
  change SemidirectProduct.inr (complementEquiv (Multiplicative.ofAdd (1 : ZMod 3), 1)) = _
  apply congrArg SemidirectProduct.inr
  apply Subtype.ext
  change multiplication cubicUnit * dihedralHom 1 = multiplication cubicUnit
  rw [map_one, mul_one]

private theorem cubicUnit_base :
    (cubicUnit : K) = algebraMap F K (cubicUnit : K).re := by decide +kernel

private theorem cubicUnit_ne_one : (cubicUnit : K) ≠ 1 := by decide +kernel

private theorem cubic_matrix_central :
    matrixEquiv (multiplication cubicUnit) ∈ center LinearGroup := by
  apply mem_center_iff.mpr
  intro g
  obtain ⟨l, rfl⟩ := matrixEquiv.surjective g
  rw [← map_mul, ← map_mul]
  apply congrArg matrixEquiv
  apply LinearEquiv.ext
  intro x
  change l ((cubicUnit : K) * x) = (cubicUnit : K) * l x
  rw [cubicUnit_base, ← Algebra.smul_def, ← Algebra.smul_def]
  exact l.map_smul _ _

private theorem naturalAction_injective : Function.Injective naturalAction := by
  intro g h he
  apply Representation.SL2FourNatural.SemilinearNormalizer.glEquiv.injective
  apply LinearEquiv.ext
  intro v
  exact congrArg Multiplicative.toAdd
    (congrArg (fun a : MulAut Plane => a (Multiplicative.ofAdd v)) he)

private theorem cubic_action_coordinates (x : Multiplicative K) :
    naturalAction (matrixEquiv (multiplication cubicUnit)) (rootCoordinates x) =
      rootCoordinates (Multiplicative.ofAdd ((cubicUnit : K) * x.toAdd)) := by
  change Representation.SL2FourNatural.SemilinearNormalizer.glEquiv
    (matrixEquiv (multiplication cubicUnit)) (coordinates x.toAdd) = _
  rw [matrixEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change coordinates ((cubicUnit : K) * coordinates.symm (coordinates x.toAdd)) = _
  rw [coordinates.symm_apply_apply]
  rfl

private theorem cubic_action_fixed (v : Plane)
    (h : naturalAction (matrixEquiv (multiplication cubicUnit)) v = v) : v = 1 := by
  obtain ⟨x, rfl⟩ := rootCoordinates.surjective v
  rw [cubic_action_coordinates] at h
  have hx : (cubicUnit : K) * x.toAdd = x.toAdd :=
    congrArg Multiplicative.toAdd (rootCoordinates.injective h)
  have hz : x.toAdd = 0 := by
    by_contra hn
    exact cubicUnit_ne_one (mul_right_cancel₀ hn (hx.trans (one_mul _).symm))
  have hx1 : x = 1 := congrArg Multiplicative.ofAdd hz
  rw [hx1, map_one]

private theorem affine_scalar_normalizer
    {V L : Type*} [Group V] [Group L] (ρ : L →* MulAut V)
    (z : L) (hz : z ∈ center L) (hfix : ∀ v, ρ z v = v → v = 1) :
    normalizer (zpowers (SemidirectProduct.inr z : V ⋊[ρ] L) : Set (V ⋊[ρ] L)) =
      (SemidirectProduct.inr : L →* V ⋊[ρ] L).range := by
  apply le_antisymm
  · intro x hx
    have hh := (mem_normalizer_iff.mp hx (SemidirectProduct.inr z)).mp (mem_zpowers _)
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hh
    rw [← map_zpow] at hn
    have hr := congrArg SemidirectProduct.right hn
    change z ^ n = x.right * z * x.right⁻¹ at hr
    rw [mem_center_iff.mp hz x.right, mul_inv_cancel_right] at hr
    rw [hr] at hn
    have hcomm : x * SemidirectProduct.inr z = SemidirectProduct.inr z * x :=
      mul_inv_eq_iff_eq_mul.mp hn.symm
    have hl := congrArg SemidirectProduct.left hcomm
    have hleft : x.left = 1 := hfix x.left (by simpa using hl.symm)
    exact ⟨x.right, SemidirectProduct.ext hleft.symm rfl⟩
  · rintro _ ⟨g, rfl⟩
    apply (centralizer_le_normalizer _)
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    have hc : Commute (SemidirectProduct.inr g : V ⋊[ρ] L) (SemidirectProduct.inr z) := by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mem_center_iff.mp hz g]
    exact (hc.zpow_right n).eq.symm

set_option maxHeartbeats 800000 in
/-- The intersection of the full original plane and cubic normalizers is
exactly the chosen GL₂(4) complement, with the original field embedding. -/
theorem field_cubic_normalizer_intersection
    {G : Type*} [Group G]
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : Model →* G) (hj : FieldEmbedding A C a j) :
    normalizer (A : Set G) ⊓ normalizer (zpowers (j cubic) : Set G) =
      C.map (normalizer (A : Set G)).subtype := by
  let N := normalizer (A : Set G)
  obtain ⟨e, heA, heC⟩ := affine_equiv_of_complement A C l a hC ha
  let jN : Model →* N := j.codRestrict N (fun x => hj.2.1 ⟨x, rfl⟩)
  let q := e.toMonoidHom.comp jN
  have hroot (x : Multiplicative K) : q (root x) =
      SemidirectProduct.inl (rootCoordinates x) := by
    have hr : jN (root x) = inclusion le_normalizer (a.symm (rootCoordinates x)) :=
      Subtype.ext (hj.2.2.2.1 x)
    change e (jN (root x)) = _
    rw [hr, heA, a.apply_symm_apply]
  obtain ⟨c, hc, hcv⟩ := hj.2.2.2.2.1 cubicUnit
  have hqc : q cubic = SemidirectProduct.inr (l ⟨c, hc⟩) := by
    change e (jN cubic) = _
    rw [show jN cubic = c from Subtype.ext (cubic_scalar ▸ hcv.symm)]
    exact heC ⟨c, hc⟩
  have hqs : q cubic =
      SemidirectProduct.inr (matrixEquiv (multiplication cubicUnit)) := by
    rw [hqc]
    apply congrArg SemidirectProduct.inr
    apply naturalAction_injective
    apply MulEquiv.ext
    intro v
    obtain ⟨x, rfl⟩ := rootCoordinates.surjective v
    have hh := congrArg q (cubic_scalar ▸ scalar_conjugation cubicUnit x)
    rw [map_mul, map_mul, map_inv, hqc, hroot, hroot, ← map_inv,
      ← SemidirectProduct.inl_aut] at hh
    exact (SemidirectProduct.inl_injective hh).trans (cubic_action_coordinates x).symm
  have hCs : C.map e.toMonoidHom =
      (SemidirectProduct.inr : LinearGroup →* Plane ⋊[naturalAction] LinearGroup).range := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨l ⟨c, hc⟩, (heC ⟨c, hc⟩).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨l.symm g, (l.symm g).property, by simpa using heC (l.symm g)⟩
  have hNs : normalizer (zpowers (jN cubic) : Set N) = C := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_equiv_normalizer_eq, MonoidHom.map_zpowers]
    change normalizer (zpowers (q cubic) : Set (Plane ⋊[naturalAction] LinearGroup)) = _
    rw [hqs, affine_scalar_normalizer naturalAction _ cubic_matrix_central cubic_action_fixed,
      hCs]
  have hcomap : (normalizer (zpowers (j cubic) : Set G)).comap N.subtype = C := by
    rw [comap_normalizer_eq_of_le_range (by
      rw [N.range_subtype]
      exact zpowers_le.mpr (jN cubic).property)]
    have hs : (zpowers (j cubic)).comap N.subtype = zpowers (jN cubic) := by
      rw [show zpowers (j cubic) = (zpowers (jN cubic)).map N.subtype from
        (MonoidHom.map_zpowers N.subtype (jN cubic)).symm, comap_map_eq,
        N.subtype.ker_eq_bot N.subtype_injective, sup_bot_eq]
    rw [hs, hNs]
  ext x
  constructor
  · rintro ⟨hxA, hxs⟩
    exact ⟨⟨x, hxA⟩, hcomap ▸ hxs, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    change x ∈ (normalizer (zpowers (j cubic) : Set G)).comap N.subtype
    rwa [hcomap]

end Sporadic.Janko3.SourceRecognition.PlaneTransport
