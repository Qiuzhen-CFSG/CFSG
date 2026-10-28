module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Essential

/-!
# The original seed inside the essential residual quotient

Every invariant subspace containing V contains its H-conjugate span U. Thus
V has nonzero image in every proper quotient of the literal conjugation
module on U. Its Sylow normalization passes through the quotient map, so
binary fixed-vector theory supplies a nonzero Sylow-fixed seed vector.
The essential quotient theorem puts that vector in its simple residual image.

The final source theorem returns an element of the original V whose image is
this vector. Every actual element centralizing V fixes that same image, which
allows the component Borel lifts to act on the essential simple submodule.
No seed-generation, fixed-vector or compatibility witness is assumed.

Source: Aschbacher–Smith, original3.1.9(5), printed p.578, used in15.1.12(3).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open Representation.EssentialResidualQuotient
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] (H V : Subgroup G)
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

/-- The original V inside the binary module on its H-conjugate span. -/
abbrev spanSeed : Submodule (ZMod 2) (Additive ((conjugateSpan H V).subgroupOf H)) :=
  AddSubgroup.toZModSubmodule 2 ((V.subgroupOf H).subgroupOf
    ((conjugateSpan H V).subgroupOf H)).toAddSubgroup

/-- The literal quotient image of the original seed. -/
abbrev quotientSeed (W : Subrepresentation
    (normalRepresentation ((conjugateSpan H V).subgroupOf H))) :=
  (spanSeed H V).map W.toSubmodule.mkQ

/-- Containing the seed forces an invariant subspace to contain the whole span. -/
theorem spanSeed_generates (hVH : V ≤ H)
    (N : Subrepresentation (normalRepresentation ((conjugateSpan H V).subgroupOf H)))
    (hVN : spanSeed H V ≤ N.toSubmodule) : N = ⊤ := by
  let U := (conjugateSpan H V).subgroupOf H
  let f : U →* G := H.subtype.comp U.subtype
  let K₀ := Subgroup.toAddSubgroup.symm N.toSubmodule.toAddSubgroup
  let K := K₀.map f
  have hVK : V ≤ K := by
    intro v hv
    refine ⟨⟨⟨v,hVH hv⟩,le_conjugateSpan H V hv⟩,?_,rfl⟩
    exact hVN hv
  have hHK : H ≤ normalizer (K : Set G) := by
    apply le_normalizer_iff.mpr
    intro h hh k hk
    obtain ⟨u,hu,rfl⟩ := hk
    refine ⟨(normalRepresentation U ⟨h,hh⟩ (Additive.ofMul u)).toMul,
      N.apply_mem_toSubmodule ⟨h,hh⟩ hu,?_⟩
    rfl
  have hUK : conjugateSpan H V ≤ K := conjugateSpan_le H V K hVK hHK
  apply top_unique
  intro v _
  obtain ⟨u,hu,he⟩ := hUK v.toMul.property
  have heu : u = v.toMul := Subtype.ext (Subtype.ext he)
  change Additive.ofMul u ∈ N at hu
  rwa [heu] at hu

/-- The original seed survives every proper invariant quotient. -/
theorem quotientSeed_ne_bot (hVH : V ≤ H)
    (W : Subrepresentation (normalRepresentation ((conjugateSpan H V).subgroupOf H)))
    (hW : W ≠ ⊤) : quotientSeed H V W ≠ ⊥ := by
  intro hz
  apply hW
  apply spanSeed_generates H V hVH W
  intro v hv
  have hm : W.toSubmodule.mkQ v ∈ quotientSeed H V W := ⟨v,hv,rfl⟩
  rw [hz,Submodule.mem_bot] at hm
  exact (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp hm

/-- Seed normalization survives the actual quotient projection. -/
theorem quotientSeed_stable (P : Subgroup H)
    (hP : P.map H.subtype ≤ normalizer (V : Set G))
    (W : Subrepresentation (normalRepresentation ((conjugateSpan H V).subgroupOf H))) :
    P ≤ subspaceStabilizer W.quotientRepresentation (quotientSeed H V W) := by
  apply le_subspaceStabilizer
  intro p hp q hq
  obtain ⟨v,hv,rfl⟩ := hq
  refine ⟨normalRepresentation _ p v,?_,rfl⟩
  exact le_normalizer_iff.mp hP p (mem_map_of_mem H.subtype hp) _ hv

/-- Every actual centralizer element fixes the same seed in the quotient. -/
theorem quotientSeed_fixed_by_centralizer
    (W : Subrepresentation (normalRepresentation ((conjugateSpan H V).subgroupOf H)))
    (x : H) (hx : (x : G) ∈ centralizer (V : Set G)) :
    ∀ q ∈ quotientSeed H V W, W.quotientRepresentation x q = q := by
  rintro q ⟨v,hv,rfl⟩
  change W.toSubmodule.mkQ (normalRepresentation _ x v) = W.toSubmodule.mkQ v
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  change (x : G) * (v.toMul.val : G) * (x : G)⁻¹ = (v.toMul.val : G)
  exact mul_inv_eq_iff_eq_mul.mpr (hx _ hv).symm

/-- The original seed element, embedded in its actual elementary conjugate span. -/
def spanSeedVector (hVH : V ≤ H) (v : V) :
    Additive ((conjugateSpan H V).subgroupOf H) :=
  Additive.ofMul ⟨⟨v,hVH v.property⟩,le_conjugateSpan H V v.property⟩

variable [Finite G] {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The original seed survives in the essential quotient and supplies a nonzero
Sylow-fixed vector, fixed also by every lift centralizing the original seed. -/
theorem QrcHypotheses.sqtk_essential_fixed_seed
    (h : QrcHypotheses T M M₀ H V)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    let S := T.subtype h.right_mem.1.1.2
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    let ρ := normalRepresentation U
    ∃ W : Subrepresentation ρ,
      ¬ moved ρ (pResidual 2 H) ≤ W ∧
      (∀ N : Subrepresentation ρ, W < N → moved ρ (pResidual 2 H) ≤ N) ∧
      IsIrreducible (W.quotientImage (moved ρ (pResidual 2 H))).toRepresentation ∧
      (∀ N : Subrepresentation W.quotientRepresentation, N ≠ ⊥ →
        W.quotientImage (moved ρ (pResidual 2 H)) ≤ N) ∧
      fixedSpace W.quotientRepresentation (pResidual 2 H) = ⊥ ∧
      ∃ v : V,
        let q := W.toSubmodule.mkQ (spanSeedVector H V (hV.trans (twoCore_le H)) v)
        q ≠ 0 ∧ q ∈ fixedSpace W.quotientRepresentation S ∧
        q ∈ W.quotientImage (moved ρ (pResidual 2 H)) ∧
        ∀ x : H, (x : G) ∈ centralizer (V : Set G) →
          W.quotientRepresentation x q = q := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let U := (conjugateSpan H V).subgroupOf H
  let S := T.subtype h.right_mem.1.1.2
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let ρ := normalRepresentation U
  obtain ⟨W,hW,hmax,hi,he,hfixed,hSylow⟩ := h.sqtk_essential_residual_quotient hu hne hV hq
  have hWtop : W ≠ ⊤ := fun hh => hW (hh ▸ le_top)
  have hSnorm : (S : Subgroup H).map H.subtype ≤ normalizer (V : Set G) := by
    have hsmap : (S : Subgroup H).map H.subtype = T :=
      map_subgroupOf_eq_of_le h.right_mem.1.1.2
    rw [hsmap]
    exact h.sylow_le.trans h.module_normalized
  obtain ⟨q,hqSeed,hqne,hqS⟩ := exists_nonzero_fixed_seed W.quotientRepresentation S
    (quotientSeed H V W) (quotientSeed_stable H V S hSnorm W)
    (quotientSeed_ne_bot H V (hV.trans (twoCore_le H)) W hWtop)
  have hqsocle := hSylow S hqS
  obtain ⟨u,huSeed,huq⟩ := hqSeed
  let v : V := ⟨(u.toMul.val : G),huSeed⟩
  have huv : spanSeedVector H V (hV.trans (twoCore_le H)) v = u := rfl
  refine ⟨W,hW,hmax,hi,he,hfixed,v,?_,?_,?_,?_⟩
  · rw [huv,huq]
    exact hqne
  · rw [huv,huq]
    exact hqS
  · rw [huv,huq]
    exact hqsocle
  · intro x hx
    apply quotientSeed_fixed_by_centralizer H V W x hx
    exact ⟨_,v.property,rfl⟩

end CFSG.Quasithin.Chapter3
