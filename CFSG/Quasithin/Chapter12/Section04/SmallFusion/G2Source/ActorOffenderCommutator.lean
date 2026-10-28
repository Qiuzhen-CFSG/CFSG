module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.NormalizerAction
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.G2OrthogonalCover.BinaryOffenders

/-!
# Literal commutators from the full binary G₂ actor

The full Weyl offender calculation says that its commutator space is its fixed
space. The coordinates of the normalizer actor carry this identity to the
original subgroups: `[V,A] = V ∩ C_G(A)`. The proof first transports the
commutator through the prescribed conjugation map, identifies the fixed
subgroup in the same coordinates, and cancels the coordinate isomorphism.

Source: Aschbacher--Smith B.4.6(3),(13), printed pp.88--90, applied to
12.4.9, printed p.816. The hypothesis that the actor image is an offender
remains with the local-group argument producing that image.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterB.QuasisimpleSource Atlas.G2.Natural
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "σ" => traceZeroAction F
variable {G : Type*} [Group G]
variable {L V A : Subgroup G}

private theorem conjugation_formula
    (b : V ≃* Multiplicative E)
    (φ : normalizer (L : Set G) →* Atlas.G2.Model F)
    (hφ : ∀ (m : normalizer (L : Set G)) (x : E),
      (b.symm (Multiplicative.ofAdd (σ (φ m) x)) : G) =
        (m : G) * (b.symm (Multiplicative.ofAdd x) : G) * (m : G)⁻¹)
    (hAV : A ≤ normalizer (V : Set G)) (hAM : A ≤ normalizer (L : Set G))
    (a : A) (v : V) :
    (b (V.normalizerMonoidHom ⟨a, hAV a.property⟩ v)).toAdd =
      σ (φ (inclusion hAM a)) (b v).toAdd := by
  apply Multiplicative.ofAdd.injective
  apply b.symm.injective
  apply Subtype.ext
  change (b.symm (b (V.normalizerMonoidHom ⟨a, hAV a.property⟩ v)) : G) = _
  rw [b.symm_apply_apply, hφ]
  change _ = (a : G) * (b.symm (b v) : G) * (a : G)⁻¹
  rw [b.symm_apply_apply]
  rfl

/-- The literal ambient commutator identity supplied by full Weyl offender
geometry and the prescribed normalizer action. -/
theorem actor_offender_commutator
    (b : V ≃* Multiplicative E)
    (φ : normalizer (L : Set G) →* Atlas.G2.Model F)
    (hφ : ∀ (m : normalizer (L : Set G)) (x : E),
      (b.symm (Multiplicative.ofAdd (σ (φ m) x)) : G) =
        (m : G) * (b.symm (Multiplicative.ofAdd x) : G) * (m : G)⁻¹)
    (hAV : A ≤ normalizer (V : Set G)) (hAM : A ≤ normalizer (L : Set G))
    (hoff : IsOffender σ (φ.comp (inclusion hAM)).range) :
    ⁅V,A⁆ = V ⊓ centralizer (A : Set G) := by
  let : Module F (Additive (Multiplicative E)) := inferInstanceAs (Module F E)
  let ψ := φ.comp (inclusion hAM)
  have hact (a : A) (v : V) :
      σ (ψ a) (Additive.ofMul (b v)) =
        Additive.ofMul (b ⟨(a : G) * v * (a : G)⁻¹,
          le_normalizer_iff.mp hAV a a.property v v.property⟩) :=
    (conjugation_formula b φ hφ hAV hAM a v).symm
  have htop : binarySubgroup (⊤ : Submodule F (Additive (Multiplicative E))) =
      (V.subgroupOf V).map b.toMonoidHom := by
    rw [subgroupOf_self, map_top_of_surjective _ b.surjective]
    rfl
  have hc := commutator_image_eq σ V V A hAV le_rfl ψ b.toMonoidHom hact ⊤ htop
  have hoffψ : IsOffender σ ψ.range := hoff
  have hmodel : subspaceCommutator σ
      (⊤ : Submodule F (Additive (Multiplicative E))) ψ.range =
        fixedSpace σ ψ.range :=
    OrthogonalCover.BinaryOffenders.offender_commutator_eq_fixed _ hoffψ
  have hcf : (⁅V,A⁆.subgroupOf V).map b.toMonoidHom =
      binarySubgroup (fixedSpace σ ψ.range) :=
    hc.trans (congrArg (fun S : Submodule F (Additive (Multiplicative E)) =>
      binarySubgroup S) hmodel)
  have hf : ((V ⊓ centralizer (A : Set G)).subgroupOf V).map b.toMonoidHom =
      binarySubgroup (fixedSpace σ ψ.range) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩ ⟨_, a, rfl⟩
      change σ (ψ a) (b v).toAdd = (b v).toAdd
      exact (hact a v).trans (congrArg (fun w : V => Additive.ofMul (b w))
        (Subtype.ext (mul_inv_eq_iff_eq_mul.mpr (hv.2 a a.property))))
    · intro hx
      refine ⟨b.symm x, ⟨(b.symm x).property, ?_⟩, b.apply_symm_apply x⟩
      intro a ha
      have hh := hx ⟨ψ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩
      change σ (ψ ⟨a, ha⟩) x.toAdd = x.toAdd at hh
      have he := hφ (inclusion hAM ⟨a, ha⟩) x.toAdd
      have hconj : a * (b.symm x : G) * a⁻¹ = (b.symm x : G) :=
        he.symm.trans (congrArg (fun y : E =>
          (b.symm (Multiplicative.ofAdd y) : G)) hh)
      exact mul_inv_eq_iff_eq_mul.mp hconj
  have he := (map_injective b.injective) (hcf.trans hf.symm)
  have hCV : ⁅V,A⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hAV
  have hh := congrArg (Subgroup.map V.subtype) he
  simpa only [map_subgroupOf_eq_of_le hCV, map_subgroupOf_eq_of_le inf_le_left] using hh

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
