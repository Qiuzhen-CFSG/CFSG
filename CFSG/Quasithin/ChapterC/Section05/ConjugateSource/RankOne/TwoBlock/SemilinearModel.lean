module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.RootCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CoverModel

/-!
# The full normalizer of the actual natural block model is semilinear

The block's intrinsic natural image is normal in the full normalizer action.
Its natural scalar commutant supplies the field automorphism. The original
normalizer action and its full-cover centralizer kernel remain literal.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/
@[expose] public section
open Subgroup Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

noncomputable def automorphismRepresentation (H : Subgroup (MulAut (Multiplicative (Fin 2 → F)))) :
    Representation (ZMod 2) H (Fin 2 → F) where
  toFun a := (show (Fin 2 → F) →+ (Fin 2 → F) from
    { toFun v := (a.val (Multiplicative.ofAdd v)).toAdd
      map_zero' := congrArg Multiplicative.toAdd a.val.map_one
      map_add' v w := congrArg Multiplicative.toAdd (a.val.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }).toZModLinearMap 2
  map_one' := by ext v i; rfl
  map_mul' a b := by ext v i; rfl

omit [Finite F] [Algebra (ZMod 2) F] in
theorem natural_action_injective
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (hτ : ∀ g v, (τ g v).toAdd = Matrix.mulVec g.val v.toAdd) : Function.Injective τ := by
  intro g k he
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact (hτ g (Multiplicative.ofAdd v)).symm.trans
    ((congrArg (fun a => (a (Multiplicative.ofAdd v)).toAdd) he).trans (hτ k (Multiplicative.ofAdd v)))

/-- Every automorphism normalizing the actual natural SL₂ image is semilinear. -/
theorem natural_image_normalizer_semilinear
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (hτ : ∀ g v, (τ g v).toAdd = Matrix.mulVec g.val v.toAdd)
    (a : normalizer (τ.range : Set (MulAut (Multiplicative (Fin 2 → F))))) :
    ∃ σ : F ≃+* F, ∀ c v,
      (a.val (Multiplicative.ofAdd (c • v))).toAdd = σ c • (a.val (Multiplicative.ofAdd v)).toAdd := by
  let N := normalizer (τ.range : Set (MulAut (Multiplicative (Fin 2 → F))))
  let L := τ.range.subgroupOf N
  let : L.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (subgroupOfEquivOfLe τ.range.le_normalizer).trans (MonoidHom.ofInjective (natural_action_injective τ hτ)).symm
  have hnat (g : L) (v : Fin 2 → F) :
      automorphismRepresentation N (g : N) v = Matrix.mulVec (e g).val v := by
    have he : τ (e g) = ((g : N) : MulAut (Multiplicative (Fin 2 → F))) :=
      MonoidHom.apply_ofInjective_symm (natural_action_injective τ hτ) _
    change (((g : N) : MulAut (Multiplicative (Fin 2 → F))) (Multiplicative.ofAdd v)).toAdd = _
    rw [← he,hτ]
    rfl
  exact Representation.SL2NaturalOffenders.normalizer_semilinear L e (automorphismRepresentation N) hnat a

variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

/-- Literal full-normalizer natural coordinates, retaining the central cover. -/
theorem exists_full_natural_model_action
    (hshort : IsShort K)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel K τ)
    (hτ : ∀ g v, (τ g v).toAdd = Matrix.mulVec g.val v.toAdd) :
    ∃ ρ : normalizer (K : Set G) →* MulAut (Multiplicative (Fin 2 → F)),
      (∀ a u, ρ a (modelProjection m u) = modelProjection m (normalizerConjugate a u)) ∧
      ρ.ker = (centralizer (U K : Set G)).subgroupOf (normalizer (K : Set G)) ∧
      (K.subgroupOf (normalizer (K : Set G))).map ρ = τ.range ∧
      ∀ a, ∃ σ : F ≃+* F, ∀ c v,
        (ρ a (Multiplicative.ofAdd (c • v))).toAdd = σ c • (ρ a (Multiplicative.ofAdd v)).toAdd := by
  obtain ⟨ρ,hρ,hker,himage⟩ := exists_full_model_action hshort m (natural_action_injective τ hτ)
  refine ⟨ρ,hρ,hker,himage,?_⟩
  intro a
  have hn : ρ a ∈ normalizer (τ.range : Set (MulAut (Multiplicative (Fin 2 → F)))) := by
    rw [← himage]
    let : (K.subgroupOf (normalizer (K : Set G))).Normal := normal_subgroupOf_of_le_normalizer le_rfl
    exact le_normalizer_map ρ (mem_map_of_mem ρ (show a ∈ normalizer
      (K.subgroupOf (normalizer (K : Set G)) : Set (normalizer (K : Set G))) from by simpa only [(K.subgroupOf (normalizer (K : Set G))).normalizer_eq_top] using mem_top a))
  exact natural_image_normalizer_semilinear τ hτ ⟨ρ a,hn⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
