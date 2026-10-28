module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneFixedSpace
public import Theory.Representation.Suzuki.OddDisplacement
public import Theory.Representation.BinaryNormalizerResidual

/-!
# Suzuki odd-prime displacement in the original action coordinates

The specified group and vector-space equivalences conjugate the full linear
normalizer to the concrete Suzuki normalizer. Fixed codimension and the
order of each actor are preserved under this conjugation and under an
injective marking of the ambient action. This transfers H.3 without
replacing the original component, its module, or the automizer action.
Source: Aschbacher--Smith, H.3 and Table 7.2.1, printed pp.379,698.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource
variable {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) G E} {Q : Subgroup G}

/-- The natural Suzuki odd-prime bound in the original component coordinates. -/
theorem suzuki_normalizer_odd_prime_fixedCodim {m : ℕ} (hm : 1 ≤ m)
    (M : ChapterK.RankOne.SuzukiModel m ρ Q)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (a : linearNormalizer (ρ.comp Q.subtype)) (ha : orderOf a = p) :
    8 * (2*m+1) ≤ 3 * fixedCodim (normalizerRepresentation (ρ.comp Q.subtype)) (zpowers a) := by
  let σ := ρ.comp Q.subtype
  let μ := SuzukiNatural.natural m
  let c := BinaryNormalizerResidual.unitConj M.coordinates
  have hn (a : linearNormalizer σ) : c a.val ∈ linearNormalizer μ := by
    rw [← BinaryNormalizerResidual.normalizer_map σ μ M.groupEquiv M.coordinates M.intertwines]
    exact mem_map_of_mem c.toMonoidHom a.property
  let f : linearNormalizer σ →* linearNormalizer μ :=
    (c.toMonoidHom.comp (linearNormalizer σ).subtype).codRestrict _ hn
  have hf : Function.Injective f := fun _ _ he => Subtype.ext (c.injective (congrArg Subtype.val he))
  have hfa : orderOf (f a) = p := (orderOf_injective f hf a).trans ha
  have he (x : linearNormalizer σ) (v : E) :
      M.coordinates (normalizerRepresentation σ x v) =
        normalizerRepresentation μ (f x) (M.coordinates v) := by
    change _ = M.coordinates (normalizerRepresentation σ x (M.coordinates.symm (M.coordinates v)))
    rw [M.coordinates.symm_apply_apply]
  have hb := SuzukiNatural.normalizer_odd_prime_fixedCodim m hm hp ho (f a) hfa
  have hc := fixedCodim_map_equivariant (normalizerRepresentation σ)
    (normalizerRepresentation μ) f M.coordinates he (zpowers a)
  rw [MonoidHom.map_zpowers] at hc
  rwa [hc]

variable {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]

/-- Transport the bound through the complete, injective action marking. -/
theorem suzuki_odd_prime_fixedCodim_of_normalizer_marking {m : ℕ} (hm : 1 ≤ m)
    (M : ChapterK.RankOne.SuzukiModel m ρ Q)
    (τ : Representation (ZMod 2) X W)
    (j : X →* linearNormalizer (ρ.comp Q.subtype)) (hj : Function.Injective j)
    (e : E ≃ₗ[ZMod 2] W)
    (he : ∀ a v, e (normalizerRepresentation (ρ.comp Q.subtype) (j a) v) = τ a (e v))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (a : X) (ha : orderOf a = p) :
    8 * (2*m+1) ≤ 3 * fixedCodim τ (zpowers a) := by
  have hja : orderOf (j a) = p := (orderOf_injective j hj a).trans ha
  have hcoord (a : X) (v : W) :
      e.symm (τ a v) = normalizerRepresentation (ρ.comp Q.subtype) (j a) (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
  have hc := fixedCodim_map_equivariant τ (normalizerRepresentation (ρ.comp Q.subtype))
    j e.symm hcoord (zpowers a)
  rw [MonoidHom.map_zpowers] at hc
  rw [hc]
  exact suzuki_normalizer_odd_prime_fixedCodim hm M hp ho (j a) hja
end CFSG.Quasithin.Chapter7.NormalizedSource
