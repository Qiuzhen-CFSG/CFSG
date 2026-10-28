module
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.PairResidual
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.Representation.BinaryOffender.ConjugationCommutator
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Literal centralizers of marked Mathieu cocode pairs

An equivariant surjection from a subgroup K acting on an elementary abelian
W restricts to a surjection from C_K(x) onto the native vector stabilizer.
Faithfulness identifies its entire kernel with C_{C_K(x)}(W). Surjectivity
then carries the actual solvable residual onto the native stabilizer residual;
full native displacement generation lifts to [W,C_K(x)^∞] = W.

The companion NonFFSourceMathieuPairCentralizers application constructs the
surjection from the original L in the M23 and M24 cocode rows. These are the
stabilizer and residual-action inputs of 8.1.1; this module does not assert
that the ambient C_G(x) lies in N_G(L).
Source: Aschbacher--Smith, H.15.1(1)--(2) and 8.1.1, pp.398,712.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
open MathieuCode
variable {G X : Type*} [Group G] [Finite G] [Group X]
    (W K : Subgroup G) [IsElementaryAbelian 2 W]
    (hn : K ≤ normalizer (W : Set G))
    (σ : Representation (ZMod 2) X Cocode)
    (q : K →* X) (hq : Function.Surjective q)
    (e : Additive W ≃ₗ[ZMod 2] Cocode)
    (he : ∀ k v, e (elementaryRepresentation (p := 2)
      (W.normalizerMonoidHom.comp (inclusion hn)) k v) = σ (q k) (e v))

omit [Finite G] in
include he in
private theorem pair_mem_iff (x : W) (k : K) :
    q k ∈ cocodeVectorStabilizer σ (e (Additive.ofMul x)) ↔
      (k : G) ∈ centralizer ({(x : G)} : Set G) := by
  change σ (q k) (e (Additive.ofMul x)) = e (Additive.ofMul x) ↔ _
  rw [← he, e.injective.eq_iff, mem_centralizer_singleton_iff]
  change Additive.ofMul (W.normalizerMonoidHom (inclusion hn k) x) = Additive.ofMul x ↔ _
  rw [Additive.ofMul.injective.eq_iff, Subtype.ext_iff]
  change (k : G) * x * (k : G)⁻¹ = x ↔ _
  rw [mul_inv_eq_iff_eq_mul]

include he hq in
/-- The actual vector centralizer maps onto the native stabilizer, with its
full kernel retained. The perfect residual moves the original whole module. -/
theorem pair_residual_lift (hσ : Function.Injective σ) (x : W)
    (hm : subspaceCommutator σ ⊤
      ((solvableResidual (cocodeVectorStabilizer σ (e (Additive.ofMul x)))).map
        (cocodeVectorStabilizer σ (e (Additive.ofMul x))).subtype) = ⊤) :
    ∃ f : (K ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) →*
        cocodeVectorStabilizer σ (e (Additive.ofMul x)),
      Function.Surjective f ∧
      (∀ c, (f c).val = q ⟨c.val,c.property.1⟩) ∧
      f.ker = (centralizer (W : Set G)).subgroupOf
        (K ⊓ centralizer ({(x : G)} : Set G)) ∧
      ⁅W, (solvableResidual (K ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = W := by
  let C := K ⊓ centralizer ({(x : G)} : Set G)
  let S := cocodeVectorStabilizer σ (e (Additive.ofMul x))
  let k : C →* K := inclusion inf_le_left
  let f : C →* S := (q.comp k).codRestrict S (fun c =>
    (pair_mem_iff W K hn σ q e he x (k c)).mpr c.property.2)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨a,ha⟩ := hq s.val
    have hac : (a : G) ∈ centralizer ({(x : G)} : Set G) :=
      (pair_mem_iff W K hn σ q e he x a).mp (ha ▸ s.property)
    refine ⟨⟨a, a.property,hac⟩,?_⟩
    exact Subtype.ext ha
  refine ⟨f,hf,(fun _ => rfl),?_,?_⟩
  · ext c
    change f c = 1 ↔ (c : G) ∈ centralizer (W : Set G)
    constructor
    · intro hc
      have hq1 : q (k c) = 1 := congrArg Subtype.val hc
      apply mem_centralizer_iff.mpr
      intro w hw
      have hh := he (k c) (Additive.ofMul (⟨w,hw⟩ : W))
      rw [hq1,map_one,Module.End.one_apply] at hh
      have hv := congrArg (fun v : Additive W => (v.toMul : G)) (e.injective hh)
      change (c : G) * w * (c : G)⁻¹ = w at hv
      exact ((mul_inv_eq_iff_eq_mul).mp hv).symm
    · intro hc
      apply Subtype.ext
      apply hσ
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := e.surjective v
      have hv : elementaryRepresentation (p := 2)
          (W.normalizerMonoidHom.comp (inclusion hn)) (k c) w = w := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change (c : G) * (w.toMul : G) * (c : G)⁻¹ = (w.toMul : G)
        rw [mul_inv_eq_iff_eq_mul]
        exact (mem_centralizer_iff.mp hc _ w.toMul.property).symm
      change σ (q (k c)) (e w) = σ 1 (e w)
      simpa only [map_one,Module.End.one_apply,hv] using (he (k c) w).symm
  · let R := (solvableResidual C).map C.subtype
    have hRK : R ≤ K := (map_subtype_le _).trans inf_le_left
    have hRN : R ≤ normalizer (W : Set G) := hRK.trans hn
    let j : R →* X := q.comp (inclusion hRK)
    have hj : j.range = (solvableResidual S).map S.subtype := by
      have hres := congrArg (map S.subtype) (map_solvableResidual_eq f hf)
      rw [map_map] at hres
      rw [←hres]
      ext a
      constructor
      · rintro ⟨r,rfl⟩
        obtain ⟨c,hc,hcr⟩ := r.property
        refine ⟨c,hc,?_⟩
        change q (k c) = q (inclusion hRK r)
        congr 1
        exact Subtype.ext hcr
      · rintro ⟨c,hc,rfl⟩
        exact ⟨⟨c,mem_map_of_mem C.subtype hc⟩,rfl⟩
    let τ := elementaryRepresentation (p := 2)
      (W.normalizerMonoidHom.comp (inclusion hRN))
    have hτ (r : R) (v : Cocode) : τ r (e.symm v) = e.symm (σ (j r) v) := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (he (inclusion hRK r) (e.symm v)).trans
        (by rw [e.apply_symm_apply]; rfl)
    have hh := subspaceCommutator_map_embedding τ σ j e.symm.toLinearMap
      hτ ⊤ ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,hj,hm,Submodule.map_top,
      LinearMap.range_eq_top.mpr e.symm.surjective] at hh
    exact group_commutator_eq_of_elementary_moved W R hRN hh
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
