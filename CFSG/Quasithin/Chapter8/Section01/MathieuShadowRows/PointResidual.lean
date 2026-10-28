module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairCentralizers
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Irreducibility

/-!
# The original M22 cocode point residual

The ten-dimensional cocode marking maps the actual point centralizer onto
PSL3(4). Its full kernel is the centralizer of the whole original module.
Surjectivity transports solvable residuals, and the native residual
calculation proves that the original residual moves the whole module.

The lifting proof adapts the eleven-dimensional argument in
`Chapter7.NormalizedSource.MathieuPairCentralizers`; the quotient module
and point stabilizer here are the actual M22 ones. This supplies the point
quotient and movement used to construct C.2.8 in source 8.1.1, without
asserting the ensuing ambient centralizer containment.
Source: Aschbacher--Smith H.15.1 and 8.1.1, printed pp.398,712.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open MathieuCode
variable {G X : Type*} [Group G] [Finite G] [Group X]
    (W K : Subgroup G) [IsElementaryAbelian 2 W]
    (hn : K ≤ normalizer (W : Set G))
    (σ : Representation (ZMod 2) X M22Cocode)
    (q : K →* X) (hq : Function.Surjective q)
    (e : Additive W ≃ₗ[ZMod 2] M22Cocode)
    (he : ∀ k v, e (elementaryRepresentation (p := 2)
      (W.normalizerMonoidHom.comp (inclusion hn)) k v) = σ (q k) (e v))

omit [Finite G] in
include he in
private theorem pair_mem_iff (x : W) (k : K) :
    q k ∈ m22CocodeStabilizer σ (e (Additive.ofMul x)) ↔
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
private theorem point_residual_lift (hσ : Function.Injective σ) (x : W)
    (hm : subspaceCommutator σ ⊤
      ((solvableResidual (m22CocodeStabilizer σ (e (Additive.ofMul x)))).map
        (m22CocodeStabilizer σ (e (Additive.ofMul x))).subtype) = ⊤) :
    ∃ f : (K ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) →*
        m22CocodeStabilizer σ (e (Additive.ofMul x)),
      Function.Surjective f ∧
      (∀ c, (f c).val = q ⟨c.val,c.property.1⟩) ∧
      f.ker = (centralizer (W : Set G)).subgroupOf
        (K ⊓ centralizer ({(x : G)} : Set G)) ∧
      ⁅W, (solvableResidual (K ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = W := by
  let C := K ⊓ centralizer ({(x : G)} : Set G)
  let S := m22CocodeStabilizer σ (e (Additive.ofMul x))
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
    have hτ (r : R) (v : M22Cocode) : τ r (e.symm v) = e.symm (σ (j r) v) := by
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
omit σ q hq e he in
/-- The actual M22 cocode point centralizer covers PSL3(4), with its full
kernel, prescribed native quotient map and residual displacement retained. -/
theorem m22_point_residual
    (q : K →* Sporadic.Mathieu.M22) (hq : Function.Surjective q)
    (E : Additive W ≃ₗ[ZMod 2] M22Cocode)
    (hE : ∀ k v, E (elementaryRepresentation (p := 2)
      (W.normalizerMonoidHom.comp (inclusion hn)) k v) =
        m22CocodeRepresentation (q k) (E v))
    (x : W) (i : Fin 22) (hx : E (Additive.ofMul x) = m22WeightTwoVector i) :
    ∃ f : (K ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) →* Matrix.PSL3Four.PSL,
      Function.Surjective f ∧
      (∀ c, ((m22WeightTwoVector_stabilizer_equiv i).symm (f c)).val =
        q ⟨c.val,c.property.1⟩) ∧
      f.ker = (centralizer (W : Set G)).subgroupOf
        (K ⊓ centralizer ({(x : G)} : Set G)) ∧
      ⁅W, (solvableResidual (K ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = W := by
  have hσ : Function.Injective m22CocodeRepresentation := by
    let := Sporadic.Mathieu.m22_isSimpleGroup
    rcases m22CocodeRepresentation.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact m22CocodeRepresentation.ker_eq_bot_iff.mp hk
    · have he : m22CocodeRepresentation = 1 := MonoidHom.ker_eq_top_iff.mp hk
      have hv : m22WeightTwoVector i ∈ m22CocodeRepresentation.invariants := by
        intro g
        rw [he]
        rfl
      rw [m22Cocode_invariants_eq_bot,Submodule.mem_bot] at hv
      exact (m22WeightTwoVector_ne_zero i hv).elim
  have hmove : subspaceCommutator m22CocodeRepresentation ⊤
      ((solvableResidual (m22CocodeStabilizer m22CocodeRepresentation
        (E (Additive.ofMul x)))).map
          (m22CocodeStabilizer m22CocodeRepresentation (E (Additive.ofMul x))).subtype) = ⊤ := by
    rw [hx]
    exact m22WeightTwoVector_residual_commutator i
  obtain ⟨f,hf,hmap,hker,hcomm⟩ := point_residual_lift W K hn
    m22CocodeRepresentation q hq E hE hσ x hmove
  let e := (MulEquiv.subgroupCongr
    (congrArg (m22CocodeStabilizer m22CocodeRepresentation) hx)).trans
      (m22WeightTwoVector_stabilizer_equiv i)
  refine ⟨e.toMonoidHom.comp f,e.surjective.comp hf,?_,?_,hcomm⟩
  · intro c
    change ((m22WeightTwoVector_stabilizer_equiv i).symm
      ((m22WeightTwoVector_stabilizer_equiv i) _)).val = _
    rw [MulEquiv.symm_apply_apply]
    exact hmap c
  · rw [MonoidHom.ker_comp_of_injective _ _ e.injective,hker]

end CFSG.Quasithin.Chapter8.MathieuShadowRows
