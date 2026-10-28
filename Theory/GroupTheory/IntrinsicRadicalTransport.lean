module

public import Theory.GroupTheory.CentricRadicalAutomorphisms

/-!
# Intrinsic radical transport from an intermediate subgroup

For `U ≤ T ≤ G` and an isomorphism `T ≃* H`, the image of `U` in `H` is
self-centralizing precisely when `T ⊓ C_G(U) ≤ U`. Its intrinsic radical
condition is equivalent to the condition on the literal ambient normalizer
image `(T.subgroupOf (normalizer U)).map U.normalizerMonoidHom`.

The key identity transports the normalizer action inside `T` along
`U.subgroupOf T ≃* U`. Conjugation of automorphisms preserves inner
automorphisms and the p-core; ambient isomorphism transport then finishes the
argument. The same subgroup equivalence identifies restricted characters and
pulls back characteristic kernels. No finiteness assumption is needed.

Source: elementary functoriality of conjugation and kernels, together with
`Subgroup.intrinsic_radical_of_map_equiv` in `CentricRadicalAutomorphisms`
and `pCore_map_iso` in `Theory.PGroupCore`.
-/

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The intrinsic normalizer action inside an overgroup becomes exactly the
restricted ambient normalizer image under the canonical subgroup equivalence. -/
public theorem normalizer_range_subgroupOf_map_congr (U T : Subgroup G) (hUT : U ≤ T) :
    (U.subgroupOf T).normalizerMonoidHom.range.map
        (MulAut.congr (subgroupOfEquivOfLe hUT)).toMonoidHom =
      (T.subgroupOf (normalizer (U : Set G))).map U.normalizerMonoidHom := by
  apply le_antisymm
  · rintro a ⟨b, ⟨x, rfl⟩, rfl⟩
    have hn : (x.val : G) ∈ normalizer (U : Set G) := by
      exact (show x.val ∈ (normalizer (U : Set G)).subgroupOf T from
        (subgroupOf_normalizer_eq hUT).symm ▸ x.property)
    refine ⟨⟨x.val, hn⟩, x.val.property, ?_⟩
    apply MulEquiv.ext
    intro y
    rfl
  · rintro a ⟨x, hx, rfl⟩
    have hn : (⟨x.val, hx⟩ : T) ∈ normalizer (U.subgroupOf T : Set T) := by
      rw [← subgroupOf_normalizer_eq hUT]
      exact x.property
    let y : normalizer (U.subgroupOf T : Set T) := ⟨⟨x.val, hx⟩, hn⟩
    refine ⟨(U.subgroupOf T).normalizerMonoidHom y, ⟨y, rfl⟩, ?_⟩
    apply MulEquiv.ext
    intro z
    rfl

private theorem inner_range_map_congr (e : G ≃* H) :
    (MulAut.conj : G →* MulAut G).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : H →* MulAut H).range := by
  apply le_antisymm
  · rintro a ⟨b, ⟨g, rfl⟩, rfl⟩
    refine ⟨e g, ?_⟩
    ext x
    change e g * x * (e g)⁻¹ = e (g * e.symm x * g⁻¹)
    simp only [map_mul, map_inv, e.apply_symm_apply]
  · rintro a ⟨h, rfl⟩
    refine ⟨MulAut.conj (e.symm h), ⟨e.symm h, rfl⟩, ?_⟩
    ext x
    change e (e.symm h * e.symm x * (e.symm h)⁻¹) = h * x * h⁻¹
    simp only [map_mul, map_inv, e.apply_symm_apply]

private theorem radical_map_congr_iff (e : G ≃* H) (R : Subgroup (MulAut G)) (p : ℕ) :
    R.map (MulAut.congr e).toMonoidHom ⊓ pCore p (MulAut H) ≤
        (MulAut.conj : H →* MulAut H).range ↔
      R ⊓ pCore p (MulAut G) ≤ (MulAut.conj : G →* MulAut G).range := by
  rw [← pCore_map_iso p (MulAut.congr e), ← map_inf _ _ _ (MulAut.congr e).injective,
    ← inner_range_map_congr e]
  exact map_le_map_iff_of_injective (MulAut.congr e).injective

/-- Intrinsic radicality inside an overgroup, expressed using ambient maps. -/
public theorem intrinsic_radical_subgroupOf_iff (U T : Subgroup G) (hUT : U ≤ T) (p : ℕ) :
    (U.subgroupOf T).normalizerMonoidHom.range ⊓ pCore p (MulAut (U.subgroupOf T)) ≤
        (MulAut.conj : U.subgroupOf T →* MulAut (U.subgroupOf T)).range ↔
      (T.subgroupOf (normalizer (U : Set G))).map U.normalizerMonoidHom ⊓
        pCore p (MulAut U) ≤ (MulAut.conj : U →* MulAut U).range := by
  rw [← normalizer_range_subgroupOf_map_congr U T hUT]
  exact (radical_map_congr_iff (subgroupOfEquivOfLe hUT) _ p).symm

/-- Intrinsic radicality is invariant under an ambient group isomorphism. -/
public theorem intrinsic_radical_map_equiv_iff (e : G ≃* H) (U : Subgroup G) (p : ℕ) :
    (U.map e.toMonoidHom).normalizerMonoidHom.range ⊓
        pCore p (MulAut (U.map e.toMonoidHom)) ≤
        (MulAut.conj : U.map e.toMonoidHom →* MulAut (U.map e.toMonoidHom)).range ↔
      U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
        (MulAut.conj : U →* MulAut U).range := by
  refine ⟨intrinsic_radical_of_map_equiv e U p, ?_⟩
  intro h
  apply intrinsic_radical_of_map_equiv e.symm
  have hm : (U.map e.toMonoidHom).map e.symm.toMonoidHom = U := by
    simp [map_map]
  rwa [hm]


/-- The subgroup equivalence associated to a realization of an overgroup. -/
@[expose] public def subgroupOfMapEquiv (U T : Subgroup G) (hUT : U ≤ T) (e : T ≃* H) :
    U ≃* (U.subgroupOf T).map e.toMonoidHom :=
  (subgroupOfEquivOfLe hUT).symm.trans (e.subgroupMap (U.subgroupOf T))

/-- Self-centralization in a model of the overgroup is relative
self-centralization in the ambient group. -/
public theorem centralizer_subgroupOf_map_le_iff
    (U T : Subgroup G) (hUT : U ≤ T) (e : T ≃* H) :
    centralizer ((U.subgroupOf T).map e.toMonoidHom : Set H) ≤
        (U.subgroupOf T).map e.toMonoidHom ↔
      T ⊓ centralizer (U : Set G) ≤ U := by
  constructor
  · intro hc x hx
    have hec : e ⟨x, hx.1⟩ ∈
        centralizer ((U.subgroupOf T).map e.toMonoidHom : Set H) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have hh : y.val * x = x * y.val := mem_centralizer_iff.mp hx.2 y.val hy
      have ht : y * ⟨x, hx.1⟩ = ⟨x, hx.1⟩ * y := Subtype.ext hh
      change e y * e ⟨x, hx.1⟩ = e ⟨x, hx.1⟩ * e y
      rw [← map_mul, ← map_mul]
      exact congrArg e ht
    obtain ⟨y, hy, he⟩ := hc hec
    have hyx := congrArg Subtype.val (e.injective he)
    change (y : G) ∈ U at hy
    change (y : G) = x at hyx
    exact hyx ▸ hy
  · intro hc x hx
    have hec : ((e.symm x : T) : G) ∈ centralizer (U : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have hh := mem_centralizer_iff.mp hx (e ⟨y, hUT hy⟩)
        (mem_map_of_mem e.toMonoidHom (show (⟨y, hUT hy⟩ : T) ∈ U.subgroupOf T from hy))
      have hh' : (⟨y, hUT hy⟩ : T) * e.symm x = e.symm x * ⟨y, hUT hy⟩ := by
        apply e.injective
        simpa only [map_mul, e.apply_symm_apply] using hh
      exact congrArg Subtype.val hh'
    exact ⟨e.symm x, hc ⟨(e.symm x).property, hec⟩, e.apply_symm_apply x⟩

/-- Transport intrinsic radicality from a model of an overgroup to the
literal restricted ambient normalizer image. -/
public theorem intrinsic_radical_subgroupOf_map_iff
    (U T : Subgroup G) (hUT : U ≤ T) (e : T ≃* H) (p : ℕ) :
    ((U.subgroupOf T).map e.toMonoidHom).normalizerMonoidHom.range ⊓
        pCore p (MulAut ((U.subgroupOf T).map e.toMonoidHom)) ≤
        (MulAut.conj : (U.subgroupOf T).map e.toMonoidHom →*
          MulAut ((U.subgroupOf T).map e.toMonoidHom)).range ↔
      (T.subgroupOf (normalizer (U : Set G))).map U.normalizerMonoidHom ⊓
        pCore p (MulAut U) ≤ (MulAut.conj : U →* MulAut U).range :=
  (intrinsic_radical_map_equiv_iff e (U.subgroupOf T) p).trans
    (intrinsic_radical_subgroupOf_iff U T hUT p)

variable {A : Type*} [Monoid A]

/-- Restriction to the model image agrees with restriction through the
inclusion `U → T` under the canonical subgroup equivalence. -/
public theorem restricted_character_subgroupOf_map
    (U T : Subgroup G) (hUT : U ≤ T) (e : T ≃* H) (χ : H →* A) :
    (χ.comp ((U.subgroupOf T).map e.toMonoidHom).subtype).comp
        (subgroupOfMapEquiv U T hUT e).toMonoidHom =
      (χ.comp e.toMonoidHom).comp (inclusion hUT) := by
  ext x
  rfl

/-- A characteristic restricted character kernel in the model pulls back
to a characteristic kernel on the ambient subgroup. -/
public theorem characteristic_ker_subgroupOf_map
    (U T : Subgroup G) (hUT : U ≤ T) (e : T ≃* H) (χ : H →* A)
    (hc : (χ.comp ((U.subgroupOf T).map e.toMonoidHom).subtype).ker.Characteristic) :
    ((χ.comp e.toMonoidHom).comp (inclusion hUT)).ker.Characteristic := by
  let u := subgroupOfMapEquiv U T hUT e
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  have hx' : u x ∈ (χ.comp ((U.subgroupOf T).map e.toMonoidHom).subtype).ker := hx
  have ha := characteristic_iff_le_comap.mp hc (MulAut.congr u a) hx'
  change χ (u (a (u.symm (u x)))) = 1 at ha
  change χ (u (a x)) = 1
  simpa only [u.symm_apply_apply] using ha

end Subgroup
