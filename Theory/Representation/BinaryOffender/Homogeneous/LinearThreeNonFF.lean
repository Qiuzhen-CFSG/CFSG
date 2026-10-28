module
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeCoverPair
public import Theory.Representation.PSL3Two.NaturalDualNormalizerMarking
public import Theory.Representation.BinaryOffender.NormalizerNonFF

/-!
# Non-FF action on a moved binary linear-three seed orbit

The cover obstruction supplies two disjoint natural and dual seeds with the
same component marking. Their sum gives explicit coordinates on the full
normalizer orbit. Conjugation embeds the linear normalizer of this sum into
the automorphism group of SL₃(2); its canonical natural-dual action has no
FF offender. Transport through the literal action image therefore excludes
FF for K T on the whole orbit, retaining any original covering kernels
until the cover obstruction proves that they vanish.

The Chapter14 consumer uses the original U/Z and N_T(K), without identifying
this seed orbit with the full component commutator support.
Source: Aschbacher--Smith B.5.1, F.9.18(7),14.6.22, pp.99,326,1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual

/-- The full linear normalizer of the marked pair has no offender. -/
theorem not_isFFModule_normalizer : ¬ IsFFModule (normalizerRepresentation action) := by
  intro h
  apply not_isFFModule_autAction
  exact h.map_equivariant (normalizerRepresentation action) autAction
    normalizerAutomorphism normalizerAutomorphism_injective (LinearEquiv.refl _ _) (by
      intro g v
      have h := eq_autAction_of_covariance (normalizerRepresentation action)
        normalizerAutomorphism (fun g k x => normalizerAutomorphism_intertwines g k x) g
      exact LinearMap.congr_fun h v)
end BinaryLinearThree.NaturalDual

namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {K T : Subgroup D}
  {I : Submodule (ZMod 2) V}

/-- Actual coordinates on the whole orbit, using one component marking. -/
theorem IsIrrPlusWith.natural_dual_orbit_coordinates
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (hmoved : orbitSpan ρ T I ≠ I)
    (hsmall : quadraticRatio (invariantSubspace ρ K (orbitSpan ρ T I)
      (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2) :
    ∃ e : orbitSpan ρ T I ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space,
      ∀ k v, e ((invariantSubspace ρ K (orbitSpan ρ T I)
        (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation k v) =
        BinaryLinearThree.NaturalDual.action (j k) (e v) := by
  obtain ⟨t,u,w,hspan,hdis,hu,hw⟩ :=
    hI.natural_dual_pair_of_small_orbit ρ j l he hmoved hsmall
  let O := orbitSpan ρ T I
  let J := I.map (ρ t.val)
  have hIO : I ≤ O := le_orbitSpan ρ T I
  have hJO : J ≤ O := le_iSup (fun t : T => I.map (ρ t.val)) t
  let f : BinaryLinearThree.NaturalDual.Space →ₗ[ZMod 2] O :=
    ((Submodule.inclusion hIO).comp u.symm.toLinearMap).coprod
      ((Submodule.inclusion hJO).comp w.symm.toLinearMap)
  have hf (x : BinaryLinearThree.NaturalDual.Space) :
      (f x : V) = (u.symm x.1 : V) + (w.symm x.2 : V) := rfl
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    rintro ⟨x,y⟩ hxy
    have hh : (u.symm x : V) + (w.symm y : V) = 0 := congrArg Subtype.val hxy
    have hx : (u.symm x : V) = 0 := Submodule.disjoint_def.mp hdis _ (u.symm x).property
      (by rw [eq_neg_of_add_eq_zero_left hh]; exact J.neg_mem (w.symm y).property)
    have hy : (w.symm y : V) = 0 := by simpa only [hx,zero_add] using hh
    have hx' : u.symm x = 0 := Subtype.ext hx
    have hy' : w.symm y = 0 := Subtype.ext hy
    exact Prod.ext (by simpa using congrArg u hx') (by simpa using congrArg w hy')
  have hfs : Function.Surjective f := by
    intro v
    have hv : (v:V) ∈ I ⊔ J := hspan ▸ v.property
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
    refine ⟨(u ⟨x,hx⟩,w ⟨y,hy⟩),Subtype.ext ?_⟩
    rw [hf,u.symm_apply_apply,w.symm_apply_apply]
    exact hxy
  let e := (LinearEquiv.ofBijective f ⟨hfi,hfs⟩).symm
  have hfK (k : K) (x : BinaryLinearThree.NaturalDual.Space) :
      f (BinaryLinearThree.NaturalDual.action (j k) x) =
      (invariantSubspace ρ K O
        (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation k (f x) := by
    apply Subtype.ext
    rw [hf]
    change (u.symm (BinaryLinearThree.W (j k) x.1):V) +
      (w.symm (BinaryLinearThree.W.dual (j k) x.2):V) = ρ k.val (f x).val
    rw [hf,map_add]
    congr 1
    · have hh : u.symm (BinaryLinearThree.W (j k) x.1) =
          (invariantSubspace ρ K I hI.invariant).toRepresentation k (u.symm x.1) := by
        apply u.injective
        rw [u.apply_symm_apply]
        exact ((hu k (u.symm x.1)).trans
          (congrArg (BinaryLinearThree.W (j k)) (u.apply_symm_apply x.1))).symm
      exact congrArg Subtype.val hh
    · have hh : w.symm (BinaryLinearThree.W.dual (j k) x.2) =
          (invariantSubspace ρ K J
            (hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)).choose).toRepresentation k
            (w.symm x.2) := by
        apply w.injective
        rw [w.apply_symm_apply]
        exact ((hw k (w.symm x.2)).trans
          (congrArg (BinaryLinearThree.W.dual (j k)) (w.apply_symm_apply x.2))).symm
      exact congrArg Subtype.val hh
  refine ⟨e,fun k v => ?_⟩
  obtain ⟨x,rfl⟩ := hfs v
  rw [←hfK]
  exact (LinearEquiv.ofBijective f ⟨hfi,hfs⟩).symm_apply_apply _ |>.trans
    (congrArg (BinaryLinearThree.NaturalDual.action (j k))
      ((LinearEquiv.ofBijective f ⟨hfi,hfs⟩).symm_apply_apply x).symm)

/-- The original K T action on the whole homogeneous seed orbit has non-FF
faithful image. No central covering kernel is removed by assumption. -/
theorem IsIrrPlusWith.orbit_image_not_ff_of_small
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (hmoved : orbitSpan ρ T I ≠ I)
    (hsmall : quadraticRatio (invariantSubspace ρ K (orbitSpan ρ T I)
      (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2) :
    let hO := sup_le (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)
      (orbitSpan_invariant ρ T I)
    ¬ IsFFModule (imageRepresentation
      (invariantSubspace ρ (K ⊔ T) (orbitSpan ρ T I) hO).toRepresentation) := by
  let O := orbitSpan ρ T I
  let J := K ⊔ T
  let L := K.subgroupOf J
  let σ := (invariantSubspace ρ J O
    (sup_le (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)
      (orbitSpan_invariant ρ T I))).toRepresentation
  let c : L ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : L.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hI.normalizes)
  let : L.subtype.range.Normal := by rw [range_subtype]; infer_instance
  obtain ⟨e,heK⟩ := hI.natural_dual_orbit_coordinates ρ j l he hmoved hsmall
  let f : L →* BinaryLinearThree.Group := (c.trans j).toMonoidHom
  let b : Representation.Equiv (σ.comp L.subtype)
      (BinaryLinearThree.NaturalDual.action.comp f) := {
    toLinearEquiv := e
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      exact heK (c k) v }
  exact not_isFFModule_image_of_marked_normal_range σ L.subtype
    BinaryLinearThree.NaturalDual.action f (c.trans j).surjective b
    BinaryLinearThree.NaturalDual.not_isFFModule_normalizer

end Representation.BinaryOffender.Homogeneous
