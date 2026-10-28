module
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeNonFF

/-!
# Non-FF orbits of actual natural binary-three seeds

A three-dimensional homogeneous seed with natural central quotient has no
covering kernel. Its moved normalizer orbit is the direct sum of the literal
natural and dual seeds. The explicit pair coordinates identify the action
image with a subgroup of the full natural-dual normalizer, which has no FF
modules. No quadratic-ratio hypothesis is needed once the seed dimension is
known. The final theorem starts with actual natural coordinates and checks
the fixed kernel before applying the central-quotient inertia theorem.

The original irreducible-section application is Chapter14's
ComponentSupports.Modules.Recognition.QuotientNonFF. Source: Aschbacher--Smith
A.1.40--42, B.5.1 and14.6.22, printed pp.31--32,99,1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {K T : Subgroup D}
  {I : Submodule (ZMod 2) V}

/-- A moved three-dimensional seed gives a literal natural/dual pair. -/
theorem IsIrrPlusWith.natural_dual_pair_of_finrank_three
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (hmoved : orbitSpan ρ T I ≠ I)
    (hd3 : Module.finrank (ZMod 2) I = 3) :
    ∃ (t : T) (u : I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
      (w : I.map (ρ t.val) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) BinaryLinearThree.Vector),
      orbitSpan ρ T I = I ⊔ I.map (ρ t.val) ∧
      Disjoint I (I.map (ρ t.val)) ∧
      (∀ k v, u ((invariantSubspace ρ K I hI.invariant).toRepresentation k v) =
        BinaryLinearThree.W (j k) (u v)) ∧
      (∀ k v, w ((invariantSubspace ρ K (I.map (ρ t.val))
        (hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)).choose).toRepresentation k v) =
        BinaryLinearThree.W.dual (j k) (w v)) := by
  obtain ⟨t,hne,hspan,_,_,halt⟩ := hI.linear_three_moved_pair ρ j l he hmoved
  have hb := hI.linear_three_orbit_finrank_le ρ j
  have hd6 : Module.finrank (ZMod 2) (orbitSpan ρ T I) = 6 := by omega
  obtain ⟨U,W,p,q,hU,hW,hp,hq,hdU,hdW,_⟩ := hI.natural_dual_cover_pair ρ t j l he hne
  let O := orbitSpan ρ T I
  let J := I.map (ρ t.val)
  let u₀ : U.toSubmodule ≃ₗ[ZMod 2] I := (LinearEquiv.ofEq _ _ hU).trans
    (Submodule.comapSubtypeEquivOfLe (le_orbitSpan ρ T I))
  let w₀ : W.toSubmodule ≃ₗ[ZMod 2] J := (LinearEquiv.ofEq _ _ hW).trans
    (Submodule.comapSubtypeEquivOfLe (le_iSup (fun t : T => I.map (ρ t.val)) t))
  have hiP : Function.Injective p.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdU.trans (hd3.trans (Module.finrank_fin_fun (ZMod 2)).symm))).mpr hp.1
  have hiQ : Function.Injective q.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq,Module.finrank_fin_fun]
      exact hdW.trans hd3)).mpr hq.1
  let u := u₀.symm.trans (LinearEquiv.ofBijective p.toLinearMap ⟨hiP,hp.1⟩)
  let w := w₀.symm.trans (LinearEquiv.ofBijective q.toLinearMap ⟨hiQ,hq.1⟩)
  have hu (v : U.toSubmodule) : (u₀ v).val = v.val.val := by
    change ((LinearEquiv.ofEq _ _ hU) v).val.val = v.val.val
    rfl
  have hw (v : W.toSubmodule) : (w₀ v).val = v.val.val := by
    change ((LinearEquiv.ofEq _ _ hW) v).val.val = v.val.val
    rfl
  refine ⟨t,u,w,hspan,?_,?_,?_⟩
  · apply disjoint_iff.mpr
    have hh := I.finrank_sup_add_finrank_inf_eq J
    rw [←hspan,hd6,finrank_map_action,hd3] at hh
    change I ⊓ J = ⊥
    have hh0 : Module.finrank (ZMod 2) ↥(I ⊓ J) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp hh0
  · intro k v
    obtain ⟨x,rfl⟩ := u₀.surjective v
    have heq : (invariantSubspace ρ K I hI.invariant).toRepresentation k (u₀ x) =
        u₀ (U.toRepresentation (j k) x) := by
      apply Subtype.ext
      change ρ k.val (u₀ x).val = (u₀ (U.toRepresentation (j k) x)).val
      rw [hu,hu]
      change ρ k.val x.val.val = ρ (j.symm (j k)).val x.val.val
      rw [j.symm_apply_apply]
    rw [heq]
    change p (u₀.symm (u₀ (U.toRepresentation (j k) x))) =
      BinaryLinearThree.W (j k) (p (u₀.symm (u₀ x)))
    rw [u₀.symm_apply_apply,u₀.symm_apply_apply]
    exact LinearMap.congr_fun (p.isIntertwining' (j k)) x
  · intro k v
    obtain ⟨x,rfl⟩ := w₀.surjective v
    have heq : (invariantSubspace ρ K J
        (hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)).choose).toRepresentation k (w₀ x) =
        w₀ (W.toRepresentation (j k) x) := by
      apply Subtype.ext
      change ρ k.val (w₀ x).val = (w₀ (W.toRepresentation (j k) x)).val
      rw [hw,hw]
      change ρ k.val x.val.val = ρ (j.symm (j k)).val x.val.val
      rw [j.symm_apply_apply]
    rw [heq]
    change q (w₀.symm (w₀ (W.toRepresentation (j k) x))) =
      BinaryLinearThree.W.dual (j k) (q (w₀.symm (w₀ x)))
    rw [w₀.symm_apply_apply,w₀.symm_apply_apply]
    exact LinearMap.congr_fun (q.isIntertwining' (j k)) x


theorem IsIrrPlusWith.natural_dual_orbit_coordinates_of_finrank_three
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (hmoved : orbitSpan ρ T I ≠ I)
    (hd3 : Module.finrank (ZMod 2) I = 3) :
    ∃ e : orbitSpan ρ T I ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space,
      ∀ k v, e ((invariantSubspace ρ K (orbitSpan ρ T I)
        (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation k v) =
        BinaryLinearThree.NaturalDual.action (j k) (e v) := by
  obtain ⟨t,u,w,hspan,hdis,hu,hw⟩ :=
    hI.natural_dual_pair_of_finrank_three ρ j l he hmoved hd3
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
theorem IsIrrPlusWith.orbit_image_not_ff_of_finrank_three
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (hmoved : orbitSpan ρ T I ≠ I)
    (hd3 : Module.finrank (ZMod 2) I = 3) :
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
  obtain ⟨e,heK⟩ := hI.natural_dual_orbit_coordinates_of_finrank_three ρ j l he hmoved hd3
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


/-- A natural seed and an outer normalizer suffice for the non-FF orbit
exclusion. Its fixed kernel is explicitly checked before using the quotient. -/
theorem IsIrrPlusWith.orbit_image_not_ff_of_natural
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* BinaryLinearThree.Group)
    (l : I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l ((invariantSubspace ρ K I hI.invariant).toRepresentation k v) =
      BinaryLinearThree.W (j k) (l v))
    (hf : I ⊓ fixedSpace ρ K = ⊥)
    (hout : ∃ t : T, ¬ ∃ k : K,
      K.normalizerMonoidHom ⟨t,hI.normalizes t.property⟩ = MulAut.conj k) :
    let hO := sup_le (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)
      (orbitSpan_invariant ρ T I)
    ¬ IsFFModule (imageRepresentation
      (invariantSubspace ρ (K ⊔ T) (orbitSpan ρ T I) hO).toRepresentation) := by
  let C := (fixedSpace ρ K).comap I.subtype
  have hC : C = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    have hh : (v : V) ∈ I ⊓ fixedSpace ρ K := ⟨v.property,hv⟩
    rwa [hf] at hh
  let lQ : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector :=
    (C.quotEquivOfEqBot hC).trans l
  have heQ (k : K) (v : centralQuotient ρ K I) :
      lQ (centralQuotientRepresentation ρ K I hI.invariant k v) =
        BinaryLinearThree.W (j k) (lQ v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact he k v
  have hmoved : orbitSpan ρ T I ≠ I := by
    intro hh
    obtain ⟨t,ht⟩ := hout
    apply ht
    apply hI.inner_of_natural_map_eq ρ t j lQ heQ
    apply (subspace_map_eq_iff ρ I t.val).mpr
    exact (hh ▸ orbitSpan_invariant ρ T I) t.property
  exact hI.orbit_image_not_ff_of_finrank_three ρ j lQ heQ hmoved
    (l.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2)))

end Representation.BinaryOffender.Homogeneous
