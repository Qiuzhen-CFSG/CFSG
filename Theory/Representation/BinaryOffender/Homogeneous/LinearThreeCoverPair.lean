module
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreePair
public import Theory.Representation.SLThreeCentralExtension.PairedQuadratic
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport

/-!
# Natural and dual seeds after the four-dimensional cover exclusion

An outer component normalizer carries a marked natural central quotient to
its dual. The original two seed subspaces are embedded in their full orbit,
and the actual quotient maps are transported along the inverse conjugating
operator. Both remain commutator-generated central covers. Distinct seeds
intersect in a fixed space of dimension at most one.

The paired-cover quadratic obstruction therefore excludes dimension four
when the full component orbit has quadratic ratio at most two. The seed
kernels then vanish, giving an actual natural/dual direct sum of dimension
six with explicit intertwining equivalences. No whole-support exhaustion
is assumed or concluded. The original-action consumer is Chapter14's
Modules/Recognition/LinearThreeCoverExclusion.

Source: Aschbacher--Smith B.4.8(2), F.9.18(2), and14.6.22,
printed pp.91,325,1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.OneCohomology
namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K T : Subgroup D}
    {I : Submodule (ZMod 2) V}

private def markedAction (j : K ≃* BinaryLinearThree.Group)
    (O : Submodule (ZMod 2) V) (hO : K ≤ subspaceStabilizer ρ O) :
    Representation (ZMod 2) BinaryLinearThree.Group O :=
  (invariantSubspace ρ K O hO).toRepresentation.comp j.symm.toMonoidHom

private def inside (j : K ≃* BinaryLinearThree.Group)
    (O : Submodule (ZMod 2) V) (hO : K ≤ subspaceStabilizer ρ O)
    (J : Submodule (ZMod 2) V) (hJ : K ≤ subspaceStabilizer ρ J) :
    Subrepresentation (markedAction ρ j O hO) where
  toSubmodule := J.comap O.subtype
  apply_mem_toSubmodule g v hv := (hJ (j.symm g).property v.val).2 hv

private theorem inside_commutator_top (j : K ≃* BinaryLinearThree.Group)
    (O : Submodule (ZMod 2) V) (hO : K ≤ subspaceStabilizer ρ O)
    {J : Submodule (ZMod 2) V} (hJ : IsIrrPlus ρ K J) (hJO : J ≤ O) :
    Coinvariants.ker (inside ρ j O hO J hJ.choose).toRepresentation = ⊤ := by
  let U := inside ρ j O hO J hJ.choose
  let f : U.toSubmodule →ₗ[ZMod 2] V := O.subtype.comp U.toSubmodule.subtype
  have hm : J ≤ (Coinvariants.ker U.toRepresentation).map f := by
    conv_lhs => rw [←hJ.choose_spec.1]
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,hv,rfl⟩
    let w : U.toSubmodule := ⟨⟨v,hJO hv⟩,hv⟩
    refine ⟨U.toRepresentation (j ⟨k,hk⟩) w - w, Coinvariants.sub_mem_ker _ _, ?_⟩
    change ρ (j.symm (j ⟨k,hk⟩)).val v-v = ρ k v-v
    rw [j.symm_apply_apply]
  apply top_unique
  intro v _
  obtain ⟨w,hw,he⟩ := hm v.property
  have hev : w = v := Subtype.ext (Subtype.ext he)
  rwa [hev] at hw

private theorem exists_natural_cover (j : K ≃* BinaryLinearThree.Group)
    (hI : IsIrrPlus ρ K I)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.choose k v) =
      BinaryLinearThree.W (j k) (l v)) :
    ∃ p : Representation.IntertwiningMap
      (markedAction ρ j I hI.choose)
      BinaryLinearThree.W,
      IsCover p := by
  let σ : Representation (ZMod 2) BinaryLinearThree.Group I := markedAction ρ j I hI.choose
  let C := (fixedSpace ρ K).comap I.subtype
  let p : σ.IntertwiningMap BinaryLinearThree.W :=
    (l.toLinearMap.comp C.mkQ).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      have hh := he (j.symm g) (Submodule.Quotient.mk v)
      exact hh.trans (congrArg (fun k => BinaryLinearThree.W k (l (Submodule.Quotient.mk v)))
        (j.apply_symm_apply g)))
  refine ⟨p,l.surjective.comp (Submodule.mkQ_surjective _),?_,?_⟩
  · intro v hv g
    have hz : C.mkQ v = 0 := l.injective (hv.trans l.map_zero.symm)
    have hf := (Submodule.Quotient.mk_eq_zero C).mp hz
    exact Subtype.ext (hf (j.symm g))
  · have hm : I ≤ (Coinvariants.ker σ).map I.subtype := by
      conv_lhs => rw [←hI.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,hv,rfl⟩
      refine ⟨σ (j ⟨g,hg⟩) ⟨v,hv⟩ - ⟨v,hv⟩,Coinvariants.sub_mem_ker _ _,?_⟩
      change ρ (j.symm (j ⟨g,hg⟩)).val v-v = ρ g v-v
      rw [j.symm_apply_apply]
    apply top_unique
    intro v _
    obtain ⟨w,hw,hh⟩ := hm v.property
    rwa [show w = v from Subtype.ext hh] at hw

private theorem moved_automorphism_outer
    (hI : IsIrrPlusWith ρ K T I) (t : T)
    (j : K ≃* BinaryLinearThree.Group) (hne : I.map (ρ t.val) ≠ I) :
    (MulAut.congr j) (K.normalizerMonoidHom ⟨t.val⁻¹,hI.normalizes (T.inv_mem t.property)⟩)
      ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
  rintro ⟨g,hg⟩
  have hn : K.normalizerMonoidHom ⟨t.val⁻¹,hI.normalizes (T.inv_mem t.property)⟩ =
      MulAut.conj (j.symm g) := by
    apply (MulAut.congr j).injective
    rw [←hg]
    ext x
    simp [MulAut.congr_apply,MulAut.conj_apply]
  have hm := hI.map_eq_of_inner ρ t⁻¹ (j.symm g) hn
  exact hne ((subspace_map_eq_iff ρ I t.val).mpr
    ((subspaceStabilizer ρ I).inv_mem_iff.mp ((subspace_map_eq_iff ρ I t.val⁻¹).mp hm)))

/-- The literal moved seeds inside the full orbit are natural and dual central covers. -/
theorem IsIrrPlusWith.natural_dual_cover_pair
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I) (t : T)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (hne : I.map (ρ t.val) ≠ I) :
    let O := orbitSpan ρ T I
    let hO := orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus
    let σ : Representation (ZMod 2) BinaryLinearThree.Group O :=
      (invariantSubspace ρ K O hO).toRepresentation.comp j.symm.toMonoidHom
    ∃ (U W : Subrepresentation σ)
      (p : U.toRepresentation.IntertwiningMap BinaryLinearThree.W)
      (q : W.toRepresentation.IntertwiningMap BinaryLinearThree.W.dual),
      U.toSubmodule = I.comap O.subtype ∧
      W.toSubmodule = (I.map (ρ t.val)).comap O.subtype ∧
      IsCover p ∧ IsCover q ∧
      Module.finrank (ZMod 2) U.toSubmodule = Module.finrank (ZMod 2) I ∧
      Module.finrank (ZMod 2) W.toSubmodule = Module.finrank (ZMod 2) I ∧
      Module.finrank (ZMod 2) ↥(U.toSubmodule ⊓ W.toSubmodule) ≤ 1 := by
  let O := orbitSpan ρ T I
  have hO := orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus
  let J := I.map (ρ t.val)
  have hJ := hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)
  have hIO : I ≤ O := le_orbitSpan ρ T I
  have hJO : J ≤ O := le_iSup (fun t : T => I.map (ρ t.val)) t
  let U := inside ρ j O hO I hI.isIrrPlus.choose
  let W := inside ρ j O hO J hJ.choose
  let u : U.toSubmodule ≃ₗ[ZMod 2] I := Submodule.comapSubtypeEquivOfLe hIO
  let w : W.toSubmodule ≃ₗ[ZMod 2] J := Submodule.comapSubtypeEquivOfLe hJO
  let c := Submodule.equivMapOfInjective (ρ t.val) (ρ.apply_bijective t.val).1 I
  let r := w.trans c.symm
  let σI : Representation (ZMod 2) BinaryLinearThree.Group I := markedAction ρ j I hI.isIrrPlus.choose
  obtain ⟨p₀,hp₀⟩ := exists_natural_cover ρ j hI.isIrrPlus l he
  have hu (g : BinaryLinearThree.Group) (v : U.toSubmodule) :
      u (U.toRepresentation g v) = σI g (u v) := rfl
  let p : U.toRepresentation.IntertwiningMap BinaryLinearThree.W :=
    (p₀.toLinearMap.comp u.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      exact (congrArg p₀ (hu g v)).trans (LinearMap.congr_fun (p₀.isIntertwining' g) (u v)))
  have hp : IsCover p := by
    refine ⟨hp₀.1.comp u.surjective,?_,inside_commutator_top ρ j O hO hI.isIrrPlus hIO⟩
    intro v hv g
    apply u.injective
    rw [hu]
    exact hp₀.2.1 hv g
  let α := (MulAut.congr j)
    (K.normalizerMonoidHom ⟨t.val⁻¹,hI.normalizes (T.inv_mem t.property)⟩)
  let d := BinaryLinearThree.AutomorphismAction.naturalOuterEquiv α
    (moved_automorphism_outer ρ hI t j hne)
  have hrval (v : W.toSubmodule) : (r v : V) = ρ t.val⁻¹ v.val.val := by
    apply (ρ.apply_bijective t.val).1
    have hh := congrArg Subtype.val (c.apply_symm_apply (w v))
    change ρ t.val (r v).val = v.val.val at hh
    rw [hh]
    simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  have hr (g : BinaryLinearThree.Group) (v : W.toSubmodule) :
      r (W.toRepresentation g v) = σI (α g) (r v) := by
    apply Subtype.ext
    rw [hrval]
    change ρ t.val⁻¹ (ρ (j.symm g).val v.val.val) =
      ρ (j.symm (α g)).val (r v).val
    rw [hrval]
    have hg : (j.symm (α g)).val = t.val⁻¹ * (j.symm g).val * t.val := by
      simp only [α,MulAut.congr_apply,MulEquiv.trans_apply,j.symm_apply_apply,
        normalizerMonoidHom_apply_apply_coe,inv_inv]
    rw [hg]
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,mul_inv_cancel,mul_one]
  let q : W.toRepresentation.IntertwiningMap BinaryLinearThree.W.dual :=
    (d.toLinearEquiv.toLinearMap.comp (p₀.toLinearMap.comp r.toLinearMap)).intertwiningMap_of_isIntertwiningMap
      _ _ (by
        intro g v
        change d (p₀ (r (W.toRepresentation g v))) = BinaryLinearThree.W.dual g (d (p₀ (r v)))
        rw [hr,p₀.isIntertwining]
        exact LinearMap.congr_fun (d.isIntertwining' g) (p₀ (r v)))
  have hq : IsCover q := by
    refine ⟨d.toLinearEquiv.surjective.comp (hp₀.1.comp r.surjective),?_,
      inside_commutator_top ρ j O hO hJ hJO⟩
    intro v hv g
    apply r.injective
    rw [hr]
    apply hp₀.2.1
    exact d.toLinearEquiv.injective (hv.trans d.toLinearEquiv.map_zero.symm)
  have hint : I ⊓ J ≤ I ⊓ fixedSpace ρ K := by
    intro v hv
    refine ⟨hv.1,?_⟩
    apply (Submodule.Quotient.mk_eq_zero (fixedSpace ρ K)).mp
    have hh : (fixedSpace ρ K).mkQ v ∈
        I.map (fixedSpace ρ K).mkQ ⊓ J.map (fixedSpace ρ K).mkQ :=
      ⟨⟨v,hv.1,rfl⟩,⟨v,hv.2,rfl⟩⟩
    rwa [(hI.isIrrPlus.disjoint_quotientImages ρ hJ (Ne.symm hne)).eq_bot] at hh
  have hdim := (hI.isIrrPlus.finrank_of_linear_three_central_quotient ρ K j l he).1
  have hfin : Module.finrank (ZMod 2) ↥(I ⊓ J) ≤ 1 := by
    have hh := Submodule.finrank_mono hint
    have heq : Module.finrank (ZMod 2) ↥(I ⊓ fixedSpace ρ K) =
        Module.finrank (ZMod 2) ((fixedSpace ρ K).comap I.subtype) := by
      have hh := (Submodule.comapSubtypeEquivOfLe
        (inf_le_left : I ⊓ fixedSpace ρ K ≤ I)).finrank_eq
      have hh' : (I ⊓ fixedSpace ρ K).comap I.subtype =
          (fixedSpace ρ K).comap I.subtype := by
        ext v
        exact and_iff_right v.property
      rw [hh'] at hh
      exact hh.symm
    omega
  refine ⟨U,W,p,q,rfl,rfl,hp,hq,u.finrank_eq,
    w.finrank_eq.trans (finrank_map_action ρ I t.val),?_⟩
  change Module.finrank (ZMod 2) ↥(I.comap O.subtype ⊓ J.comap O.subtype) ≤ 1
  rw [←Submodule.comap_inf]
  exact (Submodule.comapSubtypeEquivOfLe (inf_le_left.trans hIO)).finrank_eq.le.trans hfin

/-- A homogeneous natural central-cover orbit with diagram movement and
quadratic ratio at most two has three-dimensional seeds. The paired-cover
obstruction excludes the nonsplit four-space without discarding its kernel. -/
theorem IsIrrPlusWith.finrank_three_of_small_orbit
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (hmoved : orbitSpan ρ T I ≠ I)
    (hsmall : quadraticRatio (invariantSubspace ρ K (orbitSpan ρ T I)
      (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2) :
    Module.finrank (ZMod 2) I = 3 ∧
      (fixedSpace ρ K).comap I.subtype = ⊥ ∧
      Module.finrank (ZMod 2) (orbitSpan ρ T I) = 6 := by
  obtain ⟨t,hne,hspan,_,_,_⟩ := hI.linear_three_moved_pair ρ j l he hmoved
  let O := orbitSpan ρ T I
  let hO := orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus
  let σ := (invariantSubspace ρ K O hO).toRepresentation
  let τ := markedAction ρ j O hO
  have hsmall' : quadraticRatio τ ≤ 2 :=
    (quadraticRatio_le_of_injective_equivariant σ τ j.toMonoidHom j.injective
      (LinearEquiv.refl _ _) (by
        intro k v
        change σ k v = σ (j.symm (j k)) v
        rw [j.symm_apply_apply])).trans hsmall
  obtain ⟨U,W,p,q,_,_,hp,hq,hdU,hdW,hi⟩ := hI.natural_dual_cover_pair ρ t j l he hne
  obtain ⟨_,hd,halt⟩ := hI.isIrrPlus.finrank_of_linear_three_central_quotient ρ K j l he
  have hd3 : Module.finrank (ZMod 2) I = 3 := halt.resolve_right (fun hd4 =>
    SLThreeCentralExtension.not_small_quadraticRatio_of_paired_covers τ U W p hp q hq
      (hdU.trans hd4) (hdW.trans hd4) hi hsmall')
  have hz : (fixedSpace ρ K).comap I.subtype = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  have hint : I ⊓ I.map (ρ t.val) = ⊥ := by
    apply bot_unique
    intro v hv
    have hc : v ∈ fixedSpace ρ K := by
      apply (Submodule.Quotient.mk_eq_zero (fixedSpace ρ K)).mp
      have hh : (fixedSpace ρ K).mkQ v ∈ I.map (fixedSpace ρ K).mkQ ⊓
          (I.map (ρ t.val)).map (fixedSpace ρ K).mkQ :=
        ⟨⟨v,hv.1,rfl⟩,⟨v,hv.2,rfl⟩⟩
      rwa [(hI.isIrrPlus.disjoint_quotientImages ρ
        (hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)) (Ne.symm hne)).eq_bot] at hh
    have hh : (⟨v,hv.1⟩ : I) ∈ (fixedSpace ρ K).comap I.subtype := hc
    rw [hz] at hh
    exact congrArg Subtype.val hh
  refine ⟨hd3,hz,?_⟩
  have hh := I.finrank_sup_add_finrank_inf_eq (I.map (ρ t.val))
  rw [hint,finrank_bot,add_zero,finrank_map_action,hd3] at hh
  rwa [hspan]

/-- After the cover obstruction, a moved homogeneous orbit is the direct
sum of its literal natural and dual seeds, with specified intertwining maps. -/
theorem IsIrrPlusWith.natural_dual_pair_of_small_orbit
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (hmoved : orbitSpan ρ T I ≠ I)
    (hsmall : quadraticRatio (invariantSubspace ρ K (orbitSpan ρ T I)
      (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2) :
    ∃ (t : T) (u : I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
      (w : I.map (ρ t.val) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) BinaryLinearThree.Vector),
      orbitSpan ρ T I = I ⊔ I.map (ρ t.val) ∧
      Disjoint I (I.map (ρ t.val)) ∧
      (∀ k v, u ((invariantSubspace ρ K I hI.invariant).toRepresentation k v) =
        BinaryLinearThree.W (j k) (u v)) ∧
      (∀ k v, w ((invariantSubspace ρ K (I.map (ρ t.val))
        (hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)).choose).toRepresentation k v) =
        BinaryLinearThree.W.dual (j k) (w v)) := by
  obtain ⟨hd3,hz,hd6⟩ := hI.finrank_three_of_small_orbit ρ j l he hmoved hsmall
  obtain ⟨t,hne,hspan,_,_,_⟩ := hI.linear_three_moved_pair ρ j l he hmoved
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

end Representation.BinaryOffender.Homogeneous
