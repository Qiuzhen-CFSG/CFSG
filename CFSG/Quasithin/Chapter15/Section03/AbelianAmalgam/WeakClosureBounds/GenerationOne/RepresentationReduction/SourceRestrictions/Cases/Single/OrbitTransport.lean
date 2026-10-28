module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.ModuleIdentifications

/-!
# Constructing the central quotient of a two-constituent orbit

Right conjugation uses t⁻¹. Its induced map on central quotients
intertwines with conjugation by t on the actor. A direct sum of the
quotient images gives an equivariant product identification of the literal
orbit central quotient. Distinct Irr⁺ sections have disjoint images, and
full commutator generation lifts the image equality to the actual sections.
The constituent marking is preserved in the product identification.

These are transport lemmas. Existence of the natural constituent, the
F.9.18 sum clause, and movement of the standard parabolics are not asserted.
Homogeneity also gives I=I_T once the actual conjugate images have been
proved equivalent.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.1.40--42,
printed pp.31--32; F.9.18(4)(iii), pp.325--326; 15.3.65, p.1152.
-/

public section

open Representation Representation.BinaryOffender Subgroup
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
variable {D E V X : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D V)

private theorem action_injective (t : D) : Function.Injective (ρ t) := by
  intro x y h
  have he := congrArg (ρ t⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply] using he

noncomputable def rightConjugateSectionEquiv (I : Submodule (ZMod 2) V) (t : D) :
    I ≃ₗ[ZMod 2] rightConjugate ρ I t :=
  Submodule.equivMapOfInjective (ρ t⁻¹) (action_injective ρ t⁻¹) I

private theorem conjugate_fixed_subspace (K : Subgroup D)
    (I : Submodule (ZMod 2) V) (t : D) (ht : t ∈ normalizer (K : Set D)) :
    ((fixedSpace ρ K).comap I.subtype).map
      (rightConjugateSectionEquiv ρ I t).toLinearMap =
    (fixedSpace ρ K).comap (rightConjugate ρ I t).subtype := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ((normalizer_le_stabilizer_fixedSpace ρ K
      ((normalizer (K : Set D)).inv_mem ht)) w).2 hw
  · intro hv
    obtain ⟨w, rfl⟩ := (rightConjugateSectionEquiv ρ I t).surjective v
    refine ⟨w, ?_, rfl⟩
    exact ((normalizer_le_stabilizer_fixedSpace ρ K
      ((normalizer (K : Set D)).inv_mem ht)) w).1 hv

noncomputable def rightConjugateCentralEquiv (K : Subgroup D)
    (I : Submodule (ZMod 2) V) (t : D) (ht : t ∈ normalizer (K : Set D)) :
    centralQuotient ρ K I ≃ₗ[ZMod 2] centralQuotient ρ K (rightConjugate ρ I t) :=
  Submodule.Quotient.equiv _ _ (rightConjugateSectionEquiv ρ I t)
    (conjugate_fixed_subspace ρ K I t ht)

theorem rightConjugateCentralEquiv_equivariant (K : Subgroup D)
    (I : Submodule (ZMod 2) V) (t : D) (ht : t ∈ normalizer (K : Set D))
    (hI : K ≤ subspaceStabilizer ρ I)
    (hJ : K ≤ subspaceStabilizer ρ (rightConjugate ρ I t))
    (g : K) (v : centralQuotient ρ K I) :
    rightConjugateCentralEquiv ρ K I t ht
      (centralQuotientRepresentation ρ K I hI (K.normalizerMonoidHom ⟨t, ht⟩ g) v) =
    centralQuotientRepresentation ρ K (rightConjugate ρ I t) hJ g
      (rightConjugateCentralEquiv ρ K I t ht v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    change ρ t⁻¹ (ρ (t * g * t⁻¹) v) = ρ g (ρ t⁻¹ v)
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left, mul_assoc]

noncomputable def rightConjugateIdentification {K : Subgroup D}
    {I : Submodule (ZMod 2) V} {hI : K ≤ subspaceStabilizer ρ I}
    {σ : Representation (ZMod 2) E X}
    (d : CentralQuotientIdentification ρ K I hI σ)
    (t : D) (ht : t ∈ normalizer (K : Set D))
    (hJ : K ≤ subspaceStabilizer ρ (rightConjugate ρ I t)) :
    CentralQuotientIdentification ρ K (rightConjugate ρ I t) hJ
      (σ.comp (MulAut.congr d.groupEquiv (K.normalizerMonoidHom ⟨t, ht⟩)).toMonoidHom) where
  groupEquiv := d.groupEquiv
  linearEquiv := (rightConjugateCentralEquiv ρ K I t ht).symm.trans d.linearEquiv
  equivariant g v := by
    let e := rightConjugateCentralEquiv ρ K I t ht
    have he : e.symm (centralQuotientRepresentation ρ K (rightConjugate ρ I t) hJ g v) =
        centralQuotientRepresentation ρ K I hI (K.normalizerMonoidHom ⟨t, ht⟩ g) (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply, rightConjugateCentralEquiv_equivariant ρ K I t ht hI hJ,
        e.apply_symm_apply]
    change d.linearEquiv (e.symm _) = _
    rw [he, d.equivariant]
    simp [MulAut.congr, e]


private def sumMap {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (I J W : Submodule (ZMod 2) U) (h : I ⊔ J = W) :
    I × J →ₗ[ZMod 2] W :=
  (I.subtype.coprod J.subtype).codRestrict W (fun v =>
    h ▸ Submodule.mem_sup.mpr ⟨v.1, v.1.property, v.2, v.2.property, rfl⟩)

private theorem sumMap_bijective {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (I J W : Submodule (ZMod 2) U) (h : I ⊔ J = W) (hd : Disjoint I J) :
    Function.Bijective (sumMap I J W h) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨x, y⟩ he
    have he' : (x : U) + y = 0 := congrArg Subtype.val he
    have hx : (x : U) ∈ I ⊓ J := ⟨x.property, by
      rw [eq_neg_of_add_eq_zero_left he']
      exact J.neg_mem y.property⟩
    rw [hd.eq_bot, Submodule.mem_bot] at hx
    have hy : (y : U) = 0 := by simpa [hx] using he'
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  · rintro ⟨w, hw⟩
    rw [← h] at hw
    obtain ⟨i, hi, j, hj, he⟩ := Submodule.mem_sup.mp hw
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), Subtype.ext he⟩

private noncomputable def sumEquiv {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (I J W : Submodule (ZMod 2) U) (h : I ⊔ J = W) (hd : Disjoint I J) :
    (I × J) ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofBijective (sumMap I J W h) (sumMap_bijective I J W h hd)

noncomputable def centralPairEquiv (K : Subgroup D)
    (I J W : Submodule (ZMod 2) V)
    (h : I.map (fixedSpace ρ K).mkQ ⊔ J.map (fixedSpace ρ K).mkQ =
      W.map (fixedSpace ρ K).mkQ)
    (hd : Disjoint (I.map (fixedSpace ρ K).mkQ) (J.map (fixedSpace ρ K).mkQ)) :
    (centralQuotient ρ K I × centralQuotient ρ K J) ≃ₗ[ZMod 2] centralQuotient ρ K W :=
  ((LinearEquiv.prodCongr (centralQuotientImageEquiv ρ K I) (centralQuotientImageEquiv ρ K J)).trans
    (sumEquiv _ _ _ h hd)).trans (centralQuotientImageEquiv ρ K W).symm

theorem centralPairEquiv_equivariant (K : Subgroup D)
    (I J W : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I) (hJ : K ≤ subspaceStabilizer ρ J)
    (hW : K ≤ subspaceStabilizer ρ W)
    (h : I.map (fixedSpace ρ K).mkQ ⊔ J.map (fixedSpace ρ K).mkQ =
      W.map (fixedSpace ρ K).mkQ)
    (hd : Disjoint (I.map (fixedSpace ρ K).mkQ) (J.map (fixedSpace ρ K).mkQ))
    (g : K) (v : centralQuotient ρ K I × centralQuotient ρ K J) :
    centralPairEquiv ρ K I J W h hd
      (centralQuotientRepresentation ρ K I hI g v.1,
        centralQuotientRepresentation ρ K J hJ g v.2) =
      centralQuotientRepresentation ρ K W hW g (centralPairEquiv ρ K I J W h hd v) := by
  apply (centralQuotientImageEquiv ρ K W).injective
  rw [centralQuotientImageEquiv_equivariant]
  change (centralQuotientImageEquiv ρ K W) ((centralQuotientImageEquiv ρ K W).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change ((centralQuotientImageEquiv ρ K I) (_) : V ⧸ fixedSpace ρ K) +
    ((centralQuotientImageEquiv ρ K J) (_) : V ⧸ fixedSpace ρ K) =
      fixedQuotientRepresentation ρ K g
        (((centralQuotientImageEquiv ρ K W) ((centralQuotientImageEquiv ρ K W).symm _)) :
          V ⧸ fixedSpace ρ K)
  rw [LinearEquiv.apply_symm_apply]
  change _ = fixedQuotientRepresentation ρ K g
    ((centralQuotientImageEquiv ρ K I v.1 : V ⧸ fixedSpace ρ K) +
      (centralQuotientImageEquiv ρ K J v.2 : V ⧸ fixedSpace ρ K))
  rw [map_add, centralQuotientImageEquiv_equivariant, centralQuotientImageEquiv_equivariant]
  rfl

noncomputable def centralPairIdentification {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    {K : Subgroup D} {I J W : Submodule (ZMod 2) V}
    {hI : K ≤ subspaceStabilizer ρ I} {hJ : K ≤ subspaceStabilizer ρ J}
    (hW : K ≤ subspaceStabilizer ρ W)
    {σ : Representation (ZMod 2) E X} {τ : Representation (ZMod 2) E Y}
    (dI : CentralQuotientIdentification ρ K I hI σ)
    (dJ : CentralQuotientIdentification ρ K J hJ τ)
    (hg : dJ.groupEquiv = dI.groupEquiv)
    (h : I.map (fixedSpace ρ K).mkQ ⊔ J.map (fixedSpace ρ K).mkQ =
      W.map (fixedSpace ρ K).mkQ)
    (hd : Disjoint (I.map (fixedSpace ρ K).mkQ) (J.map (fixedSpace ρ K).mkQ)) :
    CentralQuotientIdentification ρ K W hW (σ.prod τ) where
  groupEquiv := dI.groupEquiv
  linearEquiv := (centralPairEquiv ρ K I J W h hd).symm.trans
    (LinearEquiv.prodCongr dI.linearEquiv dJ.linearEquiv)
  equivariant g v := by
    let e := centralPairEquiv ρ K I J W h hd
    obtain ⟨w, rfl⟩ := e.surjective v
    have he := centralPairEquiv_equivariant ρ K I J W hI hJ hW h hd g w
    change (dI.linearEquiv (e.symm (_)).1, dJ.linearEquiv (e.symm (_)).2) = _
    rw [← he, e.symm_apply_apply]
    change (_, _) = (σ (dI.groupEquiv g) (dI.linearEquiv (e.symm (e w)).1),
      τ (dI.groupEquiv g) (dJ.linearEquiv (e.symm (e w)).2))
    rw [e.symm_apply_apply, dI.equivariant, dJ.equivariant, hg]


/-- The direct-sum clause in the quotient and one constituent identification
construct the complete orbit identification, with the actual t-induced twist. -/
noncomputable def orbitPairIdentification {K T : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K T I)
    {σ : Representation (ZMod 2) E X}
    (d : CentralQuotientIdentification ρ K I hI.invariant σ)
    (t : D) (ht : t ∈ T) (hne : I ≠ rightConjugate ρ I t)
    (hspan : (orbitSpan ρ T I).map (fixedSpace ρ K).mkQ =
      (I ⊔ rightConjugate ρ I t).map (fixedSpace ρ K).mkQ) :
    CentralQuotientIdentification ρ K (orbitSpan ρ T I)
      (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)
      (σ.prod (σ.comp (MulAut.congr d.groupEquiv
        (K.normalizerMonoidHom ⟨t, hI.normalizes ht⟩)).toMonoidHom)) := by
  let hJ := (hI.isIrrPlus.map_normalizer ρ (hI.normalizes (T.inv_mem ht))).choose
  let dJ := rightConjugateIdentification ρ d t (hI.normalizes ht) hJ
  apply centralPairIdentification ρ _ d dJ rfl
  · rw [← Submodule.map_sup]
    exact hspan.symm
  · exact hI.isIrrPlus.disjoint_quotientImages ρ
      (hI.isIrrPlus.map_normalizer ρ (hI.normalizes (T.inv_mem ht))) hne

/-- The orbit model uses exactly the constituent's group marking. -/
theorem orbitPairIdentification_groupEquiv {K T : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K T I)
    {σ : Representation (ZMod 2) E X}
    (d : CentralQuotientIdentification ρ K I hI.invariant σ)
    (t : D) (ht : t ∈ T) (hne : I ≠ rightConjugate ρ I t)
    (hspan : (orbitSpan ρ T I).map (fixedSpace ρ K).mkQ =
      (I ⊔ rightConjugate ρ I t).map (fixedSpace ρ K).mkQ) :
    (orbitPairIdentification ρ hI d t ht hne hspan).groupEquiv = d.groupEquiv := (rfl)

/-- Homogeneity turns equivalence of the actual conjugate quotient images
into equality I=I_T. The model theorem must supply these intertwiners. -/
theorem orbitSpan_eq_of_sameModule {K T : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K T I)
    (he : ∀ t : T, SameModule (quotientImage ρ K I hI.invariant)
      (quotientImage ρ K (I.map (ρ t))
        (hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)).choose)) :
    orbitSpan ρ T I = I := by
  apply le_antisymm _ (le_orbitSpan ρ T I)
  apply iSup_le
  intro t
  exact (hI.eq_of_isomorphic_conjugate ρ t (he t)).le

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
