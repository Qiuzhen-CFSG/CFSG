module
public import Theory.Representation.BinaryPairedTransvections.Exchange
public import Theory.Representation.BinaryPairedTransvections.Extraspecial
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Fields

/-!
# Paired transvections in the literal source-56 quotients

The natural-plus-dual model supplies the two remaining actor conclusions
of the source partner construction. Equivariant coordinates identify the
fixed subgroup of the original quotient action with a line. The original
order-two distinguished line is already fixed, so it is that entire fixed
subgroup without an additional coordinate marking.

An injective realization of the paired transvection group in the original
actor quotient supplies the extraspecial product and its elementary
subgroup. The image of the explicit center transvection identifies its
center with the original image of `V`.

The coordinate realization and center marking are the outputs of the
partner geometry; this module consumes them in the exact forms required
by `RecognitionFields.fixed_line` and `.extraspecial_product`.
Source: Aschbacher--Smith, original Lemma 15.3.56(6--7), printed p. 1148.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition Recognition.NormalReduction BinaryPairedTransvections
variable {G : Type*} [Group G] {Z ZS : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The literal source fixed subgroup is its distinguished line once its
linear action is the paired transvection action. -/
theorem paired_model_fixed_line
    (J : Subgroup (centralizerH Z))
    (e : Space Z ZS ≃ₗ[ZMod 2] PairedSpace E)
    (ρ : centralizerH Z →* BinaryLinear.GL (PairedSpace E))
    (hequiv : ∀ h : centralizerH Z, ∀ v : VectorQuotient Z ZS,
      e (Additive.ofMul (quotientAction Z ZS h v)) = ρ h (e (Additive.ofMul v)))
    (c : E) (hc : c ≠ 0) (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0) (hdc : d c = 0)
    (t : BinaryLinear.GL (PairedSpace E))
    (htc : t (c,0) = (0,d)) (htd : t (0,d) = (c,0))
    (hq : ∀ u, BinaryNaturalDual.quadratic (t u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (t (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (t (0,f)).2 = 0)
    (himage : J.map ρ = (centerGroup c).map pairedAction ⊔ zpowers t)
    (hcard : Nat.card (distinguishedLine Z ZS) = 2)
    (hfixed : letI := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
      distinguishedLine Z ZS ≤ FixedPoints.subgroup J (VectorQuotient Z ZS)) :
    let := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    FixedPoints.subgroup J (VectorQuotient Z ZS) = distinguishedLine Z ZS := by
  let := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
  have hexchange := centerGroup_conjugate_eq_axisGroup c hc d hd t hq hE hD htd
  have hmem (v : VectorQuotient Z ZS) :
      v ∈ FixedPoints.subgroup J (VectorQuotient Z ZS) ↔
      e (Additive.ofMul v) ∈ BinaryLinear.fixedSpace (J.map ρ) := by
    constructor
    · intro hv a ha
      obtain ⟨h,hh,rfl⟩ := ha
      rw [← hequiv]
      exact congrArg (fun w => e (Additive.ofMul w)) (hv ⟨h,hh⟩)
    · intro hv h
      apply Additive.ofMul.injective
      apply e.injective
      change e (Additive.ofMul (quotientAction Z ZS h.val v)) = _
      rw [hequiv]
      exact hv _ (mem_map_of_mem ρ h.property)
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : distinguishedLine Z ZS)).mp hcard
  have hz0 : e (Additive.ofMul (z : VectorQuotient Z ZS)) ≠ 0 := by
    intro he
    apply hz
    apply Subtype.ext
    apply Additive.ofMul.injective
    exact e.injective (he.trans e.map_zero.symm)
  have hzfix := (hmem _).mp (hfixed z.property)
  rw [himage] at hzfix
  have hmodel := partner_fixedSpace_eq_marked c hc d hd hdc t htc htd hexchange
    (e (Additive.ofMul z.val)) hz0 hzfix
  apply le_antisymm _ hfixed
  intro v hv
  have hvfix := (hmem v).mp hv
  rw [himage,hmodel] at hvfix
  rcases (BinaryTransvectionGroups.mem_centerLine_iff (e (Additive.ofMul z.val))
    (e (Additive.ofMul v))).mp hvfix with hzero | heq
  · have hv1 : v = 1 := Additive.ofMul.injective (e.injective (hzero.trans e.map_zero.symm))
    exact hv1 ▸ (distinguishedLine Z ZS).one_mem
  · have hvz : v = z.val := Additive.ofMul.injective (e.injective heq)
    exact hvz ▸ z.property

/-- The marked transvection in the paired actor, viewed in its generated group. -/
def pairedCenter (c : E) (d : Module.Dual (ZMod 2) E) (hdc : d c = 0) : pairGroup c d :=
  ⟨BinaryLinear.transvection c d hdc, mem_sup_left ⟨mem_top _, BinaryLinear.transvection_mem
    (Submodule.mem_span_singleton_self c) (by
      intro x hx
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [hdc])⟩⟩

/-- The extraspecial conclusion on the literal actor quotient, with its center
identified by the original marked transvection. -/
theorem paired_model_extraspecial_product [FiniteDimensional (ZMod 2) E]
    (V : Subgroup G) (c : E) (hc : c ≠ 0) (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0)
    (hdc : d c = 0) (s : ℕ) (hdim : Module.finrank (ZMod 2) E = s+2)
    (f : pairGroup c d →* ActorQuotient Z) (hf : Function.Injective f)
    (hcenter : zpowers (f (pairedCenter c d hdc)) = actorImage Z V) :
    0 < s → ∃ P : Subgroup (ActorQuotient Z), IsExtraspecial 2 P ∧
      ∃ X : Subgroup P, IsElementaryAbelian 2 X ∧ Nat.card X = 2^(s+1) ∧
        (center P).map P.subtype = actorImage Z V := by
  intro hs
  let e : pairGroup c d ≃* f.range := MonoidHom.ofInjective hf
  have he := IsExtraspecial.of_mulEquiv e (pairGroup_extraspecial c hc d hd hdc s hs hdim)
  obtain ⟨X,hX,hXcard⟩ := pairGroup_contains_elementary c hc d s hdim
  let := hX
  refine ⟨f.range,he,X.map e.toMonoidHom,IsElementaryAbelian.map e.toMonoidHom,?_,?_⟩
  · rw [card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hXcard
  · have hz : center (pairGroup c d) = zpowers (pairedCenter c d hdc) := by
      apply map_injective (pairGroup c d).subtype_injective
      rw [center_pairGroup c hc d hd hdc, MonoidHom.map_zpowers]
      rfl
    have hec : (center (pairGroup c d)).map e.toMonoidHom = center f.range := by
      ext v
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact (centerCongr e ⟨u,hu⟩).property
      · intro hv
        exact ⟨e.symm v,(centerCongr e.symm ⟨v,hv⟩).property,e.apply_symm_apply v⟩
    rw [← hec, hz, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact hcenter

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
