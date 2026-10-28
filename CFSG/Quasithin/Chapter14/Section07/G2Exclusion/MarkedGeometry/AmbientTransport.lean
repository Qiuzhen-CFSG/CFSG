module
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Assembly
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics

/-!
# Ambient transport of the marked pencil

Faithful inclusion of a local group preserves literal subgroup quotients,
marked subgroups, quotient preimages, and centralizer residuals. Applying
these comparisons to the proved 14.7.55 output supplies the ambient inputs
of 14.7.56. The order-six residual quotient, orbit, and commutator formula
are transported; the preimage span has order sixteen by the kernel count.

No ambient normality of the local subgroup is required. The residual is
O²(C_H(V₂)), and its embedding is identified with the relative centralizer
residual used by the local-action consumer.

Source application: Aschbacher–Smith, 14.7.55–56, printed p.1066.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.AmbientTransport
open Subgroup
open MarkedPencil MarkedPencil.Assembly MarkedPencil.SourceActions.ResidualAction
open LocalParabolics LocalParabolics.ThreeOffenderOrbit
open Atlas.G2 Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
variable {G K : Type*} [Group G] [Group K]

/-- Restricting a subgroup to U commutes with a faithful ambient inclusion. -/
theorem embedded_subgroupOf (j : K →* G) (hj : Function.Injective j)
    (X U : Subgroup K) :
    (X.subgroupOf U).map (U.equivMapOfInjective j hj).toMonoidHom =
      (X.map j).subgroupOf (U.map j) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y,hy,rfl⟩
  · intro hx
    obtain ⟨y,hy,he⟩ := hx
    obtain ⟨u,hu,hu'⟩ := x.property
    have huy : u = y := hj (hu'.trans he.symm)
    subst y
    exact ⟨⟨u,hu⟩,hy,Subtype.ext hu'⟩

/-- The canonical equivalence between the internal quotient and its literal
ambient realization. It is induced by the subgroup inclusion on representatives. -/
def quotientEmbedding (j : K →* G) (hj : Function.Injective j)
    (U Z : Subgroup K) [(Z.subgroupOf U).Normal]
    [((Z.map j).subgroupOf (U.map j)).Normal] :
    (U ⧸ Z.subgroupOf U) ≃* ((U.map j) ⧸ (Z.map j).subgroupOf (U.map j)) :=
  QuotientGroup.congr _ _ (U.equivMapOfInjective j hj) (embedded_subgroupOf j hj Z U)

/-- The quotient comparison uses the literal quotient maps. -/
theorem quotientEmbedding_apply (j : K →* G) (hj : Function.Injective j)
    (U Z : Subgroup K) [(Z.subgroupOf U).Normal]
    [((Z.map j).subgroupOf (U.map j)).Normal] (u : U) :
    quotientEmbedding j hj U Z (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' ((Z.map j).subgroupOf (U.map j))
        ⟨j u,mem_map_of_mem j u.property⟩ := rfl

/-- Every marked quotient subgroup, not just its cardinality, is preserved. -/
theorem quotientEmbedding_image (j : K →* G) (hj : Function.Injective j)
    (U Z X : Subgroup K) [(Z.subgroupOf U).Normal]
    [((Z.map j).subgroupOf (U.map j)).Normal] :
    ((X.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))).map
        (quotientEmbedding j hj U Z).toMonoidHom =
      ((X.map j).subgroupOf (U.map j)).map
        (QuotientGroup.mk' ((Z.map j).subgroupOf (U.map j))) := by
  rw [← embedded_subgroupOf j hj X U, map_map, map_map]
  rfl

/-- Literal preimages commute with the faithful ambient inclusion. -/
theorem quotientEmbedding_preimage (j : K →* G) (hj : Function.Injective j)
    (U Z : Subgroup K) [(Z.subgroupOf U).Normal]
    [((Z.map j).subgroupOf (U.map j)).Normal]
    (B : Subgroup (U ⧸ Z.subgroupOf U)) :
    ((B.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype).map j =
      ((B.map (quotientEmbedding j hj U Z).toMonoidHom).comap
        (QuotientGroup.mk' ((Z.map j).subgroupOf (U.map j)))).map (U.map j).subtype := by
  ext x
  constructor
  · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
    refine ⟨⟨j u,mem_map_of_mem j u.property⟩,?_,rfl⟩
    exact ⟨QuotientGroup.mk' (Z.subgroupOf U) u,hu,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨v,hv,hvu⟩ := u.property
    have heu : (⟨j v,mem_map_of_mem j hv⟩ : U.map j) = u := Subtype.ext hvu
    obtain ⟨q,hq,heq⟩ := hu
    have hqv : q = QuotientGroup.mk' (Z.subgroupOf U) ⟨v,hv⟩ := by
      apply (quotientEmbedding j hj U Z).injective
      exact heq.trans (congrArg (QuotientGroup.mk' _) heu.symm)
    refine ⟨v,⟨⟨v,hv⟩,?_,rfl⟩,hvu⟩
    change QuotientGroup.mk' (Z.subgroupOf U) ⟨v,hv⟩ ∈ B
    rwa [← hqv]

/-- The residual computed internally in H is the relative centralizer
residual in G, after inclusion. No normality in G is asserted. -/
theorem residual_map [Finite G] (H : Subgroup G) (V₂ : Subgroup H) :
    (sourceResidual V₂).map H.subtype = localResidual H (V₂.map H.subtype) := by
  have hc : (centralizer (V₂ : Set H)).map H.subtype =
      H ⊓ centralizer (V₂.map H.subtype : Set G) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.property,?_⟩
      rintro _ ⟨v,hv,rfl⟩
      exact congrArg Subtype.val (hy v hv)
    · rintro ⟨hx,hc⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      intro v hv
      exact Subtype.ext (hc v (mem_map_of_mem H.subtype hv))
  unfold sourceResidual localResidual
  rw [map_embedded_pResidual, hc]

/-- The S₃ quotient of YT is unchanged by faithful inclusion into G. -/
theorem residual_quotient_map [Finite K] (j : K →* G) (hj : Function.Injective j)
    (Y T : Subgroup K)
    (he : Nonempty (((Y ⊔ T : Subgroup K) ⧸ pCore 2 (Y ⊔ T : Subgroup K)) ≃*
      Equiv.Perm (Fin 3))) :
    Nonempty (((Y.map j ⊔ T.map j : Subgroup G) ⧸
      pCore 2 (Y.map j ⊔ T.map j : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let e := ((Y ⊔ T).equivMapOfInjective j hj).trans
    (MulEquiv.subgroupCongr (map_sup Y T j))
  exact he.map (fun f => (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans f)


/-- The geometric and subgroup-containment descriptions of the marked pencil agree. -/
theorem markedPencil_eq {Q : Type*} [Group Q] (geom : QuotientGeometry Q)
    (p : SingularPoints (ZMod 2)) : markedPencil geom p = quotientPencil geom (geom.point p) := by
  ext B
  constructor
  · rintro ⟨L,hL,rfl⟩
    exact ⟨⟨L,rfl⟩,(geom.incidence p L).mp hL⟩
  · rintro ⟨⟨L,rfl⟩,hL⟩
    exact ⟨L,(geom.incidence p L).mpr hL,rfl⟩

/-- Both source notations for the pencil span use the same literal preimage. -/
theorem pencilSpanPreimage_eq (U Z : Subgroup G) [(Z.subgroupOf U).Normal]
    (geom : QuotientGeometry (U ⧸ Z.subgroupOf U)) (p : SingularPoints (ZMod 2)) :
    pencilSpanPreimage U Z geom p =
      ((quotientPencilSpan geom (geom.point p)).comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype := by
  unfold pencilSpanPreimage
  rw [markedPencil_eq]
  rfl

variable {D : Type*} [Group D]

/-- The quotient action restricted to the ambient image of the source residual. -/
def residualAction (H : Subgroup G) (V₂ : Subgroup H)
    {Q : Type*} [Group Q] (τ : H →* MulAut Q) :
    ((sourceResidual V₂).map H.subtype) →* MulAut Q :=
  τ.comp ((sourceResidual V₂).subtype.comp
    ((sourceResidual V₂).equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom)

/-- The marked-pencil information needed by 14.7.56, in the ambient literal
quotient. The record is an output of transport of the proved 14.7.55 calculations. -/
structure AmbientPencilConclusions
    (U Z V V₂ Y T : Subgroup G) [(Z.subgroupOf U).Normal]
    (m : BinaryG2Module) (E : Multiplicative m.Space ≃* (U ⧸ Z.subgroupOf U))
    (τ : Y →* MulAut (U ⧸ Z.subgroupOf U)) (p : SingularPoints (ZMod 2)) : Prop where
  point : (transportGeometry m.singularMap.geometry E).point p =
    (V₂.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))
  line : ∃ L : ZeroProductLine (ZMod 2),
    (V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
      (transportGeometry m.singularMap.geometry E).line L ∧
    (∀ y : Y, ((transportGeometry m.singularMap.geometry E).line L).map
      (τ y).toMonoidHom ∈ markedPencil (transportGeometry m.singularMap.geometry E) p) ∧
    (∀ B ∈ markedPencil (transportGeometry m.singularMap.geometry E) p,
      ∃ y : Y, ((transportGeometry m.singularMap.geometry E).line L).map
        (τ y).toMonoidHom = B)
  span_card : Nat.card (pencilSpanPreimage U Z (transportGeometry m.singularMap.geometry E) p) = 16
  commutator :
    ((⁅pencilSpanPreimage U Z (transportGeometry m.singularMap.geometry E) p,Y⁆).subgroupOf U).map
        (QuotientGroup.mk' (Z.subgroupOf U)) =
      ((pencilSpanPreimage U Z (transportGeometry m.singularMap.geometry E) p).subgroupOf U).map
        (QuotientGroup.mk' (Z.subgroupOf U))
  residual_quotient : Nonempty (((Y ⊔ T : Subgroup G) ⧸ pCore 2 (Y ⊔ T : Subgroup G)) ≃*
    Equiv.Perm (Fin 3))

/-- Transport the marked line, the Y orbit, the order of the lifted span,
the literal commutator formula and the S₃ quotient through H ↪ G. -/
theorem source_ambient_pencil [Finite G]
    (H : Subgroup G) (U Z V₂ V : Subgroup H) [U.Normal] [(Z.subgroupOf U).Normal]
    [((Z.map H.subtype).subgroupOf (U.map H.subtype)).Normal]
    [MulDistribMulAction D (U ⧸ Z.subgroupOf U)]
    (hZU : Z ≤ U) (hZ : Nat.card Z = 2)
    (m : BinaryG2Module) (e : Multiplicative m.Space ≃* (U ⧸ Z.subgroupOf U))
    (π : H →* D) (i : D →* Model (ZMod 2)) (T : Sylow 2 H)
    (p : SingularPoints (ZMod 2))
    (s : SourceConclusions U Z V₂ V m.action m.singularMap e π i T p)
    (hact : ∀ (h : H) (u : U), m.action (i (π h))
        (e.symm (QuotientGroup.mk' (Z.subgroupOf U) u)).toAdd =
      (e.symm (QuotientGroup.mk' (Z.subgroupOf U)
        ⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩)).toAdd)
    (τ : H →* MulAut ((U.map H.subtype) ⧸ (Z.map H.subtype).subgroupOf (U.map H.subtype)))
    (hτ : ∀ h q, τ h (quotientEmbedding H.subtype H.subtype_injective U Z q) =
      quotientEmbedding H.subtype H.subtype_injective U Z
        (quotientActor m.action e (i (π h)) q)) :
    AmbientPencilConclusions (U.map H.subtype) (Z.map H.subtype) (V.map H.subtype)
      (V₂.map H.subtype) ((sourceResidual V₂).map H.subtype) ((T : Subgroup H).map H.subtype)
      m (e.trans (quotientEmbedding H.subtype H.subtype_injective U Z))
      (residualAction H V₂ τ) p := by
  let θ := quotientEmbedding H.subtype H.subtype_injective U Z
  let E := e.trans θ
  let g₀ := transportGeometry m.singularMap.geometry e
  let g₁ := transportGeometry m.singularMap.geometry E
  let Y := sourceResidual V₂
  let eY := Y.equivMapOfInjective H.subtype H.subtype_injective
  let S := quotientPencilSpan g₀ (g₀.point p)
  have hpoint (r : SingularPoints (ZMod 2)) : (g₀.point r).map θ.toMonoidHom = g₁.point r := by
    exact map_map _ _ _
  have hline (L : ZeroProductLine (ZMod 2)) : (g₀.line L).map θ.toMonoidHom = g₁.line L := by
    exact map_map _ _ _
  have hspan : S.map θ.toMonoidHom = quotientPencilSpan g₁ (g₁.point p) := by
    dsimp only [S]
    rw [quotientPencilSpan_eq, quotientPencilSpan_eq, map_map]
    rfl
  have hp : g₁.point p = ((V₂.map H.subtype).subgroupOf (U.map H.subtype)).map
      (QuotientGroup.mk' ((Z.map H.subtype).subgroupOf (U.map H.subtype))) := by
    rw [← hpoint, s.point]
    exact quotientEmbedding_image _ _ _ _ _
  obtain ⟨L,hL,hpL⟩ := s.line
  have hL' : ((V.map H.subtype).subgroupOf (U.map H.subtype)).map
      (QuotientGroup.mk' ((Z.map H.subtype).subgroupOf (U.map H.subtype))) = g₁.line L := by
    rw [← quotientEmbedding_image H.subtype H.subtype_injective U Z V, hL, hline]
  have hmap (y : Y) (B : Subgroup (U ⧸ Z.subgroupOf U)) :
      (B.map θ.toMonoidHom).map ((residualAction H V₂ τ) (eY y)).toMonoidHom =
        (B.map (quotientActor m.action e (i (π y)))).map θ.toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext q
    change τ (eY.symm (eY y)) (θ q) = θ (quotientActor m.action e (i (π y)) q)
    rw [eY.symm_apply_apply]
    exact hτ y q
  have hmem : g₀.line L ∈ quotientPencil g₀ ((V₂.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))) := by
    exact ⟨⟨L,rfl⟩,s.point ▸ (g₀.incidence p L).mp hpL⟩
  have hpre : ((S.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype).map H.subtype =
      pencilSpanPreimage (U.map H.subtype) (Z.map H.subtype) g₁ p := by
    rw [quotientEmbedding_preimage H.subtype H.subtype_injective, hspan, pencilSpanPreimage_eq]
  have hbasic := lift_support_basic (U.map H.subtype) (Z.map H.subtype)
    (map_mono hZU) (quotientPencilSpan g₁ (g₁.point p))
  have hS : Nat.card S = 8 := by
    dsimp only [S]
    rw [s.point]
    exact s.span_card
  have hcomm :
      ((⁅pencilSpanPreimage (U.map H.subtype) (Z.map H.subtype) g₁ p,
        Y.map H.subtype⁆).subgroupOf (U.map H.subtype)).map
        (QuotientGroup.mk' ((Z.map H.subtype).subgroupOf (U.map H.subtype))) =
        quotientPencilSpan g₁ (g₁.point p) := by
    rw [← hpre, ← map_commutator, ← quotientEmbedding_image H.subtype H.subtype_injective U Z _, hspan.symm]
    apply congrArg (fun B : Subgroup (U ⧸ Z.subgroupOf U) => B.map θ.toMonoidHom)
    have hc := s.residual_commutator
    dsimp only at hc
    rw [← s.point] at hc
    exact hc
  have hcomm' := hcomm.trans hbasic.2.2.2.symm
  rw [← pencilSpanPreimage_eq] at hcomm'
  refine ⟨hp,⟨L,hL',?_,?_⟩,?_,hcomm',?_⟩
  · intro y
    obtain ⟨y,rfl⟩ := eY.surjective y
    have hn : (y : H) ∈ normalizer (V₂ : Set H) :=
      centralizer_le_normalizer _ (map_subtype_le _ y.property)
    have hy := source_normalizer_point U Z V₂ m.singularMap m.action m.equivariant
      (i.comp π) e hact p s.point.symm y hn
    rw [← hline, hmap, quotientActor_line m.singularMap m.action m.equivariant, hline]
    refine ⟨i (π y) • L,?_,rfl⟩
    have hh := (pointOnLine_smul_iff (i (π y)) p L).mpr hpL
    simp only [MonoidHom.comp_apply] at hy
    rwa [hy] at hh
  · rintro B ⟨M,hM,rfl⟩
    have hm : g₀.line M ∈ quotientPencil g₀ ((V₂.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))) := by
      refine ⟨⟨M,rfl⟩,?_⟩
      rw [← s.point]
      exact (g₀.incidence _ _).mp hM
    obtain ⟨y,hy,he⟩ := s.residual_transitive _ hmem _ hm
    refine ⟨eY ⟨y,hy⟩,?_⟩
    rw [← hline, hmap, he, hline]
  · rw [pencilSpanPreimage_eq]
    change Nat.card (((quotientPencilSpan g₁ (g₁.point p)).comap
      (QuotientGroup.mk' ((Z.map H.subtype).subgroupOf (U.map H.subtype)))).map
      (U.map H.subtype).subtype) = 16
    rw [hbasic.2.2.1, ← hspan, card_map_of_injective (f := θ.toMonoidHom) θ.injective, hS,
      card_map_of_injective H.subtype_injective, hZ]
  · exact residual_quotient_map H.subtype H.subtype_injective Y T s.residual_quotient

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.AmbientTransport
