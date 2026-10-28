module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FourBlockFusion
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockContainment
public import Theory.GroupTheory.PResidual.NormalizedImageContainment

/-!
# Lifting the contrary-fusion permutation image

The original two-core normalizes L₁. A two-perfect subgroup of L whose
permutation image lies in the unordered four-block stabilizer therefore lies
in L₁: its image lies in A₄ × A₄, and two-perfectness lifts containment through
the two-group kernel. Equal orders then give equality. This needs no assumption
that the kernel normalizes the fused residual.

An arbitrary permutation conjugator can be corrected to be even, lifted to L,
and composed with the original point conjugator. The resulting L₁ alignment
feeds the checked preservation of the literal O₂(L₁T₄) and normalizer control.
For the fused image itself we construct its actual E₉ two-core quotient and
prove compatibility with the original quotient projection and both conjugators.

The final application selects the weight-four point and coordinates from the
original nontrivial C_V(L). It leaves the concrete S₈ block-containment step
explicit. That recognition, remaining fusion, HS/J₄ exclusions, weak closure,
splitting and fixed-space elimination stay with this owner. Neither 12.6.2 nor
12.6.23 is complete. Earlier invariance/TI retain qt-d-1222-source; final earlier
source discharge remains with qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
the contrary-fusion argument of 12.6.19, printed p.828.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Two-perfectness and order lift block containment through the original
Q-kernel. Only the original residual needs to be normalized by that kernel. -/
theorem SourceHypothesis.weight_four_residual_eq_of_image_le_stabilizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (B : Subgroup G) (hBL : B ≤ L) (hp : IsPPerfect 2 B)
    (hc : Nat.card (Lv L (v : G)) ≤ Nat.card B)
    (hi : (B.subgroupOf L).map
      ((alternatingGroup (Fin 8)).subtype.comp D.actorMap) ≤ FourBlockResidual.H) :
    B = Lv L (v : G) := by
  let f := (alternatingGroup (Fin 8)).subtype.comp D.actorMap
  let A := (Lv L (v : G)).subgroupOf L
  let B₀ := B.subgroupOf L
  have hp₀ : IsPPerfect 2 B₀ := hp.of_surjective
    (subgroupOfEquivOfLe hBL).symm.toMonoidHom (subgroupOfEquivOfLe hBL).symm.surjective
  have hpm : IsPPerfect 2 (B₀.map f) :=
    hp₀.of_surjective (f.subgroupMap B₀) (f.subgroupMap_surjective B₀)
  have hf : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ (alternatingGroup (Fin 8)).subtype_injective]
    exact D.actorMap_ker H.chosen H.source.quasisimple
  have hn : f.ker ≤ normalizer (A : Set L) := by
    rw [hf,←subgroupOf_normalizer_eq (Lv_le_L L (v : G))]
    intro x hx
    apply Mv_le_normalizer_Lv L (v : G)
    refine ⟨L.le_normalizer x.property,?_⟩
    have hx' : (x : G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hx
    rw [←H.centralizer_eq_core] at hx'
    have hc := hx'.2
    exact mem_centralizer_singleton_iff.mpr (hc (v : G) v.property).symm
  have hi' : B₀.map f ≤ A.map f := by
    rw [D.Lv_image_fourBlock H.chosen E hE v hv]
    exact FourBlockPoint.twoPerfect_le_residual_of_le_stabilizer _ hpm hi
  have hle := isPPerfect_le_of_map_le_of_kernel_normalizes f B₀ A hp₀
    (hf.symm ▸ pCore_isPGroup) hn hi'
  have hle' : B ≤ Lv L (v : G) := by
    have hh := map_mono (f := L.subtype) hle
    rwa [map_subgroupOf_eq_of_le hBL,map_subgroupOf_eq_of_le (Lv_le_L L _)] at hh
  exact eq_of_le_of_card_ge hle' hc

omit [IsElementaryAbelian 2 V] in
private theorem Lv_conjugation (l : L) (v : V) :
    (Lv L (v : G)).map (MulAut.conj (l : G)).toMonoidHom =
      Lv L ((l : G) * (v : G) * (l : G)⁻¹) := by
  have hL : L.map (MulAut.conj (l : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer l.property)
  rw [Lv,map_embedded_pResidual,CLv,map_inf _ _ _ (MulAut.conj (l : G)).injective,
    hL,Gv,map_pointCentralizer]
  rfl

/-- An actual permutation conjugacy into the four-block stabilizer lifts to
L-conjugacy of the original residual. The fused residual need not be
normalized by the original Q. -/
theorem SourceHypothesis.weight_four_residual_alignment_of_image
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (l : L) (w : V) (hw : (w : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (a : G) (hB : (Lv L (w : G)).map (MulAut.conj a).toMonoidHom ≤ L)
    (hi : ∃ s : alternatingGroup (Fin 8),
      ((((Lv L (w : G)).map (MulAut.conj a).toMonoidHom).subgroupOf L).map
        ((alternatingGroup (Fin 8)).subtype.comp D.actorMap)).map
          (MulAut.conj (s : Equiv.Perm (Fin 8))).toMonoidHom ≤ FourBlockResidual.H) :
    ∃ k : L, ((Lv L (w : G)).map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj (k : G)).toMonoidHom = Lv L (w : G) := by
  let B := (Lv L (w : G)).map (MulAut.conj a).toMonoidHom
  let f := (alternatingGroup (Fin 8)).subtype.comp D.actorMap
  obtain ⟨s,hs⟩ := hi
  obtain ⟨b,hb⟩ := D.actorMap_surjective s
  let c := (MulAut.conj (b : G)).toMonoidHom
  have hL : L.map c = L := mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer b.property)
  have hBc : B.map c ≤ L := (map_mono hB).trans_eq hL
  have hbmap : (B.map c).subgroupOf L =
      (B.subgroupOf L).map (MulAut.conj b).toMonoidHom := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hBc]
    symm
    have he : L.subtype.comp (MulAut.conj b).toMonoidHom = c.comp L.subtype := by
      ext x; rfl
    rw [map_map,he,←map_map,map_subgroupOf_eq_of_le hB]
  have him : ((B.map c).subgroupOf L).map f ≤ FourBlockResidual.H := by
    rw [hbmap,map_map]
    have he : f.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj (s : Equiv.Perm (Fin 8))).toMonoidHom.comp f := by
      apply MonoidHom.ext
      intro x
      change f (b*x*b⁻¹) = (s : Equiv.Perm (Fin 8))*f x*(s : Equiv.Perm (Fin 8))⁻¹
      simp only [map_mul,map_inv]
      rw [show f b = (s : Equiv.Perm (Fin 8)) from congrArg Subtype.val hb]
    rw [he,←map_map]
    exact hs
  have hp : IsPPerfect 2 (B.map c) :=
    ((isPPerfect_embedded_pResidual 2 (CLv L (w : G))).of_surjective
      ((Lv L (w : G)).equivMapOfInjective (MulAut.conj a).toMonoidHom
        (MulAut.conj a).injective).toMonoidHom
      ((Lv L (w : G)).equivMapOfInjective (MulAut.conj a).toMonoidHom
        (MulAut.conj a).injective).surjective).of_surjective
          (B.equivMapOfInjective c (MulAut.conj (b : G)).injective).toMonoidHom
          (B.equivMapOfInjective c (MulAut.conj (b : G)).injective).surjective
  have hvw : (Lv L (v : G)).map (MulAut.conj (l : G)).toMonoidHom = Lv L (w : G) := by
    rw [hw]
    exact Lv_conjugation l v
  have hc : Nat.card (Lv L (v : G)) ≤ Nat.card (B.map c) := by
    rw [card_map_of_injective (MulAut.conj (b : G)).injective]
    change Nat.card (Lv L (v : G)) ≤ Nat.card ((Lv L (w : G)).map (MulAut.conj a).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj a).injective,←hvw,
      card_map_of_injective (MulAut.conj (l : G)).injective]
  have heq := H.weight_four_residual_eq_of_image_le_stabilizer D E hE v hv
    (B.map c) hBc hp hc him
  refine ⟨l*b,?_⟩
  have he : (MulAut.conj ((l*b : L) : G)).toMonoidHom =
      (MulAut.conj (l : G)).toMonoidHom.comp c := by
    ext x
    simp [c,MulAut.conj_apply,mul_assoc]
  rw [he,←map_map]
  change (B.map c).map _ = _
  rw [heq,hvw]


private theorem weight_four_image_core_quotient
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (B : Subgroup G) (hBL : B ≤ L) (b : B ≃* Lv L (v : G)) :
    let f := (alternatingGroup (Fin 8)).subtype.comp D.actorMap
    let I := (B.subgroupOf L).map f
    IsPPerfect 2 I ∧ ∃ q : Star I ≃* FourBlockResidual.E9,
      ∀ x : B.subgroupOf L,
        q (QuotientGroup.mk' _ (f.subgroupMap (B.subgroupOf L) x)) =
          FourBlockResidual.quotientMap (D.fourBlockPointMap H.chosen E hE v hv
            (b (subgroupOfEquivOfLe hBL x))) := by
  dsimp only
  let f := (alternatingGroup (Fin 8)).subtype.comp D.actorMap
  let B₀ := B.subgroupOf L
  let I := B₀.map f
  let a : B₀ ≃* Lv L (v : G) := (subgroupOfEquivOfLe hBL).trans b
  have hp : IsPPerfect 2 B₀ := (isPPerfect_embedded_pResidual 2 (CLv L (v : G))).of_surjective
    a.symm.toMonoidHom a.symm.surjective
  have hk : IsPGroup 2 (f.subgroupMap B₀).ker := by
    rw [Subgroup.ker_subgroupMap]
    have hf : f.ker = pCore 2 L := by
      rw [MonoidHom.ker_comp_of_injective _ _ (alternatingGroup (Fin 8)).subtype_injective]
      exact D.actorMap_ker H.chosen H.source.quasisimple
    rw [hf]
    exact pCore_isPGroup.comap_subtype
  let ei := (f.subgroupMap B₀).pCoreQuotientEquiv (f.subgroupMap_surjective B₀) hk
  let ea := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let q := ei.symm.trans (ea.trans (H.fourBlockPointQuotientEquiv D E hE v hv))
  refine ⟨hp.of_surjective (f.subgroupMap B₀) (f.subgroupMap_surjective B₀),q,?_⟩
  intro x
  have hi : ei (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (f.subgroupMap B₀ x) := rfl
  change H.fourBlockPointQuotientEquiv D E hE v hv
    (ea (ei.symm (QuotientGroup.mk' _ (f.subgroupMap B₀ x)))) = _
  rw [←hi,ei.symm_apply_apply]
  exact H.fourBlockPointQuotientEquiv_mk D E hE v hv (a x)

/-- The original conjugators induce a literal E₉ quotient on the fused
permutation image. The displayed square keeps its quotient projection. -/
theorem SourceHypothesis.weight_four_fused_image_quotient
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (l : L) (w : V) (hw : (w : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (a : G) (hB : (Lv L (w : G)).map (MulAut.conj a).toMonoidHom ≤ L) :
    let B := (Lv L (w : G)).map (MulAut.conj a).toMonoidHom
    let f := (alternatingGroup (Fin 8)).subtype.comp D.actorMap
    let I := (B.subgroupOf L).map f
    ∃ b : Lv L (v : G) ≃* B,
      (∀ x, (b x : G) = a * ((l : G) * (x : G) * (l : G)⁻¹) * a⁻¹) ∧
      IsPPerfect 2 I ∧ ∃ q : Star I ≃* FourBlockResidual.E9,
        ∀ x : B.subgroupOf L,
          q (QuotientGroup.mk' _ (f.subgroupMap (B.subgroupOf L) x)) =
            FourBlockResidual.quotientMap (D.fourBlockPointMap H.chosen E hE v hv
              (b.symm (subgroupOfEquivOfLe hB x))) := by
  dsimp only
  have hvw : (Lv L (v : G)).map (MulAut.conj (l : G)).toMonoidHom = Lv L (w : G) := by
    rw [hw]
    exact Lv_conjugation l v
  let e := ((Lv L (v : G)).equivMapOfInjective (MulAut.conj (l : G)).toMonoidHom
    (MulAut.conj (l : G)).injective).trans (MulEquiv.subgroupCongr hvw)
  let b := e.trans ((Lv L (w : G)).equivMapOfInjective (MulAut.conj a).toMonoidHom
    (MulAut.conj a).injective)
  refine ⟨b,fun x => rfl,?_⟩
  exact weight_four_image_core_quotient H D E hE v hv _ hB b.symm

/-- The contrary-fusion conjugator lies in M once the literal fused action
image is placed in an unordered four-block stabilizer. -/
theorem SourceHypothesis.weight_four_conjugator_mem_of_image
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (l : L) (w : V) (hw : (w : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (a z : G) (ha : MulAut.conj a (w : G) = z) (hz : Gv z ≤ M L)
    (hS : (Tv T (w : G)).map (MulAut.conj a).toMonoidHom ≤ LT T L)
    (hi : ∃ s : Equiv.Perm (Fin 8),
      ((((Lv L (w : G)).map (MulAut.conj a).toMonoidHom).subgroupOf L).map
        ((alternatingGroup (Fin 8)).subtype.comp D.actorMap)).map
          (MulAut.conj s).toMonoidHom ≤ FourBlockResidual.H) :
    a ∈ M L ∧ z ∉ centralizer (L : Set G) := by
  let g : LT T L := inclusion le_sup_left l
  have hB := H.weight_four_fused_residual_le_component D E hE v hv g w hw a z ha hz
  have hc := H.weight_four_residual_alignment_of_image D E hE v hv l w hw a hB
    (FourBlockPoint.even_conjugator_of_conjugate_le _ hi)
  refine ⟨H.weight_four_conjugator_mem_of_residual_conjugate D hTV E hE v hv g w hw a hS hc,?_⟩
  rw [←ha]
  exact H.weight_four_no_central_fusion_of_residual_conjugate D hTV E hE v hv g w hw a hS hc

/-- The original source constructor now leaves only a concrete permutation
containment: no Q-normalization or ambient residual-conjugacy premise is needed.
All coordinates and the selected point come from the original fixed space. -/
theorem SourceHypothesis.exists_selected_weight_four_image_reduction
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    ∃ (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) (v : V),
      (∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u)) ∧
      (∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u)) ∧
      E (Additive.ofMul v) = FourBlockPoint.point ∧
      ∃ l : L, let w := conjugation L V H.chosen.normalizes l v
        Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
        (Tv T (w : G)).relIndex (T : Subgroup G) = 2 ∧
        ∀ (a z : G), MulAut.conj a (w : G) = z → Gv z ≤ M L →
          let I := (((Lv L (w : G)).map (MulAut.conj a).toMonoidHom).subgroupOf L).map
            ((alternatingGroup (Fin 8)).subtype.comp D.actorMap)
          IsPPerfect 2 I ∧ Nonempty (Star I ≃* FourBlockResidual.E9) ∧
          ((Tv T (w : G)).map (MulAut.conj a).toMonoidHom ≤ LT T L →
          (∃ s : Equiv.Perm (Fin 8),
            ((((Lv L (w : G)).map (MulAut.conj a).toMonoidHom).subgroupOf L).map
              ((alternatingGroup (Fin 8)).subtype.comp D.actorMap)).map
                (MulAut.conj s).toMonoidHom ≤ FourBlockResidual.H) →
          a ∈ M L ∧ z ∉ centralizer (L : Set G)) := by
  obtain ⟨E,v,hE,hproj,hv,l,hs,hi,_⟩ := H.exists_selected_weight_four_core D hTV hTI hz
  refine ⟨E,v,hE,hproj,hv,l,hs,hi,?_⟩
  intro a z ha hc
  let w := conjugation L V H.chosen.normalizes l v
  let g : LT T L := inclusion le_sup_left l
  have hB := H.weight_four_fused_residual_le_component D E hE v hv g w rfl a z ha hc
  obtain ⟨b,_,hp,q,_⟩ := H.weight_four_fused_image_quotient D E hE v hv l w rfl a hB
  refine ⟨hp,⟨q⟩,?_⟩
  intro hS him
  exact H.weight_four_conjugator_mem_of_image D hTV E hE v hv l _ rfl a z ha hc hS him

end CFSG.Quasithin.Chapter12.Section06
