module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OmegaResidualAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationCoveredAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
public import Theory.Representation.HexacodeAction.CoverComparison
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

/-!
# The covered natural section of the original augmentation module

Project the actual five-dimensional augmentation module onto its natural
section. The kernel is exactly C_V(L), and the preimage of the line through
the escaping omega vector is the original Sylow-fixed plane V₁. The invariant
alternating form supplies a compatible Sylow-stable hyperplane. Comparison
of central covers gives the hexacode marking over the prescribed quotient
map, rather than changing the action coordinates.

This constructs LocalAction.NaturalSetup with its permitted central fixed
kernel. CoveredPointResidual uses it to classify the literal point residuals;
the original module remains five-dimensional throughout.
Source: Aschbacher--Smith Notation 13.2.1 and 13.3.9, pp.877,887;
13.4.2, pp.896--897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The covered natural section is constructed from the original augmentation
map; its fixed kernel and literal Sylow-fixed plane are retained. -/
theorem covered_augmentation_natural_setup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    ∃ V₃ : Subgroup G, Nonempty (NaturalSetup L (T : Subgroup G) V
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) V₃) := by
  let := h.quasisimple
  let := D.elementary
  let X := L ⊔ (T : Subgroup G)
  let V₁ := V ⊓ omegaOneCenterAmbient (T : Subgroup G)
  have hn := normalizer_component_le_module_at h structural D m
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  have hXV : X ≤ normalizer (V : Set G) := hXN.trans hn
  obtain ⟨qN,hqN,hqNL,_⟩ := exists_core_normalizer_permutation D m hn
  let q := qN.comp (inclusion hXN)
  let f : V →* Multiplicative (natural (Fin 6)) :=
    ((coreToNatural (Fin 6)).toAddMonoidHom.toMultiplicative).comp m.coordinate.toMonoidHom
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v,hv⟩ := coreToNatural_surjective w.toAdd
    obtain ⟨u,hu⟩ := m.coordinate.surjective (Multiplicative.ofAdd v)
    refine ⟨u,?_⟩
    change Multiplicative.ofAdd (coreToNatural (Fin 6) (m.coordinate u).toAdd) = w
    rw [hu]
    exact congrArg Multiplicative.ofAdd hv
  have hk : f.ker = (centralizer (L : Set G)).comap V.subtype := by
    ext v
    rw [MonoidHom.mem_ker]
    change coreToNatural (Fin 6) (m.coordinate v).toAdd = 0 ↔ _
    have hkzero : coreToNatural (Fin 6) (m.coordinate v).toAdd = 0 ↔
        (m.coordinate v).toAdd.val ∈ constants (Fin 6) := by
      rw [←Subtype.val_inj]
      exact Submodule.Quotient.mk_eq_zero _
    rw [hkzero]
    exact (m.mem_fixed_iff v).symm
  have hact (g : X) (v : V) :
      (f (V.normalizerMonoidHom ⟨g.val,hXV g.property⟩ v)).toAdd =
        naturalRepresentation (Fin 6) (q g) (f v).toAdd := by
    change coreToNatural (Fin 6) (m.coordinate
      (V.normalizerMonoidHom ⟨g.val,hXV g.property⟩ v)).toAdd = _
    have he := hqN (inclusion hXN g) v
    change (m.coordinate (V.normalizerMonoidHom ⟨g.val,hXV g.property⟩ v)).toAdd =
      coreRepresentation (Fin 6) (q g) (m.coordinate v).toAdd at he
    rw [he]
    exact coreToNatural_equivariant _ _
  let w := (f z).toAdd
  have hw : w ≠ 0 := by
    intro he
    have hzker : z ∈ f.ker := he
    rw [hk] at hzker
    exact hzL hzker
  let P := Submodule.span (ZMod 2) {w}
  have hP : Module.finrank (ZMod 2) P = 1 := finrank_span_singleton hw
  have hline : V₁ = flagPreimage f P := by
    apply le_antisymm
    · intro v hv
      apply (mem_flagPreimage_iff f P ⟨v,hv.1⟩).mpr
      have he := first_fixed_plane_eq_at h structural D m z hz hzL
      have hpre : (V ⊓ centralizer (L : Set G)) ⊔ zpowers z.val ≤ flagPreimage f P := by
        apply sup_le
        · intro v hv
          apply (mem_flagPreimage_iff f P ⟨v,hv.1⟩).mpr
          have hh : f ⟨v,hv.1⟩ = 1 := by
            change (⟨v,hv.1⟩ : V) ∈ f.ker
            rw [hk]
            exact hv.2
          rw [hh]
          exact P.zero_mem
        · apply zpowers_le.mpr
          exact (mem_flagPreimage_iff f P z).mpr (Submodule.subset_span (Set.mem_singleton w))
      exact (mem_flagPreimage_iff f P ⟨v,hv.1⟩).mp (hpre (he ▸ hv))
    · intro v hv
      have hvV := flagPreimage_le f P hv
      let a : V := ⟨v,hvV⟩
      have ha : (f a).toAdd ∈ P := (mem_flagPreimage_iff f P a).mp hv
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp ha
      change v ∈ V ⊓ omegaOneCenterAmbient (T : Subgroup G)
      rw [first_fixed_plane_eq_at h structural D m z hz hzL]
      fin_cases c
      · change (0 : ZMod 2) • w = (f a).toAdd at hc
        have ha0 : a ∈ f.ker := by
          change f a = 1
          apply Multiplicative.toAdd.injective
          change (f a).toAdd = 0
          simpa only [zero_smul] using hc.symm
        rw [hk] at ha0
        exact mem_sup_left ⟨hvV,ha0⟩
      · change (1 : ZMod 2) • w = (f a).toAdd at hc
        have he : f a = f z := Multiplicative.toAdd.injective (by
          change (f a).toAdd = w
          simpa only [one_smul] using hc.symm)
        have hker : a*z⁻¹ ∈ f.ker := by
          rw [MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
        rw [hk] at hker
        have hh := ((V ⊓ centralizer (L : Set G)) ⊔ zpowers z.val).mul_mem
          (mem_sup_left ⟨(a*z⁻¹).property,hker⟩) (mem_sup_right (mem_zpowers z.val))
        simpa only [coe_mul,coe_inv,inv_mul_cancel_right] using hh
  have hTP : ∀ t : (T : Subgroup G), naturalRepresentation (Fin 6)
      (q (inclusion (show (T : Subgroup G) ≤ X from le_sup_right) t)) w = w := by
    intro t
    rw [←hact]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t.val t.property)
  have hPi : ∀ t : (T : Subgroup G),
      (q (inclusion (show (T : Subgroup G) ≤ X from le_sup_right) t)) ∈
        Representation.BinaryOffender.subspaceStabilizer (naturalRepresentation (Fin 6)) P := by
    intro t
    apply (mem_stabilizer_iff_map P _).mpr
    change (Submodule.span (ZMod 2) {w}).map _ = P
    rw [Submodule.map_span,Set.image_singleton,hTP]
  let H := form.orthogonal P
  have hH : Module.finrank (ZMod 2) H = 3 := by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even (Fin 6) (by decide),hP]
    rfl
  have hPH : P ≤ H := by
    intro a ha b hb
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨d,rfl⟩ := Submodule.mem_span_singleton.mp hb
    simp [form_alt w]
  let V₃ := flagPreimage f H
  have hV₃ : (T : Subgroup G) ≤ normalizer (V₃ : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht v hv
    let a : V := ⟨v,flagPreimage_le f H hv⟩
    let t' : X := ⟨t,mem_sup_right ht⟩
    have hg := stabilizer_le_orthogonal_stabilizer P (hPi ⟨t,ht⟩)
    have ha := (mem_flagPreimage_iff f H a).mp hv
    have hh := (hg (f a).toAdd).mpr ha
    change naturalRepresentation (Fin 6) (q t') (f a).toAdd ∈ H at hh
    rw [←hact t' a] at hh
    exact (mem_flagPreimage_iff f H _).mpr hh
  let cov : Covering (L ⧸ pCore 2 L) (alternatingGroup (Fin 6)) := {
    toMonoidHom := GLS3.Chapter5.alternatingQuotientHom (augmentationCentralQuotient D m)
    surjective := (augmentationCentralQuotient D m).surjective.comp (QuotientGroup.mk'_surjective _) }
  have hkc : Nat.card cov.toMonoidHom.ker = 3 := by
    have he : cov.toMonoidHom.ker = center (L ⧸ pCore 2 L) := by
      ext x
      simp [cov,GLS3.Chapter5.alternatingQuotientHom]
    rw [he,hc]
  obtain ⟨e,he⟩ := Representation.Hexacode.CoverComparison.exists_even_equiv_over_coordinate cov hkc
  refine ⟨V₃,⟨{
    cover := e
    normalizes_L := D.sylow_normalizes_component
    normalizes_V := hXV
    sylow := T.subtype le_sup_right
    sylow_eq := rfl
    elementary := inferInstance
    exponent_two := fun v => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val v.property)
    permutation := q
    cover_compatible := ?_
    naturalMap := f
    naturalMap_surjective := hf
    naturalMap_kernel := hk
    conjugation := hact
    point := P
    hyperplane := H
    point_dim := hP
    hyperplane_dim := hH
    compatible := hPH
    line_eq := hline
    seed_eq := rfl
    line_stable := ?_
    seed_stable := hV₃
    centralPreimage_centralizes := ?_ }⟩⟩
  · intro l
    have hh := congrArg (fun F : (L ⧸ pCore 2 L) →* alternatingGroup (Fin 6) =>
      F (QuotientGroup.mk' (pCore 2 L) l)) he
    change Atlas.Codes.hexEvenCoordinate (e (QuotientGroup.mk' (pCore 2 L) l)) =
      augmentationCentralQuotient D m (QuotientGroup.mk' (center (L ⧸ pCore 2 L))
        (QuotientGroup.mk' (pCore 2 L) l)) at hh
    rw [augmentationCentralQuotient_apply] at hh
    exact (hqNL l).trans (congrArg Subtype.val hh).symm
  · apply le_normalizer_iff.mpr
    intro t ht v hv
    have he : t*v*t⁻¹ = v := mul_inv_eq_iff_eq_mul.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp hv.2).2.2 t ht)
    exact he.symm ▸ hv
  · rintro _ ⟨l,hl,rfl⟩ v hv
    have hk : QuotientGroup.mk' (centralCore L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    have he := m.equivariant l ⟨v,hv⟩
    rw [hk,map_one] at he
    have hm : V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ ⟨v,hv⟩ = ⟨v,hv⟩ :=
      m.coordinate.injective (Multiplicative.toAdd.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hm)).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
