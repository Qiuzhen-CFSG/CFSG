module
public import Theory.Representation.PSL3Two.LineRadical
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SourceContext
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.MarkedH65
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedTransitivity
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Conjugacy
/-!
# The binary whole quotient forces a source transvection

The original residual moves the two-dimensional seed transitively. This
constructs a compatible Sylow and line-parabolic marking and proves the
five H.6.5 alternatives on the literal U_H/V₁ action. If the action had no
transvections, the earlier source geometry would select a quadratic critical
subgroup of rank greater than one and conjugate it into the line radical.
That subgroup fills the radical. The concrete core and Steinberg obstructions
then leave the natural module, whose explicit transvection is a contradiction.

Every action, cyclic seed, parabolic marking, module classification, critical
selection and rank transport is constructed here from SourceContext. The
result concerns H/O₂(H), not the allowed component quotient K/O₂(K).
The field-sieve owner qt-d-138-fields-source retains the transvection branch,
the remaining field and cover rows, and unrestricted-overgroup assembly;
qt-d-1381-source supplies the preceding original SourceContext.
Source: Aschbacher–Smith, 13.8.19, printed p.953, using H.6.5 and 13.8.18(4).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open Geometry Geometry.ParabolicMarking Geometry.CoveredProduct.ResidualPlacement
open AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [Finite G] in
private theorem seedSpace_eq_sectionImage :
    seedSpace H V₃ V₁ = TransvectionParabolic.Marking.sectionImage H V₃ V₁ V₃ := by
  ext v
  rw [mem_seedSpace_iff]
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨⟨w,le_conjugateSpanBy V₃ H w.property⟩,w.property,rfl⟩
  · rintro ⟨w,hw,he⟩
    exact ⟨⟨w,hw⟩,congrArg Additive.ofMul he⟩

private theorem source_marking
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    ∃ e : Source.Hstar H ≃* BinaryLinearThree.Group,
      H65Alternatives (act.representation.comp e.symm.toMonoidHom) ∧
      (Source.starImage H (one L T V₁ ⊔ (T : Subgroup G))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL := by
  classical
  let d := c.localSetup
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  let dn := localNaturalSetup d
  let P := one L T V₁ ⊔ (T : Subgroup G)
  have hPH : P ≤ H := hH.1.2
  have hL₁H : one L T V₁ ≤ H := le_sup_left.trans hPH
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hPH
  have hPn : P ≤ normalizer (V₃ : Set G) :=
    sup_le (Section07.ModelExclusions.point_residual_normalizes_seed dn) d.seed_stable
  have hPM : P ≤ M := by
    rw [d.local_normalizer]
    exact sup_le ((one_le L T V₁).trans (inf_le_left.trans
      (sup_le (Subgroup.le_normalizer : L ≤ normalizer (L : Set G)) d.normalizes_L))) d.normalizes_L
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le
    (show V₃ ≤ Source.UH H V₃ from le_conjugateSpanBy V₃ H)
  have hs := seedSpace_invariant H V₃ V₁ act P hPn
  have hc := seed_card_of_source_orders H V₃ V₁
    (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card
  have ht : ∀ u ∈ seedSpace H V₃ V₁, u ≠ 0 →
      ∀ v ∈ seedSpace H V₃ V₁, v ≠ 0 →
        ∃ p ∈ Source.starImage H P, act.representation p u = v := by
    intro u hu hune v hv hvne
    rw [seedSpace_eq_sectionImage] at hu hv
    obtain ⟨l,hl⟩ := Section07.ModelExclusions.seed_section_nonzero_orbit dn hL₁H
      act.representation act.conjugation u hu hune v hv hvne
    exact ⟨QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l),
      ⟨inclusion hL₁H l,mem_sup_left l.property,rfl⟩,hl⟩
  have hnotwo : ¬ IsPGroup 2 (Source.starImage H P) := by
    intro hp
    obtain ⟨m,hm,hmn,hfixed⟩ := fixed_seed act.representation _ hp
      (seedSpace H V₃ V₁) hc hs
    let D := seedSpace H V₃ V₁
    let m' : D := ⟨m,hm⟩
    let : Fintype D := Fintype.ofFinite D
    have hall : (Finset.univ : Finset D) ⊆ {0,m'} := by
      intro v _
      simp only [Finset.mem_insert,Finset.mem_singleton]
      by_cases hv : v.val = 0
      · exact Or.inl (Subtype.ext hv)
      · obtain ⟨p,hp,he⟩ := ht m hm hmn v.val v.property hv
        exact Or.inr (Subtype.ext (he.symm.trans (hfixed p hp)))
    have hle := Finset.card_le_card hall
    have hpair : ({0,m'} : Finset D).card ≤ 2 := by
      calc
        _ ≤ ({m'} : Finset D).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    have hcard : Fintype.card D = 4 := Nat.card_eq_fintype_card.symm.trans hc
    simp only [Finset.card_univ] at hle
    omega
  obtain ⟨S,hS⟩ := starImage_sylow H T hTH
  have hSP : (S : Subgroup (Source.Hstar H)) ≤ Source.starImage H P :=
    by rw [hS]; exact starImage_mono H le_sup_right
  have hproper : Source.starImage H P ≠ ⊤ :=
    starImage_ne_top H P M hPM hH.2.2 (kernel_le_source_parabolic H (one L T V₁) T hTH)
  obtain ⟨e,hTe,hPe⟩ := Matrix.PSL3Two.exists_sylow_line_marking e₀ S _ hSP hproper hnotwo
  have hfaith := f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes)
  have h65 : H65Theorem (U := Additive (Source.Utilde H V₃ V₁)) := by
    intro ρ _ m hf hg hd
    exact BinaryLinearThree.ParabolicCyclic.parabolic_seed_alternatives ρ m hf hg hd
  refine ⟨e,?_,hPe⟩
  exact H65_of_marking H V₃ V₁ act hfaith h65 _ _ hSP S.isPGroup' hc hs ht e hTe hPe

/-- The original binary quotient has all five H.6.5 alternatives with the
same isomorphism marking the actual point-residual parabolic. This also
exposes the marking to the natural-three reduction of the transvection case. -/
theorem source_binary_marking
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    ∃ e : Source.Hstar H ≃* BinaryLinearThree.Group,
      H65Alternatives (act.representation.comp e.symm.toMonoidHom) ∧
      (Source.starImage H (one L T V₁ ⊔ (T : Subgroup G))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL :=
  source_marking c act e₀

/-- Every binary whole quotient in the original source context has an actual
rank-one displacement on U_H/V₁. The alternative without transvections is
excluded using the selected source critical group and its marked line radical. -/
theorem source_binary_has_transvection
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    ∃ g : Source.Hstar H, fixedCodim act.representation (zpowers g) = 1 := by
  classical
  by_contra! hno
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  have hqs := (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339 hH K c.component.component).2
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness c.localSetup hH hF9
    (by rw [←c.component.generated,sup_assoc]) c.component.component c.component.normal hqs
    c.centralizer c.noncentral_core act.representation act.conjugation
    (fun g => by rw [←fixedCodim_zpowers_eq_displacement_rank]; exact hno g)
  obtain ⟨e,hclass,hPe⟩ := source_marking c act e₀
  let B := w.pair.Vgamma.map (MulAut.conj (w.conjugator : G)).toMonoidHom
  have hBq : IsQuadratic act.representation (Source.starImage H B) := by
    dsimp only [B]
    rw [MarkedGeometry.starImage_conjugate _ w.actor_le w.conjugator]
    exact (Representation.OrthogonalFourMinus.RankOne.InnerTransport.quadratic_conj_iff _ _ _).mpr w.quadratic
  have hBr : 1 < rank (Source.starImage H B) := by
    dsimp only [B]
    rw [MarkedGeometry.starImage_conjugate _ w.actor_le w.conjugator,rank_map_conj]
    exact w.rank_gt_one
  let σ := act.representation.comp e.symm.toMonoidHom
  have he (g : Source.Hstar H) (v : Additive (Source.Utilde H V₃ V₁)) :
      (LinearEquiv.refl (ZMod 2) _ : _ ≃ₗ[ZMod 2] _) (act.representation g v) =
        σ (e g) ((LinearEquiv.refl (ZMod 2) _ : _ ≃ₗ[ZMod 2] _) v) := by
    change act.representation g v = act.representation (e.symm (e g)) v
    rw [e.symm_apply_apply]
  apply BinaryLinearThree.LineRadical.no_large_quadratic_of_no_transvections σ hclass
    (fun g => ?_) ((Source.starImage H B).map e.toMonoidHom)
    (source_subgroup_image_le_R H _ B hH.1.2 w.conjugate_le_core e hPe)
    (quadratic_map_equivariant _ _ e.toMonoidHom (LinearEquiv.refl _ _) he hBq)
    (by rw [rank_map_injective e.toMonoidHom e.injective]; exact hBr)
  have hc := fixedCodim_map_equivariant act.representation σ e.toMonoidHom
    (LinearEquiv.refl _ _) he (zpowers (e.symm g))
  simp only [MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom,e.apply_symm_apply] at hc
  rw [←hc]
  exact hno _
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
