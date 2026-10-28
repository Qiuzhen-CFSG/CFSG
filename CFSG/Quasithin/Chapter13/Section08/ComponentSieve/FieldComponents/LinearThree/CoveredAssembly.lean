module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalAssembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.CoveredExclusion

/-!
# Assembly of the covered A₆ external-component exclusion

The actual earlier covered natural action and component list construct the
point-oriented L₃(2) × S₃ product. The generating seed then supplies a natural
tensor chief section and excludes transvections. Only at that point is the
earlier critical configuration invoked. Its marked proper and saturated cases
are both excluded, proving L₁ ≤ K.

`CriticalEarlier` records the literal earlier commutator, conjugation and
index clauses. It assumes neither a tensor module, a product marking, nor a
rank-one conclusion. It is requested only under the no-transvection premise
of 13.8.8(2); the proof discharges that premise.
Source: Aschbacher–Smith 13.8.21(1), printed p.957, with 13.8.4–18 and F.9.13–16.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
open Geometry Geometry.ExternalComponentAction Geometry.CoveredProduct
open Geometry.CoveredProduct.ResidualPlacement ExternalModules
variable {G : Type*} [Group G] [Finite G]
variable (H L₁ T V V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The earlier critical pair, with both directions of the conjugation, the
actual denominators D_H and D_γ, and the strict rank implication 13.8.18(4).
The section owner supplies these from 13.8.4–18 and F.9.13–16 after the
no-transvection hypothesis of case (2) has been established. -/
structure CriticalEarlier (act : SourceAction H V₃ V₁) where
  g : G
  h : H
  hV : V ≤ H
  hflag : V₃ ≤ V
  hflag_index : V₃.relIndex V = 2
  hline : V₁ ≤ V₃
  hcard : Nat.card V₁ = 2
  hcentral : H ≤ centralizer (V₁ : Set G)
  hseed : ⁅L₁ ⊔ T,V⁆ ≤ Source.UH H V₃
  hnoncentral : ¬ ⁅Source.VH H V,H⁆ ≤ Source.UH H V₃
  hforward : (Source.VH H V).map (MulAut.conj g).toMonoidHom ≤ H
  hback : Source.VH H V ≤ ((L₁ ⊔ T).pCoreIn 2).map (MulAut.conj g).toMonoidHom
  hplace : ((Source.VH H V).map (MulAut.conj g).toMonoidHom).map
    (MulAut.conj (h:G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2
  hcentralizer : ⁅Source.HC H V₃,Source.VH H V⁆ ≤ V₁
  hdisjoint : Disjoint V₁ (V₁.map (MulAut.conj g).toMonoidHom)
  hseed_noncentral : ¬ ⁅(Source.UH H V₃).map (MulAut.conj g).toMonoidHom,V⁆ ≤
    V₁.map (MulAut.conj g).toMonoidHom
  hcommute : ⁅Source.DH (Source.UH H V₃)
      ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
      (V₁.map (MulAut.conj g).toMonoidHom),
    Source.Dgamma ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
      (Source.UH H V₃) V₁⁆ = ⊥
  hline_commutators :
    ⁅(Source.UH H V₃).map (MulAut.conj g).toMonoidHom,
      Source.EH (Source.VH H V) ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (V₁.map (MulAut.conj g).toMonoidHom)⁆ ≤ V₁.map (MulAut.conj g).toMonoidHom ∧
    ⁅Source.UH H V₃, Source.Egamma ((Source.VH H V).map (MulAut.conj g).toMonoidHom)
      (Source.UH H V₃) V₁⁆ ≤ V₁
  hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃)
      ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
      (V₁.map (MulAut.conj g).toMonoidHom)).relIndex (Source.UH H V₃)) ≤
    Nat.log 2 ((Source.Dgamma ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
      (Source.UH H V₃) V₁).relIndex ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom))
  hactor : IsElementaryTwo
      (Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)) ∧
    IsQuadratic act.representation
      (Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)) ∧
    fixedCodim act.representation
        (Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)) ≤
      2 * rank (Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom))
  hlarge : (∀ a : Source.Hstar H,
      fixedCodim act.representation (zpowers a) ≠ 1) →
    1 < rank (Source.starImage H ((Source.VH H V).map (MulAut.conj g).toMonoidHom))

variable (κ : GroupClass) (K L M G₁ : Subgroup G) (S : Sylow 2 G)

/-- The covered-A₆ branch of 13.8.21(1) from the source component list.
The full product and every subgroup mark are derived. The earlier critical
pair is conditional on absence of transvections, proved from the actual
natural tensor chief section before requesting that pair. -/
theorem L₁_le_of_covered_source
    (d : RankReduction.SourceSetup κ H K (one L S V₁) M G₁ S)
    (models : RankReduction.SmallQuotient (K ⧸ pCore 2 K))
    (natural : LocalAction.NaturalSetup L S V V₁ V₃)
    (hfactor : one L S V₁ = plus L S V₁ ⊔ zero L)
    (hNM : normalizer (zero L : Set G) = M)
    (hfit : fittingPreimageResidual H = ⊥ ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        fittingPreimageResidual H = one L S V₁) ∨
      fittingPreimageResidual H = plus L S V₁)
    (hqs : IsQuasisimple (Source.starImage H K))
    (act : SourceAction H V₃ V₁)
    (hfaithful : ∀ h : H,
      (∀ u : Source.UH H V₃,
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (conjugateUH H V₃ h u) =
          QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) → h ∈ pCore 2 H)
    (hd : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2)
    (critical : (∀ a : Source.Hstar H,
        fixedCodim act.representation (zpowers a) ≠ 1) →
      Nonempty (CriticalEarlier H (one L S V₁) S V V₃ V₁ act)) :
    one L S V₁ ≤ K := by
  by_contra hout
  let : (K.subgroupOf H).Normal := d.normal
  have hTH : (S : Subgroup G) ≤ H := le_sup_right.trans_eq d.generated
  have hSyl : ((S.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype = S := by
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
  have hH : H = K ⊔ (one L S V₁ ⊔ (S : Subgroup G)) := by
    rw [← d.generated, sup_assoc]
  obtain ⟨_, ⟨eK₀⟩⟩ := RankReduction.rank_one_and_model d hout models
  let eK := eK₀.trans Matrix.PSL3Two.equiv.symm
  obtain ⟨geo⟩ := source_product_geometry H K L S V V₁ V₃ M natural hfactor
    hH hout d.external hNM (S.subtype hTH) hSyl eK hfit
  have hfaith := ParabolicMarking.faithful_of_source_centralizer act hfaithful
  have hn : ∃ k : Source.starImage H K, ∃ v, act.representation k v ≠ v := by
    by_contra! hh
    have hall : ∀ k : Source.starImage H K, (k : Source.Hstar H) = 1 := by
      intro k
      apply hfaith
      ext v
      simpa using hh k v
    have hb : Source.starImage H K = ⊥ := bot_unique (fun k hk => hall ⟨k,hk⟩)
    exact (nontrivial_iff_ne_bot _).mp (eK₀.surjective.nontrivial) hb
  have hXcubic := geo.tensorCubic_inverse_image
  have hzseed := geo.component.seed_zero_fixed
  have hxseed := geo.component.seed_moved
  obtain ⟨A, B, hchief⟩ := source_natural_tensor_chief_section H V₃ V₁ act geo.equiv
    K (one L S V₁) S (zero L) (plus L S V₁) geo.component_image hn
    geo.parabolic_seed_normalizes geo.plus_le (geo.plus_le_one.trans le_sup_left)
    geo.oneT_image hXcubic hd hzseed hxseed
  obtain ⟨ec⟩ := hchief.2
  obtain ⟨c⟩ := critical (natural_tensor_section_no_transvections act.representation
    geo.equiv A B ec)
  let : Group.IsPerfect (K.subgroupOf H) := d.component.perfect
  have hres : pResidual 2 (K.subgroupOf H) = ⊤ := by
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN hp
    let := hN
    by_contra hne
    let : Nontrivial ((K.subgroupOf H) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect ((K.subgroupOf H) ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  exact CoveredExclusion.source_covered_configuration_exclusion H V₃ V₁ act
    K (zero L) (plus L S V₁) (one L S V₁) S V c.g c.h geo.equiv
    c.hV c.hflag c.hflag_index c.hline c.hcard c.hcentral
    (by rw [hfactor]; exact le_sup_right) geo.plus_le_one
    (by rw [geo.zero_image]; exact Subgroup.prod_mono le_top le_rfl)
    (by rw [geo.plus_image]; exact Subgroup.prod_mono le_rfl le_top)
    hzseed hxseed geo.parabolic_le hH d.normal hres hqs c.hseed c.hnoncentral
    c.hforward c.hback c.hplace c.hcentralizer c.hdisjoint c.hseed_noncentral
    c.hcommute geo.oneT_image c.hline_commutators
    (geo.oneT_core_image.trans MarkedProduct.pointV_prod_eq_tensorPointRadical) c.hcritical
    geo.component_image hn geo.parabolic_seed_normalizes hXcubic hd c.hactor c.hlarge

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
