module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlternatingAutomizerSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BinaryAutomizerSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoBinarySource
public import Theory.GroupTheory.CentralizerNormalSupplement
/-! # Normal-component automizers on the original two-core quotient
For the source-generated group with normal centerless component, its whole
centralizer lies in the original Sylow and equals the two-core. Quotienting
its actual conjugation action therefore uses exactly O₂(H). The previously
proved binary linear and A₆ automizers transfer to this literal quotient,
and each model supplies a surjective map with the original centralizer kernel.
Source: Aschbacher--Smith 2.5.8(2), 2.5.16 and 2.5.21, pp.556,560,565.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {M H L:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.normal_component_conjugation_ker
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype) :
    (MulAut.conjNormal:H→*MulAut (L.subgroupOf H)).ker=pCore 2 H := by
  let D:=L.subgroupOf H
  let e:=subgroupOfEquivOfLe c.component_le
  have hc:=MathieuSourceSetup.component_center_eq_bot c hG hempty hgen
  have hz:center D=⊥:=by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    have he: e x∈center L:=(centerCongr e ⟨x,hx⟩).property
    rw [hc] at he
    exact (mem_bot.mp he).trans (map_one e).symm
  have hg:D⊔(S:Subgroup H)=⊤:=by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le c.component_le,←hgen,
      ←MonoidHom.range_eq_map,range_subtype]
  have hC:=centralizer_le_sylow_of_normal_centerless_sup D S hz hg
  rw [MulAut.conjNormal_ker_eq_centralizer]
  ext a
  have he:=MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  constructor
  · intro ha
    have hcA:(a:G)∈twoCore H:=by
      rw [he]
      refine ⟨mem_map_of_mem H.subtype (hC ha),?_⟩
      intro l hl
      exact congrArg Subtype.val (ha ⟨l,c.component_le hl⟩ hl)
    obtain ⟨b,hb,hba⟩:=hcA
    exact H.subtype_injective hba ▸ hb
  · intro ha
    have hcA:(a:G)∈twoCore H:=mem_map_of_mem H.subtype ha
    rw [he] at hcA
    intro l hl
    exact Subtype.ext (hcA.2 l hl)

noncomputable def MathieuSourceSetup.normal_component_core_quotient_equiv_normalizer
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype) :
    (H⧸pCore 2 H)≃*((normalizer (L.subgroupOf H:Set H)) ⧸
      (centralizer (L.subgroupOf H:Set H)).subgroupOf (normalizer (L.subgroupOf H:Set H))) := by
  let D:=L.subgroupOf H
  let e:H≃*normalizer (D:Set H):=
    topEquiv.symm.trans (MulEquiv.subgroupCongr D.normalizer_eq_top.symm)
  let f:=MulAut.conjNormal (H:=D)
  have hf:D.normalizerMonoidHom.comp e.toMonoidHom=f:=by
    ext a d
    rfl
  have hk:f.ker=pCore 2 H:=MathieuSourceSetup.normal_component_conjugation_ker c hG hempty hgen
  have hmap:(pCore 2 H).map e.toMonoidHom=
      (centralizer (D:Set H)).subgroupOf (normalizer (D:Set H)):=by
    rw [←D.normalizerMonoidHom_ker,←hk,←hf,←MonoidHom.comap_ker,
      map_comap_eq_self_of_surjective e.surjective]
  exact QuotientGroup.congr _ _ e hmap

/-- The binary linear quotient of the original H by its two-core. -/
theorem MathieuSourceSetup.normal_linear_binary_core_quotient
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L≃*Matrix.PSL3Two.PSL) :
    Nonempty ((H⧸pCore 2 H)≃*MulAut Matrix.PSL3Two.PSL) := by
  obtain ⟨eN⟩:=MathieuSourceSetup.linear_binary_normalizer_quotient c hG hempty e
  exact ⟨(MathieuSourceSetup.normal_component_core_quotient_equiv_normalizer c hG hempty hgen).trans eN⟩

/-- The A₆ alternatives on the literal original two-core quotient. -/
theorem MathieuSourceSetup.normal_alternating_six_core_quotient
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L≃*AlternatingSix.ShadowLocal.A6) :
    Nonempty ((H⧸pCore 2 H)≃*AlternatingSix.M10.extension) ∨
      Nonempty ((H⧸pCore 2 H)≃*GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∨
      Nonempty ((H⧸pCore 2 H)≃*AlternatingSix.ShadowLocal.AutA6) := by
  let q:=MathieuSourceSetup.normal_component_core_quotient_equiv_normalizer c hG hempty hgen
  rcases MathieuSourceSetup.alternating_six_normalizer_quotient c hG hempty e with h|h|h
  · obtain ⟨eB⟩:=h
    exact Or.inl ⟨q.trans eB⟩
  · obtain ⟨eB⟩:=h
    exact Or.inr (Or.inl ⟨q.trans eB⟩)
  · obtain ⟨eB⟩:=h
    exact Or.inr (Or.inr ⟨q.trans eB⟩)

/-- A quotient model supplies the exact surjection consumed by the source
Sylow analysis, with S_C as its literal kernel. -/
theorem MathieuSourceSetup.exists_surjective_core_model
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    {B:Type*} [Group B] (e:(H⧸pCore 2 H)≃*B) :
    ∃f:H→*B,Function.Surjective f ∧
      f.ker=(((S:Subgroup H).map H.subtype)⊓centralizer (L:Set G)).subgroupOf H := by
  let f:=e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  refine ⟨f,e.surjective.comp (QuotientGroup.mk'_surjective _),?_⟩
  rw [show f=e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)) from rfl,
    MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',
    ←MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
  exact (comap_map_eq_self_of_injective H.subtype_injective (pCore 2 H)).symm

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
