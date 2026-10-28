module

public import CFSG.Quasithin.Chapter13.Section07.SourceDuality
public import CFSG.Quasithin.Chapter13.Section07.SpanGrowth
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# The original seed displacement in13.7.12(2)

The fixed denominator of index four has a two-dimensional annihilator
under the constructed commutator duality. V3 centralizes that denominator,
and its original image has dimension two because its fixed kernel is V1.
Thus it is exactly the annihilator. Dual fixation then puts every original
actor displacement in that same seed image.

The group consumer proves [UH,A] <= V3 U0 on the unchanged subgroups,
where A=VH^g intersection Q and U0=C_UH(QH). It constructs the original
source g and retains genuine13.5.4(5) noncentrality; neither duality nor
a faithful-action or displacement conclusion is a premise.
Source: Aschbacher--Smith13.7.12(2), printed p.942.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
 theorem source_duality_seed_displacement
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hHG:H≤G₁) (hne:⁅V₃,G₁.pCoreIn 2⁆≠⊥)
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let U:=Section08.Source.UH H V₃
    let QH:=H.pCoreIn 2
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let U₀:=U⊓centralizer (QH:Set G)
    let C:=Section08.Source.HC H V₃
    let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
    let R:=(QH⊓Q)⊔C
    ∃hE:IsElementaryAbelian 2 U, letI:=hE;
      ∃ (ρ:Representation (ZMod 2) H (Additive (U⧸U₀.subgroupOf U)))
        (sU:Representation.BinaryConjugationSection H U U₀ ρ)
        (sQ:Representation.BinaryConjugationSection H QH C ρ.dual),
        (∀(q:QH)(u:U),(sQ.coordinates q).toAdd (sU.coordinates u).toAdd=0 ↔ ⁅(q:G),(u:G)⁆=1) ∧
        (∀u:U,(sU.coordinates u).toAdd=Additive.ofMul (QuotientGroup.mk' (U₀.subgroupOf U) u)) ∧
        (sQ.imageSpace R).dualCoannihilator=sU.imageSpace V₃ ∧
        Module.finrank (ZMod 2) (sU.imageSpace V₃)=2 ∧
        ∀a:H,(a:G)∈A→LinearMap.range (ρ a-(1:Module.End (ZMod 2) (Additive (U⧸U₀.subgroupOf U))))≤sU.imageSpace V₃ := by
  dsimp only
  let U:=Section08.Source.UH H V₃
  let QH:=H.pCoreIn 2
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let U₀:=U⊓centralizer (QH:Set G)
  let C:=Section08.Source.HC H V₃
  let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
  let R:=(QH⊓Q)⊔C
  obtain ⟨hE,ρ,sU,sQ,hpair,hcoord,hr,hfixed⟩:=source_duality_fixed_core d h hU hV hHG hne g hs hout
  let :=hE
  have hseedU:V₃≤U:=le_conjugateSpanBy V₃ H
  have hU₀seed:U₀⊓V₃=V₁ := by
    have he:=seed_centralizer_eq_line d h (seed_noncentral_on_local_core h hHG hne)
    change V₃⊓centralizer (QH:Set G)=V₁ at he
    rw [←he]
    ext z
    exact ⟨fun hz=>⟨hz.2,hz.1.2⟩,fun hz=>⟨⟨hseedU hz.1,hz.2⟩,hz.1⟩⟩
  have hindex:U₀.relIndex V₃=4 := by
    rw [←inf_relIndex_right,hU₀seed]
    have he:=relIndex_mul_relIndex (⊥:Subgroup G) V₁ V₃ bot_le h.point_lt.le
    rw [relIndex_bot_left,relIndex_bot_left,d.line_card,d.seed_card] at he
    omega
  have hdim:Module.finrank (ZMod 2) (sU.imageSpace V₃)=2:=
    sU.imageSpace_finrank_of_index V₃ hseedU 2 hindex
  have hCQ:C≤QH:=sQ.kernel_le
  have hRQ:R≤QH:=sup_le inf_le_left hCQ
  have hCR:C≤R:=le_sup_right
  have hcodim:=sQ.imageSpace_codimension_of_index R hRQ hCR 2 hr
  have hadd:Module.finrank (ZMod 2) (sQ.imageSpace R)+
      Module.finrank (ZMod 2) (sQ.imageSpace R).dualCoannihilator=
      Module.finrank (ZMod 2) (Additive (U⧸U₀.subgroupOf U)) :=
    Subspace.finrank_add_finrank_dualCoannihilator_eq _
  rw [Subspace.dual_finrank_eq] at hcodim
  change Module.finrank (ZMod 2) (sQ.imageSpace R)+2=
    Module.finrank (ZMod 2) (Additive (U⧸U₀.subgroupOf U)) at hcodim
  have hannDim:Module.finrank (ZMod 2) (sQ.imageSpace R).dualCoannihilator=2:=by omega
  have hRC:R≤centralizer (V₃:Set G) := by
    apply sup_le
    · exact inf_le_right.trans (h.sylow_centralizer.symm.le.trans
        (inf_le_right.trans (centralizer_le d.seed_le)))
    · exact inf_le_right.trans (centralizer_le hseedU)
  have hseedAnn:sU.imageSpace V₃≤(sQ.imageSpace R).dualCoannihilator := by
    intro w hw
    obtain ⟨u,hu,rfl⟩:=(sU.mem_imageSpace_iff _ _).mp hw
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨q,hq,rfl⟩:=(sQ.mem_imageSpace_iff _ _).mp hφ
    exact (hpair q u).mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hRC hq u hu).symm)
  have hann:(sQ.imageSpace R).dualCoannihilator=sU.imageSpace V₃:=
    (Submodule.eq_of_le_of_finrank_eq hseedAnn (hdim.trans hannDim.symm)).symm
  refine ⟨hE,ρ,sU,sQ,hpair,hcoord,hann,hdim,?_⟩
  intro a ha
  rw [←hann]
  exact Representation.displacement_le_coannihilator_of_dual_fixed ρ a (sQ.imageSpace R)
    (hfixed a⁻¹ (A.inv_mem ha))


/-- The literal original13.7.12(2): after killing the actual fixed subgroup U₀,
all displacement by the original second core factor lies in the original V₃ image. -/
theorem source_seed_displacement_bound
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hHG:H≤G₁) (hne:⁅V₃,G₁.pCoreIn 2⁆≠⊥)
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let U:=Section08.Source.UH H V₃
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
    ⁅U,A⁆≤V₃⊔(U⊓centralizer (H.pCoreIn 2:Set G)) := by
  dsimp only
  let U:=Section08.Source.UH H V₃
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
  have hAH:A≤H:=inf_le_right.trans
    ((h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H)
  obtain ⟨hE,ρ,sU,sQ,hpair,hcoord,hann,hdim,hmove⟩:=
    source_duality_seed_displacement d h hU hV hHG hne g hs hout
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha u hu
  let aH:H:=⟨a,hAH ha⟩
  let uU:U:=⟨u,hu⟩
  apply (sU.displacement_mem_imageSpace_iff V₃ (le_conjugateSpanBy V₃ H) aH uU).mp
  exact hmove aH ha ⟨(sU.coordinates uU).toAdd,rfl⟩

/-- Original-source construction of13.7.11 and13.7.12(2) on the same marked pair. -/
theorem exists_source_seed_displacement
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hHG:H≤G₁) (hne:⁅V₃,G₁.pCoreIn 2⁆≠⊥) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
      let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
      let A:=conjugate F.VH (g:G)⊓Q
      F.DH (g:G)<F.UH ∧ ⁅F.UH,A⁆≤V₃⊔(F.UH⊓centralizer (F.QH:Set G)) := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  exact ⟨g,hs,hspan,hout,pair_D_lt_seed_span d h hU hV (inclusion le_sup_left g) hs hout,
    source_seed_displacement_bound d h hU hV hHG hne (inclusion le_sup_left g) hs hout⟩

end CFSG.Quasithin.Chapter13.Section07
