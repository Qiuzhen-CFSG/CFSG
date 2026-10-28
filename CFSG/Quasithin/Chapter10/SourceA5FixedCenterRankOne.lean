module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterTransvection
public import Theory.Representation.CentralizerQuotientRankOne

/-!
# The literal rank-one quotient action in the positive fixed-center branch

The actual H-star orbit W and commutator witness give a nonidentity involution
in H/C_H(W). Its conjugation action is faithful, its two-core is trivial by
the source reducedness of W, and its displacement range is exactly the line
spanned by the original nonzero commutator. The original H is the SQTK cover.
The separate generation hypothesis in G.6.1 is not asserted for all of W.

Source: Aschbacher–Smith 10.2.1 and G.6.1–4, printed pp.743 and345–346.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual module and centralizer quotient satisfy every elementary
rank-one action requirement, with generation kept separate. -/
@[expose] def SourceFixedCenterRankOne
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal ∧
    H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
    IsSQTK KnownSimple.IsKnownSimple H ∧
    (let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
     W ≤ omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) ∧
     ∃ hred : IsPReduced 2 (W.subgroupOf H),
       letI := hred.normal
       letI := hred.elementary
       let q := QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H))
       let ρ := centralizerQuotient (W.subgroupOf H)
       Function.Injective ρ ∧ Function.Surjective q ∧
       pCore 2 (H ⧸ centralizer (W.subgroupOf H : Set H)) = ⊥ ∧
       ∃ g : H, (g:G)∈(T : Subgroup G) ⊓ localOrbit T L ∧
         ∃ v : W.subgroupOf H, v≠1 ∧
           LinearMap.range (ρ (q g)-(LinearMap.id : Additive (W.subgroupOf H) →ₗ[ZMod 2] Additive (W.subgroupOf H))) =
             Submodule.span (ZMod 2) {Additive.ofMul v} ∧
           Module.finrank (ZMod 2) (LinearMap.range (ρ (q g)-(LinearMap.id : Additive (W.subgroupOf H) →ₗ[ZMod 2] Additive (W.subgroupOf H))))=1 ∧
           q g≠1 ∧ (q g)^2=1)

theorem source_exists_fixed_center_rank_one
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourceFixedCenterRankOne D := by
  obtain ⟨H,hH,hHN,hWE,hred,g,hg,v,hv,hvne,hline,x,hx,hxv⟩ :=
    source_exists_fixed_center_transvection D e hn hne hout
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  have hWH : W ≤ H := fun x hx => hH.1.1.2
    (((mem_omegaOneCenterAmbient_iff _ _).mp (hWE hx)).1.1)
  let gH : H := ⟨g,hH.1.1.2 hg.1⟩
  let vH : W.subgroupOf H := ⟨⟨v,hWH hv⟩,hv⟩
  let := hred.normal
  let := hred.elementary
  refine ⟨H,hH,hHN,Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1,hWE,hred,?_,
    QuotientGroup.mk'_surjective _,hred.quotient_pCore_eq_bot,gH,hg,vH,?_,?_⟩
  · intro a b hab
    apply centralizerQuotient_faithful (W.subgroupOf H)
    exact Units.ext hab
  · intro he
    exact hvne (congrArg (fun z : W.subgroupOf H => (z.val:G)) he)
  · apply centralizerQuotient_rank_one_of_commutator_line (W.subgroupOf H) gH vH
    · intro he
      exact hvne (congrArg (fun z : W.subgroupOf H => (z.val:G)) he)
    · intro y hy
      exact (hline y hy).imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
    · exact ⟨⟨x,hWH hx⟩,hx,Subtype.ext hxv⟩

end CFSG.Quasithin.Chapter10
