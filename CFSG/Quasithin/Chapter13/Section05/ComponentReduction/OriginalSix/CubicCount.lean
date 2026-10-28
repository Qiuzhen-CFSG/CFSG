module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosureUpper
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients

/-!
# The original A₄ quotient and cubic chief-count invariant

The source residual maps onto the marked four-letter A₄. Its kernel is
the pair core intersected with L₁. That core normalizes L₁, so both have
the same cubic fixed index. The complete original L₁ chief count is
therefore this fixed length plus the single Klein-four contribution.
Source: Aschbacher–Smith13.5.22(2), printed p.924.
-/
public section
open Subgroup NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicCount
open Section08.SourceCompletion NormalBranch
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks SourceFiveModule SourceUpperStructure
open ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
include d

theorem exists_residual_actor (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L) (hL : D.L₁≤NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    ∃ f : D.L₁→*alternatingGroup (Fin 4), Function.Surjective f ∧
      f.ker=((NormalBranch.K D g.val).pCoreIn 2).subgroupOf D.L₁ ∧ IsPGroup 2 f.ker := by
  let hLL : D.L₁≤D.L := hL.trans hK
  let f₀ : D.L₁→*Equiv.Perm (Fin 6) := (localMap d).comp (inclusion hLL)
  have hr : f₀.range=(D.L₁.subgroupOf D.L).map (localMap d) := by
    rw [MonoidHom.range_comp,inclusion_range]
  obtain ⟨b,hb,_⟩ := QuadraticSource.source_even_flag d
  have he : f₀.range=Theory.SpecificGroups.SymmetricSix.BinaryFlags.K.map
      (MulAut.conj b.val).toMonoidHom := hr.trans (SourcePointCore.local_residual_marking d h b hb)
  let q : f₀.range≃*alternatingGroup (Fin 4) :=
    (MulEquiv.subgroupCongr he).trans
      (((MulAut.conj b.val).subgroupMap Theory.SpecificGroups.SymmetricSix.BinaryFlags.K).symm.trans fourLetterEquiv)
  let f : D.L₁→*alternatingGroup (Fin 4) := q.toMonoidHom.comp f₀.rangeRestrict
  have hk₀ : f.ker=f₀.ker := by
    ext x
    change q (f₀.rangeRestrict x)=1 ↔ f₀ x=1
    rw [q.map_eq_one_iff,Subtype.ext_iff]
    rfl
  have hk : f.ker=((NormalBranch.K D g.val).pCoreIn 2).subgroupOf D.L₁ := by
    rw [hk₀]
    ext x
    let xK : NormalBranch.K D g.val := ⟨x.val,hL x.property⟩
    have hf : x∈f₀.ker ↔ xK∈(restrictedActor d hK a hi).ker := by
      rw [restrictedActor_ker d hK a hi]
      rfl
    rw [hf,restrictedActor_ker_eq_twoCore d hK a hi e]
    constructor
    · exact fun hx => mem_map_of_mem (NormalBranch.K D g.val).subtype hx
    · rintro ⟨y,hy,he⟩
      exact (show y=xK from Subtype.ext he) ▸ hy
  refine ⟨f,q.surjective.comp f₀.rangeRestrict_surjective,hk,?_⟩
  rw [hk]
  exact (isPGroup_pCoreIn 2 _).comap_subtype

theorem core_normalizes_residual (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    (NormalBranch.K D g.val).pCoreIn 2≤normalizer (D.L₁:Set G) := by
  have hSL := (pCoreIn_le 2 (NormalBranch.K D g.val)).trans hK
  have hSG : (NormalBranch.K D g.val).pCoreIn 2≤D.Gz :=
    (core_centralizes_module d h e g hK a hi).trans
      (centralizer_le (h.point_lt.le.trans h.plus_le))
  exact (le_inf hSL hSG).trans (le_normalizer_embedded_pResidual 2 (D.L⊓D.Gz))

theorem count_eq_core_length_add_one (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L) (hL : D.L₁≤NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (A : Subgroup G) (hAL : A≤D.L₁) (hA : Nat.card A=3)
    (t : ChiefSeries D.L₁) (h0 : t.head=⊥) (h1 : t.last=⊤) :
    t.noncentralTwoCount=conjugationCubicLength A ((NormalBranch.K D g.val).pCoreIn 2)+1 := by
  obtain ⟨f,hf,hk,hp⟩ := exists_residual_actor d h e g hK hL a hi
  have hcard : Nat.card (A.subgroupOf D.L₁)=3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv).trans hA
  have hc := alternatingFour_count f hf hp (A.subgroupOf D.L₁) hcard t h0 h1
  rw [hk] at hc
  let S := (NormalBranch.K D g.val).pCoreIn 2
  have hI : (S⊓D.L₁).subgroupOf D.L₁=S.subgroupOf D.L₁ := by
    ext x
    exact and_iff_left x.property
  have he := length_subgroupOf A (S⊓D.L₁) D.L₁ hAL inf_le_right
  rw [hI] at he
  have hlen := intersection_length_eq A S D.L₁
    (IsPGroup.of_card (p:=3) (n:=1) (by simpa using hA))
    (isPGroup_pCoreIn 2 _) hAL (core_normalizes_residual d h e g hK a hi)
    (hL.trans (pair_normalizes_core g))
  exact hc.trans (congrArg (·+1) (he.trans hlen))

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicCount
