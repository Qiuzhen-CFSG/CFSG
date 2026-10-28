module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleCase
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.ProperSections
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ParabolicSections
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerRankObstruction

/-!
# Proper-section induction for sporadic local obstructions

A simple section of a proper two-local in a quotient lifts to an actual proper
two-local section in the original group. Apply the simultaneous induction
hypothesis to its literal kernel quotient, which is in the ambient universe.
This gives the source rank bound without assuming quasithinness of a quotient.
The remaining helpers retain the original central projection and exclude the
simultaneous odd-primary and two-primary center possibilities.

Source: Aschbacher–Smith A.2.15 and A.2.19, printed pp.37–41.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
universe u v w
variable {G : Type u} {H : Type v} {T : Type w}
  [Group G] [Group H] [Group T]

public theorem simple_quasisimple [IsSimpleGroup T] (hna : ¬ IsMulCommutative T) :
    IsQuasisimple T := by
  have hc : commutator T = ⊤ :=
    (inferInstance : (commutator T).Normal).eq_bot_or_eq_top.resolve_left
      (fun h => hna ((commutator_eq_bot_iff T).mp h))
  let : Group.IsPerfect T := ⟨hc⟩
  have hz : center T = ⊥ :=
    (inferInstance : (center T).Normal).eq_bot_or_eq_top.resolve_right
      (fun h => hna (center_eq_top_iff.mp h))
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }

public theorem semisimple_of_quasisimple [IsQuasisimple T] : IsSemisimple T := by
  let : IsQuasisimple (⊤ : Subgroup T) := IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
  exact top_unique (le_sSup (show IsComponent T ⊤ from ⟨.top,inferInstance⟩))

public theorem proper_section_rank_bound [Finite G] [IsSimpleGroup T]
    {K : GroupClass.{u}} (ih : TheoremsOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (hna : ¬ IsMulCommutative T) {M : Subgroup G}
    (hM : M ≠ ⊤) (hlocal : IsTwoLocal M) (hT : IsSectionOf T M)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p T ≤ 2 := by
  let : Finite T := hT.finite
  let : IsQuasisimple T := simple_quasisimple hna
  obtain ⟨U,f,hf⟩ := hT
  let e : (U ⧸ f.ker) ≃* T := QuotientGroup.quotientKerEquivOfSurjective f hf
  let : IsQuasisimple (U ⧸ f.ker) := IsQuasisimple.of_mulEquiv e.symm
  have hl : primeRank p M ≤ 2 := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG M hlocal p hp ho
  have hb := ((ih.subgroup M hM).1 (hG.subgroup M) (hK.subgroup M)
    (U ⧸ f.ker) (.quotient_subgroup U f.ker) semisimple_of_quasisimple p hp ho).2 hl
  exact (primeRank_equiv p e).symm ▸ hb.trans hl

public theorem false_of_centralizer_quotient [Finite G] [IsSimpleGroup T]
    {K : GroupClass.{u}} (ih : TheoremsOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (π : G →* H) (hπ : Function.Surjective π) (hZ : center H = ⊥)
    (d : InvolutionCentralizerQuotientData H T)
    (hna : ¬ IsMulCommutative T) (hr : 2 < primeRank 3 T) : False := by
  let : Finite H := Finite.of_surjective π hπ
  have hs : IsSectionOf T (centralizer ({d.involution} : Set H)) := by
    let e := subgroupOfEquivOfLe d.centralizes
    exact ⟨d.numerator.subgroupOf _, d.quotientMap.comp e.toMonoidHom,
      d.surjective.comp e.surjective⟩
  obtain ⟨M,hM,hl,_,hT⟩ := EvenLie.exists_proper_twoLocal_section_lift π hπ
    (d.proper_centralizer hZ) (isTwoLocal_involution_centralizer d.involution_order) hs
  exact (not_le_of_gt hr) (proper_section_rank_bound ih hG hK hna hM hl hT 3
    (by decide) (by decide))

@[expose] public noncomputable def projection (e : G ⧸ center G ≃* H) : G →* H :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center G))

public theorem projection_surjective (e : G ⧸ center G ≃* H) : Function.Surjective (projection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

public theorem projection_ker (e : G ⧸ center G ≃* H) : (projection e).ker = center G := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

public theorem center_eq_bot_of_simple [IsSimpleGroup H] (hna : ¬ IsMulCommutative H) : center H = ⊥ :=
  (inferInstance : (center H).Normal).eq_bot_or_eq_top.resolve_right
    (fun h => hna (center_eq_top_iff.mp h))

public theorem center_eq_bot_of_central_quotient [IsQuasisimple G]
    (e : G ⧸ center G ≃* H) : center H = ⊥ := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : IsSimpleGroup H := e.symm.isSimpleGroup
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective (projection_surjective e)
  exact center_eq_bot_of_simple (Group.IsPerfect.not_isMulCommutative H)

public theorem false_of_cover_centralizer_quotient [Finite G] [IsQuasisimple G] [IsSimpleGroup T]
    {K : GroupClass.{u}} (ih : TheoremsOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (e : G ⧸ center G ≃* H) (d : InvolutionCentralizerQuotientData H T)
    (hna : ¬ IsMulCommutative T) (hr : 2 < primeRank 3 T) : False :=
  false_of_centralizer_quotient ih hG hK (projection e) (projection_surjective e)
    (center_eq_bot_of_central_quotient e) d hna hr

public theorem center_eq_bot_of_two_and_odd {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hP : IsPGroup p (center G)) (h2 : IsPGroup 2 (center G)) : center G = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hd := IsPGroup.disjoint_of_ne p 2 (by intro hh; subst p; norm_num at ho)
    (center G) (center G) hP h2
  exact disjoint_self.mp hd

public theorem twoCore_eq_bot_of_odd_center [Finite G] [IsQuasisimple G] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hP : IsPGroup p (center G)) : pCore 2 G = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hd := IsPGroup.disjoint_of_ne p 2 (by intro hh; subst p; norm_num at ho)
    (center G) (pCore 2 G) hP pCore_isPGroup
  apply bot_unique
  intro x hx
  exact disjoint_iff_inf_le.mp hd ⟨IsQuasisimple.pCore_le_center 2 hx,hx⟩

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
