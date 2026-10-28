module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Closure
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.SourceEscape

/-!
# The original two-A₃ product in13.5.6

For the nonisotropic conjugate W of the original V₂, the earlier source
escape theorem constructs the actual short A₆ block and its literal layer V.
Lift the native cubic axes through its possible central two-cover. The
resulting commuting A₃ factors generate the full O^{3′}(N_M(W)), with
embedded two-core V. The original normalizer and conjugating element are
retained throughout. Only the preceding unique maximal two-local theorem
remains explicit; the later ambient-containment contradiction is separate.

Source: Aschbacher–Smith13.5.6, printed p.917, combined manuscript of
1 March2004.
-/

@[expose] public section
open Subgroup BinaryPermutation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)

noncomputable def cubicResidual (M W:Subgroup G) : Subgroup G :=
  (primeToResidual 3 (M⊓normalizer (W:Set G) : Subgroup G)).map
    (M⊓normalizer (W:Set G)).subtype

theorem two_blocks_of_original_block
    (hb:ChapterC.IsAlternatingBlock L 6) (hU:(ChapterC.blockU L).map L.subtype=V)
    (hMV:M≤normalizer (V:Set G)) (W:Subgroup G) (hWV:W≤V) (hcard:Nat.card W=4)
    (hn:¬∀v∈image d W,∀w∈image d W,form v w=0)
    (hr:primeRank 3 (M⊓normalizer (W:Set G) : Subgroup G)≤2) :
    ∃X₁ X₂:Subgroup G, ChapterC.IsAlternatingBlock X₁ 3 ∧ ChapterC.IsAlternatingBlock X₂ 3 ∧
      X₁≤centralizer (X₂:Set G) ∧ Disjoint X₁ X₂ ∧
      cubicResidual M W=X₁⊔X₂ ∧ (cubicResidual M W).pCoreIn 2=V ∧
      M⊓normalizer (W:Set G)≤normalizer (cubicResidual M W:Set G) := by
  obtain ⟨c⟩:=exists_cubicPair d hb W hWV hcard hn
  have hy:=CubicPair.residual_eq d c hb hU hMV hWV hr
  change cubicResidual M W=V⊔(c.first⊔c.second).map L.subtype at hy
  have hd:Disjoint (⁅V,c.first.map L.subtype⁆⊔c.first.map L.subtype)
      (⁅V,c.second.map L.subtype⁆⊔c.second.map L.subtype):=
    (ChapterC.alternatingThree_pair _ _ c.first_block c.second_block c.commuting).1
  refine ⟨_,_,c.first_block,c.second_block,c.commuting,hd,hy.trans c.join.symm,?_,?_⟩
  · rw [hy]
    exact c.core
  · rw [hy]
    exact CubicPair.normalized d c hb hU hMV hWV

/-- The literal two-A₃ product in the contrary nonisotropic conjugate branch
of13.5.6. Only the earlier unique maximal two-local theorem remains explicit. -/
theorem source_two_blocks_of_nonisotropic_conjugate
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (x:G)(hWV:V₂.map (MulAut.conj x).toMonoidHom≤V)
    (hn:¬∀v∈image d (V₂.map (MulAut.conj x).toMonoidHom),
      ∀w∈image d (V₂.map (MulAut.conj x).toMonoidHom),form v w=0) :
    let W:=V₂.map (MulAut.conj x).toMonoidHom
    ∃X₁ X₂:Subgroup G, ChapterC.IsAlternatingBlock X₁ 3 ∧ ChapterC.IsAlternatingBlock X₂ 3 ∧
      X₁≤centralizer (X₂:Set G) ∧ Disjoint X₁ X₂ ∧
      cubicResidual M W=X₁⊔X₂ ∧ (cubicResidual M W).pCoreIn 2=V ∧
      M⊓normalizer (W:Set G)≤normalizer (cubicResidual M W:Set G) := by
  obtain ⟨hb,hU,hMV,_,hr⟩:=source_block_of_nonisotropic_conjugate d hu x hWV hn
  exact two_blocks_of_original_block d hb hU hMV _ hWV
    ((card_map_of_injective (MulAut.conj x).injective).trans d.plane_card) hn hr
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
