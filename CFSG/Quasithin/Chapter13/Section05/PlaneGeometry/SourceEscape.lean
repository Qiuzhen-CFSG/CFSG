module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.CardBounds
public import Theory.GroupTheory.SylowSubgroupCentralizerAlignment.NormalizerControl
/-!
# Original normalizer escape and the A₆ block in 13.5.6

Select a fully centralized conjugate of the contrary nondegenerate plane
inside M_V. If its two-centralizer normalizer lay in M, the finite p-group
normalizer condition would make it Sylow in the ambient centralizer.
Its index is at least four in T, whereas a conjugate of C_T(V₂) has order
at least |T|/2 in that same centralizer. This contradiction supplies escape.
The complete original C.1.24 application now gives the actual block L,
its literal layer V, M normalization, characteristic two and ternary rank.

Source: Aschbacher--Smith 13.5.6, printed p.917. Only the earlier unique
maximal two-local property of LT remains explicit. The subsequent two-A₃
product and original nonabelian-core contradiction are separate steps.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_plane_normalizer_escape (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,form x y=0)
    (hmax:∀U:Subgroup G,IsPGroup 2 U→planeCentralizer (T:=T) W≤U→
      U≤M⊓centralizer (W:Set G)→U=planeCentralizer (T:=T) W)
    (x:G)(hx:V₂.map (MulAut.conj x).toMonoidHom=W) :
    ¬normalizer (planeCentralizer (T:=T) W:Set G)≤M := by
  intro hN
  let R:Subgroup G:=(planeCentralizer (T:=T) V₂).map (MulAut.conj x).toMonoidHom
  have hr:IsPGroup 2 R:=(T.isPGroup'.to_le inf_le_left).map _
  have hRC:R≤centralizer (W:Set G):=by
    rw [←hx]
    exact (map_mono (show planeCentralizer (T:=T) V₂≤centralizer (V₂:Set G) from inf_le_right)).trans
      (map_centralizer_le_centralizer_image _ _)
  have hb:=Subgroup.card_le_of_local_sylow_normalizer_control
    (planeCentralizer (T:=T) W) (centralizer (W:Set G)) M
    (T.isPGroup'.to_le inf_le_left) inf_le_right hN
    (fun U hp hQU hUC hUM=>hmax U hp hQU (le_inf hUM hUC)) R hr hRC
  have hc:Nat.card R=Nat.card (planeCentralizer (T:=T) V₂):=
    card_map_of_injective (MulAut.conj x).injective
  rw [hc] at hb
  have hlow:=sylow_le_two_mul_card_seedPlaneCentralizer d
  have hhi:=four_mul_card_planeCentralizer_le_sylow d W hWV hcard hn
  have hp:0<Nat.card (planeCentralizer (T:=T) W):=Nat.card_pos
  nlinarith

/-- The original contrary nondegenerate conjugate forces the actual A₆
block, with no transposition, kernel, Sylow, normalizer-escape or block
premise. Only the preceding unique maximal two-local theorem remains. -/
theorem source_block_of_nonisotropic_conjugate
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (x:G)(hWV:V₂.map (MulAut.conj x).toMonoidHom≤V)
    (hn:¬∀v∈image d (V₂.map (MulAut.conj x).toMonoidHom),
      ∀w∈image d (V₂.map (MulAut.conj x).toMonoidHom),form v w=0) :
    ChapterC.IsAlternatingBlock L 6 ∧ (ChapterC.blockU L).map L.subtype=V ∧
      M≤normalizer (V:Set G) ∧ generalizedFitting M=pCore 2 M ∧
      primeRank 3 (M⊓normalizer (V₂.map (MulAut.conj x).toMonoidHom:Set G):Subgroup G)≤2 := by
  let W:=V₂.map (MulAut.conj x).toMonoidHom
  have hc:Nat.card W=4:=by rw [card_map_of_injective (MulAut.conj x).injective,d.plane_card]
  obtain ⟨g,hgV,hgc,hgn,hgmax⟩:=source_fully_centralized_plane d W hWV hc hn
  have he:V₂.map (MulAut.conj (g.val*x)).toMonoidHom=
      W.map (MulAut.conj g.val).toMonoidHom := by
    exact Subgroup.conjBy_mul V₂ g.val x
  have hesc:=source_plane_normalizer_escape d _ hgV hgc hgn hgmax (g.val*x) he
  obtain ⟨hb,hV,hM,hF,_⟩:=source_block_with_rank d hu _ hgV hgc hgn hesc
  exact ⟨hb,hV,hM,hF,source_local_plane_normalizer_rank d W hc⟩

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
