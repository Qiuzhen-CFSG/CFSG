module

public import CFSG.Quasithin.Chapter13.Section07.PairDIntersections
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original seed complement

The square condition transfers the escaped point to the opposite seed
span. Two hyperplanes in the natural group of order sixteen meet in at
least four elements; disjointness from the original point forces exactly
four. Their intersection is therefore the complete intersection of the
conjugate seed span with V3 and a complement to V1 in V3.
The unchanged V3 also lies in the actual pair intersection.
Source: Aschbacher--Smith13.7.10(9), printed p.942.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- Original13.7.10(9), on the unchanged seed and conjugate seed span. -/
theorem pair_seed_complement
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let U:=Section08.Source.UH H V₃
    let W:=conjugate U (g:G)⊓V₃
    Disjoint V₁ W ∧ V₁⊔W=V₃ ∧ Nat.card W=4 ∧
      W=conjugate V₃ (g:G)⊓V₃ ∧
      V₃≤Section08.Source.VH H V⊓conjugate (Section08.Source.VH H V) (g:G) := by
  dsimp only
  let U:=Section08.Source.UH H V₃
  let Ug:=conjugate U (g:G)
  let Zg:=conjugate V₃ (g:G)
  let W:=Ug⊓V₃
  have hpoint:V₁≤V₃:=h.point_lt.le
  have hgV:conjugate V (g:G)=V:=mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (V:Set G)).inv_mem (d.normalizes_V g.property))
  have hZg:Zg≤V:=(map_mono d.seed_le).trans hgV.le
  have hZgU:Zg≤Ug:=map_mono (le_conjugateSpanBy V₃ H)
  have hnot:¬V₁≤Ug := by
    intro he
    have hm:=map_mono (f:=(MulAut.conj (g:G)⁻¹).toMonoidHom) he
    change conjugate V₁ (g:G)≤conjugate (conjugate (conjugateSpanBy V₃ H) (g:G)) (g:G) at hm
    rw [h.conjugate_twice_eq_of_square (le_normalizer_conjugateSpanBy V₃ H)
      (h.square_mem_local_of_core_quotient_square g hs)] at hm
    exact hout hm
  have hd:Disjoint V₁ W := by
    apply disjoint_iff.mpr
    have hc:Nat.card (V₁⊓W:Subgroup G)∣2:=d.line_card ▸ card_dvd_of_le (show V₁⊓W≤V₁ from inf_le_left)
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hc with hc|hc
    · exact eq_bot_of_card_eq _ hc
    · have he:V₁⊓W=V₁:=eq_of_le_of_card_ge inf_le_left (by rw [hc,d.line_card])
      exact (hnot (he.symm.le.trans (inf_le_right.trans inf_le_left))).elim
  let :IsMulCommutative V:= (NaturalAction.elementary d).toIsMulCommutative
  have commute_sub (A B:Subgroup G) (ha:A≤V) (hb:B≤V):B≤centralizer (A:Set G) := by
    intro b hbb a haa
    exact congrArg Subtype.val (mul_comm (⟨a,ha haa⟩:V) ⟨b,hb hbb⟩)
  have hcardV:Nat.card V=16 := by
    calc
      Nat.card V=Nat.card (BinaryPermutation.natural (Fin 6)):=Nat.card_congr d.coordinate.toEquiv
      _=16:=by rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
          BinaryPermutation.finrank_natural_even (Fin 6) (by decide),Fintype.card_fin];norm_num
  have hcardZg:Nat.card Zg=8:= (card_map_of_injective (MulAut.conj (g:G)⁻¹).injective).trans d.seed_card
  have hn:Zg≤normalizer (V₃:Set G):=(commute_sub V₃ Zg d.seed_le hZg).trans (Subgroup.centralizer_le_normalizer _)
  have hmul:=card_mul_eq_card_inf_mul_card_sup_of_normalizes V₃ Zg hn
  have hsup:Nat.card (V₃⊔Zg:Subgroup G)≤16:=(card_le_of_le (sup_le d.seed_le hZg)).trans_eq hcardV
  rw [d.seed_card,hcardZg] at hmul
  have hlo:4≤Nat.card (V₃⊓Zg:Subgroup G):=by nlinarith
  have hsmall:V₃⊓Zg≤W:=le_inf (inf_le_right.trans hZgU) inf_le_left
  have hW:W≤V₃:=inf_le_right
  have hp:=card_sup_eq_mul_of_normalizes_of_disjoint V₁ W
    ((commute_sub V₁ W (hpoint.trans d.seed_le) (hW.trans d.seed_le)).trans (Subgroup.centralizer_le_normalizer _)) hd
  rw [d.line_card] at hp
  have hup:Nat.card (V₁⊔W:Subgroup G)≤8:=(card_le_of_le (sup_le hpoint hW)).trans_eq d.seed_card
  have hge:4≤Nat.card W:=hlo.trans (card_le_of_le hsmall)
  have hcard:Nat.card W=4:=by omega
  have heq:V₁⊔W=V₃:=eq_of_le_of_card_ge (sup_le hpoint hW) (by rw [hp,hcard,d.seed_card])
  have hsmallEq:V₃⊓Zg=W:=eq_of_le_of_card_ge hsmall (by rw [hcard];exact hlo)
  refine ⟨hd,heq,hcard,?_,?_⟩
  · exact hsmallEq.symm.trans (inf_comm V₃ Zg)
  · exact d.seed_le.trans (pair_intersection_layer d h hU g hout).1
end CFSG.Quasithin.Chapter13.Section07
