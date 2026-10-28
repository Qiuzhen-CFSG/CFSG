module

public import CFSG.Quasithin.Chapter13.Section07.PairTransport

/-!
# An internal conjugator squaring into the original core

In the order-six quotient, multiplying an arbitrary conjugator by the
first transposition if necessary makes its square trivial. Lifting that
adjustment inside the first original span keeps the same H-coset and hence
every H-normalized subgroup marking. Its square belongs to the original
ambient two-core. This permits simultaneous exchange of the two literal
D-intersections without assuming the originally selected g lies in I.
Source: Aschbacher--Smith13.7.10(5), printed pp.941--942.
-/

public section

open Subgroup
open scoped IsMulCommutative
private theorem symmetricThree_adjust_square :
    ∀s t:Equiv.Perm (Fin 3),t^2=1→t≠1→s^2=1∨(s*t)^2=1 := by decide +kernel
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- An internal source conjugator can square into the original ambient two-core. -/
theorem pair_internal_square_conjugator
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    ∃x:(Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G):Subgroup G),
      (x:G)^2∈(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2 ∧
      ∀K:Subgroup G,H≤normalizer (K:Set G)→conjugate K (g:G)=K.conjBy (x:G) := by
  let X:=L⊔(T:Subgroup G)
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let I:=A⊔B
  let Q:=X.pCoreIn 2
  obtain ⟨hc,⟨e⟩⟩:=pair_twoCore_quotient d h hU hV g hout
  have hcore:pCore 2 I=Q.subgroupOf I := by
    apply map_injective I.subtype_injective
    exact hc.trans ((inf_comm I Q).trans (subgroupOf_map_subtype Q I).symm)
  let f:I→*Equiv.Perm (Fin 3):=e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hk:f.ker=pCore 2 I:=(MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  let AI:=A.subgroupOf I
  have hcard:Nat.card (AI.map f)=2 := by
    rw [←relIndex_ker AI f,hk,hcore,relIndex_subgroupOf (show A≤I from le_sup_left)]
    exact (nonabelian_core_indices d h hU hV).1
  have hne:AI.map f≠⊥:=by intro he;rw [he] at hcard;simp at hcard
  obtain ⟨t,ht,ht1⟩:=SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have htne:t≠1:=by simpa only [mem_bot] using ht1
  have htt:=ht
  obtain ⟨a,ha,hat⟩:=ht
  have ht2:t^2=1 := by
    have hp:=pow_card_eq_one' (x:=(⟨t,htt⟩:AI.map f))
    rw [hcard] at hp
    exact congrArg Subtype.val hp
  obtain ⟨x,_,hx⟩:=pair_internal_marked_conjugator d h hU hV g hout
  have square (y:I) (hy:(f y)^2=1):(y:G)^2∈Q := by
    have hyk:y^2∈f.ker:=by rw [MonoidHom.mem_ker,map_pow];exact hy
    have hq:y^2∈Q.subgroupOf I:=(hk.trans hcore) ▸ hyk
    exact hq
  rcases symmetricThree_adjust_square (f x) t ht2 htne with hs|hs
  · exact ⟨x,square x hs,hx⟩
  · refine ⟨x*a,square (x*a) ?_,?_⟩
    · rwa [map_mul,hat]
    · intro K hK
      have haH:(a:G)∈H:=h.VH_le_H ha
      have he:K.conjBy (a:G)=K:=mem_normalizer_iff_map_conj_eq.mp (hK haH)
      change conjugate K (g:G)=K.conjBy ((x:G)*(a:G))
      rw [conjBy_mul,he]
      exact hx K hK
end CFSG.Quasithin.Chapter13.Section07
