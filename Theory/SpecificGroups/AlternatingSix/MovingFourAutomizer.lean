module
public import Theory.SpecificGroups.AlternatingSix.M10.InvolutionAlignment
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.PGLComparison
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.FourMovementSource
/-! # A₆ automizers moving an inner four-group
The three index-two overgroups of Inn(A₆) are the natural S₆, the concrete
M₁₀ and the exceptional PGL₂(9). Two index-two membership tests distinguish
the latter two. In a two-group action containing an inner Sylow D₈, genuine
movement of one of its four-groups escapes the natural S₆, by the marked
32-element Sylow geometry. All model identifications use the actual carriers.
Source: Aschbacher--Smith 2.5.16(3), printed p.560.
-/
public section
open Subgroup AlternatingSix.ShadowLocal GLS3.Chapter5
namespace AlternatingSix
private theorem canonical_order : orderOf canonicalExceptionalAut=2 := by
  apply orderOf_eq_prime
  · rw [canonicalExceptionalAut,exceptionalTwistAut_square]
    have hp:outerHom canonicalTwistPerm*outerSquareConjugator*canonicalTwistPerm=1:=by
      decide +kernel
    rw [hp,map_one]
  · intro he
    apply outerAltAut_not_mem_natural
    have hh:outerAltAut=(MulAut.conjNormal canonicalTwistPerm)⁻¹:=by
      apply eq_inv_of_mul_eq_one_left
      exact he
    rw [hh]
    exact natural.inv_mem ⟨canonicalTwistPerm,rfl⟩
private theorem canonical_not_natural : canonicalExceptionalAut∉natural := by
  intro h
  apply outerAltAut_not_mem_natural
  have hh:=natural.mul_mem h (natural.inv_mem (show (MulAut.conjNormal canonicalTwistPerm:AutA6)∈natural from ⟨_,rfl⟩))
  simpa only [canonicalExceptionalAut,exceptionalTwistAut,mul_inv_cancel_right] using hh
private theorem canonical_not_m10 : canonicalExceptionalAut∉M10.extension := by
  intro h
  exact canonical_not_natural (inner_le_natural (M10.InvolutionAlignment.involution_mem_inner _ canonical_order h))

private theorem intermediate_index_two (A:Subgroup AutA6) (hA:ShadowLocal.inner≤A)
    (hne:A≠ShadowLocal.inner) (htop:A≠⊤) : A.index=2 := by
  have hm:=relIndex_mul_index hA
  rw [inner_index] at hm
  have hr1:ShadowLocal.inner.relIndex A≠1:=by
    intro h
    exact hne (le_antisymm (relIndex_eq_one.mp h) hA)
  have hi1:A.index≠1:=fun h=>htop (index_eq_one.mp h)
  have hr2:2≤ShadowLocal.inner.relIndex A:=by
    have hr0:ShadowLocal.inner.relIndex A≠0:=by intro h;rw [h,zero_mul] at hm;omega
    omega
  have hi2:2≤A.index:=by
    have hi0:A.index≠0:=by intro h;rw [h,mul_zero] at hm;omega
    omega
  have hh:=Nat.mul_le_mul_right A.index hr2
  rw [hm] at hh
  omega
private theorem card_of_index_two (A:Subgroup AutA6) (hi:A.index=2) : Nat.card A=720 := by
  have hh:=A.card_mul_index
  rw [hi,ShadowLocal.card_aut] at hh
  omega
private theorem inf_eq_inner (A B:Subgroup AutA6) (ha:ShadowLocal.inner≤A)
    (hb:ShadowLocal.inner≤B) (hA:A.index=2) (hB:B.index=2) (hne:A≠B) :
    A⊓B=ShadowLocal.inner := by
  by_contra hh
  have hnot:A⊓B≠⊤:=by
    intro ht
    have he:A=⊤:=top_unique (ht ▸ (show A⊓B≤A from inf_le_left))
    simp [he] at hA
  have hi:=intermediate_index_two (A⊓B) (le_inf ha hb) hh hnot
  have he:A⊓B=A:=eq_of_le_of_card_ge inf_le_left (by
    rw [card_of_index_two _ hi,card_of_index_two _ hA])
  apply hne
  apply eq_of_le_of_card_ge
  · exact he ▸ inf_le_right
  · rw [card_of_index_two _ hA,card_of_index_two _ hB]
private theorem canonical_card : Nat.card OuterInvolutionExtension.canonicalExtension=720 := by
  obtain ⟨e⟩:=OuterInvolutionExtension.canonicalExtension_equiv_pgl2
  rw [Nat.card_congr e.toEquiv,GorensteinWalter.pgl2_card_formula,Atlas.Comparisons.Exceptional.Nine.card]
  norm_num

theorem overgroup_not_natural_alternatives (A:Subgroup AutA6) (hA:ShadowLocal.inner≤A)
    (hn:¬A≤natural) :
    A=M10.extension ∨ A=OuterInvolutionExtension.canonicalExtension ∨ A=⊤ := by
  by_cases ht:A=⊤
  · exact Or.inr (Or.inr ht)
  by_cases he:A=M10.extension
  · exact Or.inl he
  have hne:A≠ShadowLocal.inner:=fun h=>hn (h ▸ inner_le_natural)
  have hi:=intermediate_index_two A hA hne ht
  have hin:A⊓natural=ShadowLocal.inner:=inf_eq_inner A natural hA inner_le_natural
    hi naturalAlternatingAutomorphismSubgroup_index (fun h=>hn h.le)
  have hie:A⊓M10.extension=ShadowLocal.inner:=inf_eq_inner A M10.extension hA
    M10.Action.inner_le_extension hi M10.Action.extension_index he
  right;left
  apply eq_of_le_of_card_ge
  · intro x hx
    by_cases hxi:x∈ShadowLocal.inner
    · exact mem_sup_left hxi
    have hxn:x∉natural:=by intro h;exact hxi (hin ▸ (show x∈A⊓natural from ⟨hx,h⟩))
    have hxe:x∉M10.extension:=by intro h;exact hxi (hie ▸ (show x∈A⊓M10.extension from ⟨hx,h⟩))
    have hd:x*canonicalExceptionalAut⁻¹∈ShadowLocal.inner:=by
      rw [←M10.Action.extension_inf_natural]
      constructor
      · exact (M10.extension.mul_mem_iff_of_index_two M10.Action.extension_index).mpr
          (iff_of_false hxe (by simpa using canonical_not_m10))
      · exact (natural.mul_mem_iff_of_index_two naturalAlternatingAutomorphismSubgroup_index).mpr
          (iff_of_false hxn (by simpa using canonical_not_natural))
    have hm:=OuterInvolutionExtension.canonicalExtension.mul_mem
      (mem_sup_left hd) (mem_sup_right (mem_zpowers canonicalExceptionalAut))
    simpa using hm
  · rw [canonical_card,card_of_index_two _ hi]
/-- The actual three model carriers for an overgroup escaping the natural S₆. -/
theorem overgroup_not_natural_models (A:Subgroup AutA6) (hA:ShadowLocal.inner≤A)
    (hn:¬A≤natural) :
    Nonempty (A≃*M10.extension) ∨
      Nonempty (A≃*GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∨
      Nonempty (A≃*AutA6) := by
  rcases overgroup_not_natural_alternatives A hA hn with h|h|h
  · exact Or.inl ⟨MulEquiv.subgroupCongr h⟩
  · obtain ⟨e⟩:=OuterInvolutionExtension.canonicalExtension_equiv_pgl2
    exact Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr h).trans e⟩)
  · exact Or.inr (Or.inr ⟨(MulEquiv.subgroupCongr h).trans topEquiv⟩)
end AlternatingSix

namespace AlternatingSix.ShadowLocal

theorem not_le_natural_of_four_movement (P:Sylow 2 A6)
    (A:Subgroup AutA6) (hA:IsPGroup 2 A)
    (hPA:(P:Subgroup A6).map MulAut.conj≤A)
    (F:Subgroup A6) [IsKleinFour F] (hFP:F≤P)
    (hmove:∃a∈A,F.map a.toMonoidHom≠F) : ¬A≤natural := by
  obtain ⟨Q,hAQ⟩:=hA.exists_le_sylow
  let E:=F.map (MulAut.conj:A6→*AutA6)
  have hEQ:E≤Q:=(map_mono hFP).trans (hPA.trans hAQ)
  let Eq:=E.subgroupOf (Q:Subgroup AutA6)
  let eF:=F.equivMapOfInjective (MulAut.conj:A6→*AutA6) inner_injective
  let : IsKleinFour E:={
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  let eE:=subgroupOfEquivOfLe hEQ
  let : IsKleinFour Eq:={
    card_four := (Nat.card_congr eE.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).trans IsKleinFour.exponent_two }
  have hED:Eq≤sylowInner Q:=by
    rintro d ⟨f,_,hf⟩
    exact ⟨f,hf⟩
  have hn:normalizer (Eq:Set Q)=sylowNatural Q:=by
    rcases SylowGeometry.kleinFour_subgroups_inner Q Eq hED with h|h
    · rw [h];exact SylowGeometry.normalizer_kleinZero Q
    · rw [h];exact SylowGeometry.normalizer_kleinOne Q
  intro hnat
  obtain ⟨a,ha,hm⟩:=hmove
  let aq:Q:=⟨a,hAQ ha⟩
  have haq:aq∈normalizer (Eq:Set Q):=hn ▸ hnat ha
  have hh:=congrArg (Subgroup.map (Q:Subgroup AutA6).subtype)
    (mem_normalizer_iff_map_conj_eq.mp haq)
  have hcomp:(Q:Subgroup AutA6).subtype.comp (MulAut.conj aq).toMonoidHom=
      (MulAut.conj a).toMonoidHom.comp (Q:Subgroup AutA6).subtype:=by ext x;rfl
  change (Eq.map (MulAut.conj aq).toMonoidHom).map (Q:Subgroup AutA6).subtype=Eq.map (Q:Subgroup AutA6).subtype at hh
  rw [map_map,hcomp,←map_map,map_subgroupOf_eq_of_le hEQ] at hh
  change E.map (MulAut.conj a).toMonoidHom=E at hh
  rw [FourNormalizers.inner_map_transport F a] at hh
  exact hm ((map_injective inner_injective) hh)
end AlternatingSix.ShadowLocal
