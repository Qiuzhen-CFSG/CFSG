module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductMarkedThompson
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductAssembly
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductMarkedEmbedding

/-!
# TerminalProductMarkedThompson at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductMarkedThompson`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Stellmacher

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem second_le_Y_thompson_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.L2 ≤ elementaryAbelianMaxJ P.Y := by
  rw [←P.L2_thompson_at structural escape C,commutator_comm]
  exact (commutator_mono P.sylow_thompson_le_Y_thompson le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      (P.second_le_Y.trans P.Y_normalizes_thompson))

theorem marked_thompson_contains_residual_product_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (alternatingGroup (Fin 5)).prod (alternatingGroup (Fin 3)) ≤
      ((elementaryAbelianMaxJ P.Y).subgroupOf P.Y).map (P.markedProductAction_at structural escape C) := by
  have hK : (alternatingGroup (Fin 5)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) ≤
      ((elementaryAbelianMaxJ P.Y).subgroupOf P.Y).map (P.markedProductAction_at structural escape C) := by
    rw [←P.markedProductAction_first_image_at structural escape C]
    exact map_mono (subgroupOf_mono _ (P.component_le_Y_thompson C))
  have hR : (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3)) ≤
      ((elementaryAbelianMaxJ P.Y).subgroupOf P.Y).map (P.markedProductAction_at structural escape C) := by
    rw [←P.markedProductAction_second_image_at structural escape C]
    exact map_mono (subgroupOf_mono _ (P.second_le_Y_thompson_at structural escape C))
  rintro ⟨a,b⟩ ⟨ha,hb⟩
  have h := Subgroup.mul_mem _ (hK (show (a,1) ∈
    (alternatingGroup (Fin 5)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) from ⟨ha,one_mem _⟩))
    (hR (show (1,b) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3)) from
      ⟨one_mem _,hb⟩))
  simpa only [Prod.mk_mul_mk,mul_one,one_mul] using h

theorem productAnalysis_of_markedThompson_surjective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (hfull : Function.Surjective ((P.markedProductAction_at structural escape C).comp
      ((elementaryAbelianMaxJ P.Y).subgroupOf P.Y).subtype)) : Nonempty P.ProductAnalysis := by
  let f := P.markedProductAction_at structural escape C
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨j,hj⟩ := hfull a
    exact ⟨j,hj⟩
  have hq : Function.Surjective (P.markedQuotientEmbedding_at structural escape C) := by
    intro a
    obtain ⟨y,hy⟩ := hf a
    exact ⟨QuotientGroup.mk' (pCore 2 P.Y) y,hy⟩
  let e := MulEquiv.ofBijective (P.markedQuotientEmbedding_at structural escape C)
    ⟨P.markedQuotientEmbedding_injective_at structural escape C,hq⟩
  have he : e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y)) = f := by
    apply MonoidHom.ext
    intro y
    rfl
  apply P.productAnalysis_of_marked_quotient_at structural escape C e
  · rw [he]
    exact P.markedProductAction_first_image_at structural escape C
  · rw [he]
    exact P.markedProductAction_second_image_at structural escape C
  · rw [he]
    have h := MonoidHom.range_eq_top.mpr hfull
    rwa [MonoidHom.range_comp,range_subtype] at h

theorem false_of_markedThompson_surjective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (hfull : Function.Surjective ((P.markedProductAction_at structural escape C).comp
      ((elementaryAbelianMaxJ P.Y).subgroupOf P.Y).subtype)) : False := by
  obtain ⟨A⟩ := P.productAnalysis_of_markedThompson_surjective_at structural escape C hfull
  exact P.false_of_module_analysis_at structural A

theorem secondYAction_thompson_surjective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    Function.Surjective ((P.secondYAction_at structural escape C).comp
      ((elementaryAbelianMaxJ P.Y).subgroupOf P.Y).subtype) := by
  let J := (elementaryAbelianMaxJ P.Y).subgroupOf P.Y
  let q := (P.secondYAction_at structural escape C).comp J.subtype
  have hA : alternatingGroup (Fin 3) ≤ q.range := by
    rw [MonoidHom.range_comp,range_subtype,←P.secondYAction_second_image_at structural escape C]
    exact map_mono (subgroupOf_mono _ (P.second_le_Y_thompson_at structural escape C))
  obtain ⟨j,hj,hj2,hj1⟩ := P.exists_thompson_second_involution_at structural escape
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) := sSup_le fun _ h => h.1
  let t : J := ⟨⟨j,P.sylow_le_Y (hJT hj)⟩,P.sylow_thompson_le_Y_thompson hj⟩
  have ht : q t = (P.pointBlockAction j).2 := P.secondYAction_agrees_at structural escape C _ j.property
  have htodd : q t ∉ alternatingGroup (Fin 3) := by
    rw [ht]
    intro h
    let a : alternatingGroup (Fin 3) := ⟨(P.pointBlockAction j).2,h⟩
    have hd3 : orderOf a ∣ 3 := by
      have hh := orderOf_dvd_natCard a
      rw [nat_card_alternatingGroup,Nat.card_fin] at hh
      exact hh
    have hd2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext hj2)
    have he : a = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 2) hd3 hd2)
    exact hj1 (congrArg Subtype.val he)
  intro a
  by_cases ha : a ∈ alternatingGroup (Fin 3)
  · exact hA ha
  · have ham : a * (q t)⁻¹ ∈ alternatingGroup (Fin 3) := by
      rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two,inv_mem_iff]
      exact iff_of_false ha htodd
    obtain ⟨x,hx⟩ := hA ham
    exact ⟨x*t,by rw [map_mul,hx,inv_mul_cancel_right]⟩

theorem markedThompson_surjective_of_independent_actor_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (t : P.Y) (htJ : (t : G) ∈ elementaryAbelianMaxJ P.Y)
    (htfirst : P.firstYAction C t ∉ alternatingGroup (Fin 5))
    (htsecond : P.secondYAction_at structural escape C t = 1) :
    Function.Surjective ((P.markedProductAction_at structural escape C).comp
      ((elementaryAbelianMaxJ P.Y).subgroupOf P.Y).subtype) := by
  let J := (elementaryAbelianMaxJ P.Y).subgroupOf P.Y
  let f := (P.markedProductAction_at structural escape C).comp J.subtype
  let tJ : J := ⟨t,htJ⟩
  have hbase : (alternatingGroup (Fin 5)).prod (alternatingGroup (Fin 3)) ≤ f.range := by
    rw [MonoidHom.range_comp,range_subtype]
    exact P.marked_thompson_contains_residual_product_at structural escape C
  have hpure (a : Equiv.Perm (Fin 5)) : (a,1) ∈ f.range := by
    by_cases ha : a ∈ alternatingGroup (Fin 5)
    · exact hbase ⟨ha,one_mem _⟩
    · have ham : a * (P.firstYAction C t)⁻¹ ∈ alternatingGroup (Fin 5) := by
        rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two,inv_mem_iff]
        exact iff_of_false ha htfirst
      have hm := f.range.mul_mem (hbase (show (a * (P.firstYAction C t)⁻¹,1) ∈
        (alternatingGroup (Fin 5)).prod (alternatingGroup (Fin 3)) from ⟨ham,one_mem _⟩))
        (show f tJ ∈ f.range from ⟨tJ,rfl⟩)
      change (a * (P.firstYAction C t)⁻¹ * P.firstYAction C t,
        1 * P.secondYAction_at structural escape C t) ∈ f.range at hm
      simpa only [htsecond,mul_one,inv_mul_cancel_right] using hm
  intro a
  obtain ⟨x,hx⟩ := P.secondYAction_thompson_surjective_at structural escape C a.2
  have hm := f.range.mul_mem (hpure (a.1 * (f x).1⁻¹)) (show f x ∈ f.range from ⟨x,rfl⟩)
  have he : (a.1 * (f x).1⁻¹,1) * f x = a := by
    apply Prod.ext
    · simp only [Prod.fst_mul,inv_mul_cancel_right]
    · exact (one_mul (f x).2).trans hx
  rwa [he] at hm

theorem productAnalysis_of_independent_thompson_actor_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (t : P.Y) (htJ : (t : G) ∈ elementaryAbelianMaxJ P.Y)
    (htfirst : P.firstYAction C t ∉ alternatingGroup (Fin 5))
    (htsecond : P.secondYAction_at structural escape C t = 1) : Nonempty P.ProductAnalysis :=
  P.productAnalysis_of_markedThompson_surjective_at structural escape C
    (P.markedThompson_surjective_of_independent_actor_at structural escape C t htJ htfirst htsecond)

theorem false_of_independent_thompson_actor_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (t : P.Y) (htJ : (t : G) ∈ elementaryAbelianMaxJ P.Y)
    (htfirst : P.firstYAction C t ∉ alternatingGroup (Fin 5))
    (htsecond : P.secondYAction_at structural escape C t = 1) : False := by
  obtain ⟨A⟩ := P.productAnalysis_of_independent_thompson_actor_at structural escape C t htJ htfirst htsecond
  exact P.false_of_module_analysis_at structural A

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

