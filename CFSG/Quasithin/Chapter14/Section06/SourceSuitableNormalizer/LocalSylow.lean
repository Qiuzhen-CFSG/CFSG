module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableNormalizer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The local Sylow clause from the suitable normalizer condition

The source condition N_Mc(T₀) = T forces T₀ to be Sylow in the literal
quotient centralizer C_H(ũ): its normalizer in that group is T₀ itself.
The central commutator character x ↦ [u,x] then identifies C_H(u) with
a normal subgroup of C_H(ũ). Sylow restriction gives Tᵤ ∈ Syl₂(C_H(u)).

Thus the local Sylow assertion in (U1) follows from (U0) and (U3) in the
original rank-two setup. The final theorem applies the completed 14.6.3(4)
with this assertion discharged, retaining the original index, movement
and local-normalizer hypotheses.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, (U0)--(U3), Lemma 14.6.3(4), printed pp.1021--1022;
the same Sylow restriction is used in Lemma 14.6.24(1), printed p.1039.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

/-- The original local normalizer condition forces the quotient-centralizer Sylow clause. -/
theorem suitable_quotient_sylow_of_local_normalizer (u : G)
    (Mc : Subgroup G) (hHMc : D.H ≤ Mc)
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer h u : Set G) =
      (D.T : Subgroup G)) :
    Chapter1.IsSylowIn 2 (suitableQuotientCentralizer h u) (h.kernel (zpowers u)) := by
  let K := h.kernel (zpowers u)
  let T0 := suitableQuotientCentralizer h u
  have hKK : K ≤ Mc := (map_subtype_le _).trans hHMc
  have hT0K : T0 ≤ K := inf_le_right
  have hn : normalizer (T0.subgroupOf K : Set K) = T0.subgroupOf K := by
    rw [← subgroupOf_normalizer_eq hT0K]
    ext x
    change (x : G) ∈ normalizer (T0 : Set G) ↔ (x : G) ∈ T0
    constructor
    · intro hx
      exact ⟨hU3 ▸ (show (x : G) ∈ Mc ⊓ normalizer (T0 : Set G) from
        ⟨hKK x.property,hx⟩),x.property⟩
    · exact fun hx => T0.le_normalizer hx
  obtain ⟨S,hS⟩ := exists_sylow_eq_of_isPGroup_of_normalizer_eq (T0.subgroupOf K)
    (D.T.isPGroup'.to_le (show T0 ≤ (D.T : Subgroup G) from inf_le_left)).comap_subtype hn
  exact ⟨S,by rw [hS,map_subgroupOf_eq_of_le hT0K]⟩

private def quotientCentralizerCharacter (u : G) (hu : u ∈ D.UH) :
    h.kernel (zpowers u) →* D.V₁ where
  toFun x := ⟨⁅u,(x : G)⁆,
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp x.property).2
      u (mem_zpowers u)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    change ⁅u,(a : G) * (b : G)⁆ = ⁅u,(a : G)⁆ * ⁅u,(b : G)⁆
    have ha := ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp a.property).1
    have hb := ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp b.property).2
      u (mem_zpowers u)
    have hc := h.H_centralizes ha _ hb
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅u,(a : G)⁆ * ((a : G) * ⁅u,(b : G)⁆) * (a : G)⁻¹ := by group
      _ = _ := by rw [← hc]; group

/-- Restrict the quotient-centralizer Sylow subgroup through the central commutator character. -/
theorem suitable_local_sylow_of_quotient_sylow (u : G) (hu : u ∈ D.UH)
    (hs : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer h u) (h.kernel (zpowers u))) :
    Chapter1.IsSylowIn 2 (suitableCentralizer (D := D) u)
      (D.H ⊓ centralizer ({u} : Set G)) := by
  let K := h.kernel (zpowers u)
  let C := D.H ⊓ centralizer ({u} : Set G)
  have hCK : C ≤ K := by
    intro x hx
    apply (h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mpr
    refine ⟨hx.1,?_⟩
    have hx' : x ∈ centralizer (zpowers u : Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
      exact hx.2
    intro a ha
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx' a ha)]
    exact D.V₁.one_mem
  let f := quotientCentralizerCharacter h u hu
  have hker : f.ker = C.subgroupOf K := by
    ext x
    change (⟨⁅u,(x : G)⁆,_⟩ : D.V₁) = 1 ↔
      ((x : G) ∈ D.H ∧ (x : G) ∈ centralizer ({u} : Set G))
    rw [Subtype.ext_iff]
    change ⁅u,(x : G)⁆ = 1 ↔
      ((x : G) ∈ D.H ∧ (x : G) ∈ centralizer ({u} : Set G))
    rw [commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff]
    have hx := ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp x.property).1
    simp only [hx,true_and]
    exact eq_comm
  have hn : (C.subgroupOf K).Normal := hker ▸ inferInstance
  have hi := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs hCK hn.isSubnormal
  have he : suitableQuotientCentralizer h u ⊓ C = suitableCentralizer (D := D) u := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    · intro x hx
      have hxC : x ∈ C := ⟨h.T_le_H hx.1,hx.2⟩
      exact ⟨⟨hx.1,hCK hxC⟩,hxC⟩
  rwa [he] at hi

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)

include hG hempty hM hunique hmany hcard e hab H hH hu

/-- The local Sylow assertion in (U1) follows from the source hypotheses and (U3). -/
theorem source_suitable_local_sylow
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)) := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  exact suitable_local_sylow_of_quotient_sylow h u hu
    (suitable_quotient_sylow_of_local_normalizer h u Mc hHMc hU3)

/-- Original 14.6.3(4), with the local Sylow assertion of (U1) proved internally. -/
theorem source_suitable_normalizer_of_local_normalizer
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G)) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    normalizer (Tu : Set G) = suitableQuotientCentralizer h u ∧
      Chapter1.IsSylowIn 2 Tu (centralizer ({u} : Set G)) ∧
      ¬∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({u} : Set G) := by
  exact source_lemma_14_6_3_4 hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct hU3
    (source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab H hH u hu hU3)

end CFSG.Quasithin.Chapter14.Section06
