module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Unique maximality in a normal chi-zero block extension

For a Sylow two-subgroup S of a chi-zero block L, the full two-core lies in S.
Thus the actual quotient L/O₂(L) controls the overgroups of S. In A₃ the
trivial subgroup is the unique proper subgroup. In A₅ and even-field SL₂ the
unique maximal overgroup is a Borel; the A₅ case uses the proved isomorphism
SL₂(4) ≃ PSL₂(4) ≃ A₅. The elementary root-group calculation is provided by
`Theory.SpecificGroups.SL2.SylowUniqueMaximal`.

Relative normality gives Q ∩ L as a Sylow subgroup of L. Its unique maximal
overgroup is normalized by Q and extends to the unique maximal overgroup of Q
in LQ. All lifting is through the full O₂(L), so the possible central cover
in C.1.13(c) is retained. The natural-module and characteristic-two hypotheses
in the source contract are compatible with this more general quotient argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of E.6.14,
printed p.251 (PDF p.262), and C.1.12–13, printed pp.124–125.
-/

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection

private theorem sylow_equiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : ∀ S : Sylow 2 A, Order.HasUniqueMaximalOver (S : Subgroup A) ⊤)
    (S : Sylow 2 B) : Order.HasUniqueMaximalOver (S : Subgroup B) ⊤ := by
  have hh := (h (S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective)).map e.mapSubgroup
  rw [OrderIso.map_top] at hh
  change Order.HasUniqueMaximalOver
    (((S : Subgroup B).map e.symm.toMonoidHom).map e.toMonoidHom) ⊤ at hh
  simpa [map_map] using hh

private theorem a3_sylow (S : Sylow 2 (alternatingGroup (Fin 3))) :
    Order.HasUniqueMaximalOver (S : Subgroup (alternatingGroup (Fin 3))) ⊤ := by
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hScard : Nat.card S = 1 := S.isPGroup'.card_eq_or_dvd.resolve_right (by
    intro htwo
    have hh := htwo.trans (card_subgroup_dvd_card (S : Subgroup (alternatingGroup (Fin 3))))
    rw [hcard] at hh
    norm_num at hh)
  have hS : (S : Subgroup (alternatingGroup (Fin 3))) = ⊥ := card_eq_one.mp hScard
  rw [hS]
  have hbot : (⊥ : Subgroup (alternatingGroup (Fin 3))) ≠ ⊤ := by
    intro he
    have hh := congrArg (fun K : Subgroup (alternatingGroup (Fin 3)) => Nat.card K) he
    rw [card_bot, card_top, hcard] at hh
    omega
  have hp : Fact (Nat.Prime (Nat.card (alternatingGroup (Fin 3)))) := ⟨by rw [hcard]; decide⟩
  have hc : (⊥ : Subgroup (alternatingGroup (Fin 3))) ⋖ ⊤ := by
    apply IsCoatom.covBy_top
    apply isCoatom_iff_ge_of_le.mpr
    refine ⟨hbot, fun K hK _ => ?_⟩
    exact le_of_eq (K.eq_bot_or_eq_top_of_prime_card.resolve_right hK)
  refine ⟨lt_top_iff_ne_top.mpr hbot, ⊥, ⟨le_rfl, hc⟩, ?_⟩
  intro K hK
  exact K.eq_bot_or_eq_top_of_prime_card.resolve_right hK.2.ne

private theorem a5_sylow (S : Sylow 2 (alternatingGroup (Fin 5))) :
    Order.HasUniqueMaximalOver (S : Subgroup (alternatingGroup (Fin 5))) ⊤ := by
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  exact sylow_equiv ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).trans e)
    (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2) S

/-- Intrinsic Sylow unique maximality for every chi-zero block, with its full two-core retained. -/
public theorem chiZeroBlock_sylow_hasUniqueMaximalOver {L : Type*} [Group L] [Finite L]
    (h : ChapterC.IsChiZeroBlock L) (S : Sylow 2 L) :
    Order.HasUniqueMaximalOver (S : Subgroup L) ⊤ := by
  let π := QuotientGroup.mk' (pCore 2 L)
  apply hasUniqueMaximalOver_of_surjective π (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  · let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
    change Order.HasUniqueMaximalOver (Sb : Subgroup (L ⧸ pCore 2 L)) ⊤
    rcases h with ⟨n, _, _, F, _, _, hF, _, hm⟩ | h | h
    · obtain ⟨e⟩ := hm.quotient_iso
      let := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
        simpa only [Nat.card_eq_fintype_card] using hF)
      exact sylow_equiv e.symm (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2) Sb
    · obtain ⟨e⟩ := h.2.2.quotient_iso
      exact sylow_equiv e.symm a3_sylow Sb
    · obtain ⟨e⟩ := h.2.2.quotient_iso
      exact sylow_equiv e.symm a5_sylow Sb

/-- The intrinsic overgroup input used by the single-block assembly of E.6.14. -/
public theorem blockSylowMaximalInput {G : Type*} [Group G] [Finite G] : BlockSylowMaximalInput G := by
  intro Q H L _hc hQ hLH hn hL
  have hQH := (Chapter1.isSylowIn_iff.mp hQ).2.1
  obtain ⟨S, hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hQ hLH hn.isSubnormal
  have hu := hasUniqueMaximalOver_map_subtype (chiZeroBlock_sylow_hasUniqueMaximalOver hL S)
  rw [hS, inf_comm Q L] at hu
  apply hasUniqueMaximalOver_sup_of_normalizes _ hu
  exact hQH.trans ((normal_subgroupOf_iff_le_normalizer hLH).mp hn)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
