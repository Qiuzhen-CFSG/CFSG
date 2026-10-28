module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.BlockRecognition.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ModuleIrreducibility
public import Theory.SpecificGroups.SL2.CubicFixedVectors
/-!
# Irreducibility of the source derived natural actor

For fields larger than F₂ the derived actor is all of SL₂ and is transitive
on nonzero vectors. Over F₂ a cubic determinant-one matrix has no nonzero
fixed vector, excluding the only possible proper nonzero subgroup of the
four-group. This covers the actual derived actor in both source cases.

Source: Aschbacher–Smith C.1.17–18, printed p.126.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles.BlockRecognition
variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}
variable {F : Type} [Field F] [Finite F] [CharP F 2] (m : NaturalModel e F)

include m in
theorem derivedNatural_irreducible
    (W:Subgroup (Multiplicative (Fin 2→F)))
    (hW:∀a v,v∈W→derivedNaturalAction F a v∈W) : W=⊥∨W=⊤ := by
  have htwo : 2≤Nat.card F:=Finite.one_lt_card
  rcases htwo.eq_or_lt with h2|h2
  · have hc:Nat.card (commutator PSL(2,F))=3 :=
      (Nat.card_congr m.actorIso.toEquiv).symm.trans (m.actor_card_of_field_card_two e h2.symm)
    have hn : Nontrivial (commutator PSL(2,F)) := by
      apply not_subsingleton_iff_nontrivial.mp
      intro hs
      let := hs
      have hh:=Nat.card_of_subsingleton (1:commutator PSL(2,F))
      omega
    let := hn
    obtain ⟨a,ha⟩:=exists_ne (1:commutator PSL(2,F))
    have hao:orderOf a=3 := by
      let : Fact (Nat.Prime 3):=⟨Nat.prime_three⟩
      apply orderOf_eq_prime
      · rw [←hc];exact pow_card_eq_one'
      · exact ha
    let g:SL(2,F):=Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm a
    have hgo:orderOf g=3 := by
      rw [MulEquiv.orderOf_eq,orderOf_coe]
      exact hao
    have hVcard:Nat.card (Multiplicative (Fin 2→F))=4 := by
      change Nat.card (Fin 2→F)=4
      rw [Nat.card_fun,Nat.card_fin,←h2]
      norm_num
    have hd:Nat.card W∣2^2:=by simpa [hVcard] using W.card_subgroup_dvd_card
    obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases n
    · exact Or.inl (Subgroup.card_eq_one.mp (by simpa using he))
    · have hwcard:Nat.card W=2:=by simpa using he
      obtain ⟨w,hw,huniq⟩:=(Nat.card_eq_two_iff' (1:W)).mp hwcard
      let w':W:=⟨derivedNaturalAction F a w,hW a w w.property⟩
      have hw':w'≠1 := by
        intro hh
        apply hw
        apply Subtype.ext
        exact (derivedNaturalAction F a).injective
          ((congrArg Subtype.val hh).trans ((derivedNaturalAction F a).map_one).symm)
      have heq:w'=w := (huniq w' hw').trans (huniq w hw).symm
      have hv:g.val *ᵥ (w:Multiplicative (Fin 2→F)).toAdd=(w:Multiplicative (Fin 2→F)).toAdd :=
        congrArg Multiplicative.toAdd (congrArg Subtype.val heq)
      exact (hw (Subtype.ext (Multiplicative.toAdd.injective
        (Matrix.SL2.cubic_fixed_eq_zero g hgo _ hv)))).elim
    · exact Or.inr (eq_of_le_of_card_ge le_top (by rw [card_top,hVcard,he];norm_num))
  · apply Matrix.SL2.naturalAction_irreducible F W
    intro g v hv
    let a:commutator PSL(2,F):=⟨Atlas.RankOneFieldAutomorphisms.slEquivPSL g,
      by rw [derived_psl_eq_top_of_two_lt_card h2];trivial⟩
    have hh:=hW a v hv
    change Matrix.SL2.naturalAction F
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (Atlas.RankOneFieldAutomorphisms.slEquivPSL g)) v∈W at hh
    simpa only [MulEquiv.symm_apply_apply] using hh
end CFSG.Quasithin.ChapterC.GlaubermanNiles.BlockRecognition
