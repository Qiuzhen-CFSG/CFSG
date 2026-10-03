module
public import Stellmacher.SectionEight.LocalQuotientOddCoreSupplement
public import Stellmacher.SectionFiveToSeven.Result7_4
public import Stellmacher.QuotientModuleWitness


/-!
# Faithful local center actions and arbitrary Sylow supplements

At the initial vertex of a critical path satisfying the Section Seven
hypotheses, every exact faithful quotient acting on the elementary abelian
center module satisfies the standing Section One hypotheses. Its odd core
supplements the image of any Sylow two-subgroup of the vertex stabilizer.

The quotient image of the distinguished Sylow subgroup is nontrivial:
otherwise (7.4) identifies that Sylow subgroup with the vertex two-core,
contradicting membership in the local P-family. This proves even order of
the quotient. Local solvability, faithfulness of the witness action, and
the existing local quotient core theorem give the other hypotheses.
The known odd-core supplement for the distinguished Sylow image transfers
to every Sylow image by Sylow conjugacy and normality of the odd core.
All action-dependent conclusions retain the supplied witness action.

This is the setup for the hereditary application of (1.2) in Stellmacher
(9.3), Journal of Algebra 190 (1997), building on (7.4) and the local odd-core
supplement used in (9.2).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The faithful local center action satisfies Section One, with the odd
core supplement available for every supplied local Sylow subgroup. -/
public theorem local_quotient_sylow_action_setup
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    [IsElementaryAbelian 2 (ZAt Γ cp.a)]
    (w : QuotientModuleWitness (GAt Γ cp.a)
      (GAt Γ cp.a ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G)) (ZAt Γ cp.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt Γ cp.a) w.action
    SectionOne.Hypotheses w.X (ZAt Γ cp.a) ∧
      ∀ U : Sylow 2 (GAt Γ cp.a),
        SectionOne.oddCore w.X ⊔ (U : Subgroup (GAt Γ cp.a)).map w.projection = ⊤ := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt Γ cp.a) w.action
  let P := stabilizer Γ cp.a
  have hlocal := (SevenSix.edge_local_data h Γ cp).1
  let : Group.IsSolvable P := hlocal.2
  obtain ⟨_, sylow, hsylow⟩ := hlocal.1.1.2.1
  have hTP : T ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hnative : (sylow : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTP]
    exact hsylow
  let quotientSylow := sylow.mapSurjective w.surjective
  have hnontrivial : (quotientSylow : Subgroup w.X) ≠ ⊥ := by
    intro hbot
    apply hlocal.1.1.2.2.2
    have hTQ : T ≤ q Γ cp.a := by
      intro actor hactorT
      let lift : P := ⟨actor, hTP hactorT⟩
      have hlift : lift ∈ (sylow : Subgroup P) := by
        rw [hnative]
        exact hactorT
      have hkernel : lift ∈ w.projection.ker := by
        have himage : w.projection lift ∈ (quotientSylow : Subgroup w.X) :=
          Subgroup.mem_map_of_mem w.projection hlift
        rwa [hbot, Subgroup.mem_bot] at himage
      rw [w.kernel_eq] at hkernel
      change actor ∈ q Γ cp.a
      rw [← (lemma_seven_four h Γ cp).edge_centralizer]
      exact ⟨hactorT, hkernel.2⟩
    apply le_antisymm
    · simpa only [q, stabilizer, Γ.twoCoreAt_def] using hTQ
    · simpa only [q, stabilizer, Γ.twoCoreAt_def] using
        (SevenSix.local_cores_le_edge_sylow h Γ cp).1
  let : Nontrivial quotientSylow :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hnontrivial
  obtain ⟨exponent, hpositive, hcard⟩ :=
    quotientSylow.isPGroup'.nontrivial_iff_card.mp inferInstance
  have heven : Even (Nat.card w.X) := by
    apply even_iff_two_dvd.mpr
    apply (show 2 ∣ Nat.card quotientSylow by
      rw [hcard]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpositive)).trans
    exact Subgroup.card_subgroup_dvd_card _
  refine ⟨⟨Group.isSolvable_of_surjective w.surjective, heven,
    w.action_faithful, local_quotient_twoCore_eq_bot Γ cp.a w⟩, ?_⟩
  intro U
  let otherSylow := U.mapSurjective w.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq w.X quotientSylow otherSylow
  have hconj : (quotientSylow : Subgroup w.X).map (MulAut.conj g).toMonoidHom =
      (otherSylow : Subgroup w.X) := congrArg Sylow.toSubgroup hg
  have : (SectionOne.oddCore w.X).Normal := by
    change (pPrimeCore 2 w.X).Normal
    infer_instance
  have hsup : SectionOne.oddCore w.X ⊔ (quotientSylow : Subgroup w.X) = ⊤ := by
    change SectionOne.oddCore w.X ⊔ (sylow : Subgroup P).map w.projection = ⊤
    rw [hnative]
    exact local_quotient_oddCore_sup_sylow h Γ cp w
  have hmap := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hsup
  have hnormalmap : (SectionOne.oddCore w.X).map (MulAut.conj g).toMonoidHom =
      SectionOne.oddCore w.X := Subgroup.Normal.map_conj_eq _ g
  rw [Subgroup.map_sup, hnormalmap, hconj,
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at hmap
  exact hmap

end Stellmacher.SectionEight
