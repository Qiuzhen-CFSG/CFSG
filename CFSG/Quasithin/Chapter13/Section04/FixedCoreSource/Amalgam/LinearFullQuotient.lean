module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearParabolicPair
public import Theory.SpecificGroups.PSL3Two.NormalExtension
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterCentralizerGeneration
public import Theory.SpecificGroups.PSL3Two.NonSolvable

/-!
# The full quotient of the original linear amalgam

A Goldschmidt triple cannot generate Aut(L₃(2)). Each solvable vertex
contains an ambient Sylow two-subgroup and is not a two-group. An outer
automorphism in it would force it to contain the nonsolvable inner group.
Thus both vertices would lie in the proper inner group, contradicting generation.
The actual normal-component extension dichotomy therefore identifies the whole
original two-core quotient with L₃(2), excluding the graph extension.

This supplies the full actor needed for the two fixed-line orbit comparison.
Source1332OneTwo retains its earlier producer and final discharge in the fixed-core
assembly. Source: Aschbacher–Smith 13.4.7, printed pp.900–901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

private theorem no_linear_automorphism_triple
    {A B : Subgroup (MulAut Matrix.PSL3Two.SL)} (h : ChapterF.IsGoldschmidtTriple A B) : False := by
  let I := MulAut.innerSubgroup Matrix.PSL3Two.SL
  obtain ⟨S,hS⟩ := h.intersection_sylow
  have step (P Q : Subgroup (MulAut Matrix.PSL3Two.SL))
      (hp : ChapterF.IsGoldschmidtTriple P Q) (hSP : (S : Subgroup _) ≤ P) : P ≤ I := by
    have hn : ¬ IsPGroup 2 P := by
      intro hh
      let q := QuotientGroup.mk' (pCore 2 P)
      have ht : IsPGroup 2 (Equiv.Perm (Fin 3)) :=
        (hh.of_surjective q (QuotientGroup.mk'_surjective _)).of_equiv hp.quotient_left.some
      obtain ⟨n,hn⟩ := ht.exists_card_eq
      have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
        norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
      have hd : 3 ∣ 2 ^ n := hn ▸ (hc ▸ (by decide : 3 ∣ 6))
      exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
    intro a ha
    by_contra hai
    have hIP := Matrix.PSL3Two.Automorphisms.OuterCentralizerGeneration.inner_le_of_sylow_le_of_not_isTwoGroup
      S P hSP hn a ha hai
    let j : Matrix.PSL3Two.SL →* P := MulAut.conj.codRestrict P (fun x => hIP ⟨x,rfl⟩)
    have hj : Function.Injective j := fun x y hxy =>
      (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot) (congrArg Subtype.val hxy)
    let := hp.local_solvable
    exact not_isSolvable_sl3_two (Group.isSolvable_of_isSolvable_injective hj)
  have hi : I = ⊤ := top_unique (by
    rw [←h.generated]
    exact sup_le (step A B h (hS.symm.le.trans inf_le_left))
      (step B A h.symm (hS.symm.le.trans inf_le_right)))
  have hc := Matrix.PSL3Two.Automorphisms.card_outer_sl
  change I.index = 2 at hc
  rw [hi,index_top] at hc
  omega

open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The whole two-core quotient is linear, with no graph automorphism extension. -/
theorem original_pair_linear_full_quotient
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    Nonempty (((A ⊔ B : Subgroup G) ⧸ pCore 2 (A ⊔ B : Subgroup G)) ≃* Matrix.PSL3Two.PSL) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let S : Sylow 2 X := T.subtype (hTA.trans le_sup_left)
  let : K.Normal := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).1
  have hgen : K ⊔ (S : Subgroup X) = ⊤ := by
    rw [←(original_pair_component_is_residual h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1]
    exact pResidual_sup_sylow_eq_top S
  let j := K.equivMapOfInjective X.subtype X.subtype_injective
  let jq := QuotientGroup.congr (pCore 2 K) (pCore 2 C) j (pCore_map_iso 2 j)
  let k := ((jq.trans eK).trans Matrix.PSL3Two.equiv.symm).trans
    (BinaryLinear.OuterCyclic.slEquivLinear 3)
  rcases BinaryLinear.NormalThreeExtension.quotient K (S : Subgroup X) k S.isPGroup' hgen
    with hn | ha
  · obtain ⟨e⟩ := hn
    exact ⟨(e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).trans Matrix.PSL3Two.equiv⟩
  · obtain ⟨e⟩ := ha
    let t := e.trans (MulAut.congr (BinaryLinear.OuterCyclic.slEquivLinear 3).symm)
    have ht := ((pair_goldschmidt hTA hTB eA eB hne).quotient_twoCore).map_of_two_kernel
      t.toMonoidHom t.surjective (IsPGroup.ker_isPGroup_of_injective t.injective)
      (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact bot_le)
    exact (no_linear_automorphism_triple ht).elim


/-- The actual component fills the whole two-core quotient. In particular
its two-core supplement in the original join is exactly the original join. -/
theorem original_pair_linear_core_supplement
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let X := A ⊔ B
    let q := QuotientGroup.mk' (pCore 2 X)
    K.map q = ⊤ ∧ K.map X.subtype ⊔ X.pCoreIn 2 = X := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let q := QuotientGroup.mk' (pCore 2 X)
  obtain ⟨eqX⟩ := original_pair_linear_full_quotient h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  obtain ⟨eqK,_⟩ := (original_pair_component_twoCore_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2.2.2.1
  let j := K.equivMapOfInjective X.subtype X.subtype_injective
  let jq := QuotientGroup.congr (pCore 2 K) (pCore 2 C) j (pCore_map_iso 2 j)
  have hc : Nat.card (K.map q) = Nat.card (X ⧸ pCore 2 X) :=
    (Nat.card_congr eqK.toEquiv).symm.trans
      ((Nat.card_congr (jq.trans eK).toEquiv).trans (Nat.card_congr eqX.toEquiv).symm)
  have ht : K.map q = ⊤ := (K.map q).eq_top_of_card_eq hc
  have hg : K ⊔ pCore 2 X = ⊤ := by
    have hh := congrArg (Subgroup.comap q) ht
    rwa [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
  have hh := congrArg (Subgroup.map X.subtype) hg
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
  exact ⟨ht,hh⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
