module

public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian
public import Stellmacher.SectionTwo.QuotientHypotheses
public import Stellmacher.SectionTwo.QuotientOffenders
public import Stellmacher.SectionTwo.QuotientModuleTransport
public import Stellmacher.SectionTwo.BaumannFixedPoints
public import Stellmacher.SectionOne.OffenderSelectedProduct
public import Stellmacher.SectionOne.OneSevenBaumann
public import Stellmacher.SectionOne.SL2FamilySylowCard
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import Stellmacher.DirectProductMap
public import Theory.GroupTheory.WeakClosureQuotient
public import Theory.GroupTheory.WeakClosureFrattini

/-!
# Stellmacher (2.2): the faithful quotient factor decomposition

For the quotient of `G` by the centralizer of the normal closure
`V = ⟨Ω₁(Z(S))^G⟩`, this module states the normal `SL₂(2)` factor
decomposition and the matching decomposition of `V` into four-element action
modules.  The two decompositions deliberately share one indexed family: the
same source factors `\bar E_i` occur in both parts (c) and (d).  Compatibility
projections retain the former `part_c` and `part_d` APIs.

The proof maps the actual maximal elementary subgroups of `S` into the
offender family for the named faithful quotient action. The proved local
`m ≤ 1` classification selects a subproduct of the global rank-one factors
from the (1.7) development. It is essential to use those offender generators:
an arbitrary subgroup of the global offender-generated subgroup need not
give such a subproduct. No unrestricted (1.6) claim is used.

Weak closure of the elementary Thompson subgroup descends to the quotient.
The Frattini argument then upgrades normality in the global factor product
to ambient normality. The Baumann image fixes the Thompson fixed space, so
it normalizes every selected factor and fixes the complementary module.
Faithfulness embeds its action into the four-element factor modules, bounding
its order by that of the Thompson image and proving equality. Injective
subtype transport gives the stated common ambient module decomposition.

The elementary-abelian and 2-core properties of `V` come from independent
Section 2 leaves. The scan on journal p. 20 confirms that the residual in `\bar E` is
`O_{2'}(\bar G)`; the unprimed `O_2` in
`refs/latex/stellmacher-n-group.tex` is a transcription error.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionTwo

universe u

public structure LemmaTwoTwoConclusion
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (barJ barB : Subgroup barG) : Prop where
  part_a :
    (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ).Normal
  part_b : barJ = barB
  parts_c_d :
    ∃ (n : ℕ) (E : Fin n → Subgroup barG) (Vf : Fin n → Subgroup G),
      (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ) = ⨆ i : Fin n, E i ∧
      IsInternalDirectProductFamily
        (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ) E ∧
      (∀ i : Fin n, IsSL2Two (↥(E i))) ∧
      (∀ i : Fin n, Vf i =
        ambientCommutator ((E i).comap q) (vSubgroup S) ∧ Nat.card (Vf i) = 4) ∧
      IsInternalDirectProductFamily (vSubgroup S)
        (fun i : Option (Fin n) =>
          match i with
          | none => vSubgroup S ⊓
              Subgroup.centralizer
                (((⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ).comap q : Subgroup G) : Set G)
          | some i => Vf i)

/-- The group-factor projection of the common factor/module decomposition in
parts (c) and (d) of Stellmacher (2.2). -/
public theorem LemmaTwoTwoConclusion.part_c
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (barJ barB : Subgroup barG)
    (h : LemmaTwoTwoConclusion S q barJ barB) :
    ∃ (n : ℕ) (E : Fin n → Subgroup barG),
      (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ) = ⨆ i : Fin n, E i ∧
      IsInternalDirectProductFamily
        (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ) E ∧
      ∀ i : Fin n, IsSL2Two (↥(E i)) := by
  rcases h.parts_c_d with ⟨n, E, _Vf, hE, hprod, hSL2, _hVf, _hVprod⟩
  exact ⟨n, E, hE, hprod, hSL2⟩

/-- The action-module projection of the common factor/module decomposition in
parts (c) and (d) of Stellmacher (2.2). -/
public theorem LemmaTwoTwoConclusion.part_d
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (barJ barB : Subgroup barG)
    (h : LemmaTwoTwoConclusion S q barJ barB) :
    ∃ (n : ℕ) (E : Fin n → Subgroup barG) (Vf : Fin n → Subgroup G),
      (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ) = ⨆ i : Fin n, E i ∧
      (∀ i : Fin n, Vf i =
        ambientCommutator ((E i).comap q) (vSubgroup S) ∧ Nat.card (Vf i) = 4) ∧
      IsInternalDirectProductFamily (vSubgroup S)
        (fun i : Option (Fin n) =>
          match i with
          | none => vSubgroup S ⊓
              Subgroup.centralizer
                (((⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ).comap q : Subgroup G) : Set G)
          | some i => Vf i) := by
  rcases h.parts_c_d with ⟨n, E, Vf, hE, _hprod, _hSL2, hVf, hVprod⟩
  exact ⟨n, E, Vf, hE, hVf, hVprod⟩

/-! **Stellmacher (2.2).**  Here `q : G → barG` is the quotient map with
kernel `C_G(V)`.  The bars in the paper denote images of the unbarred
subgroups `J(S)` and `B`, and `bar E` uses the odd core `O_{2'}(bar G)`.
Parts (c) and (d) retain one common family `E`: the source uses the same
`\bar E_i` both for the `SL₂(2)` direct factors and for the four-element
commutator modules.
-/
-- The named barS presentation is retained in the source-facing API even though
-- the conclusion uses only the images of J(S) and B.
set_option linter.unusedVariables false in
public theorem lemma_two_two
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S)
    (barS barJ barB : Subgroup barG)
    (hbarS : barS = (S : Subgroup G).map q)
    (B : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓
      Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hbarJ : barJ =
      (elementaryAbelianMaxJ (S : Subgroup G)).map q)
    (hbarB : barB = B.map q)
    (hJne : barJ ≠ ⊥) :
    LemmaTwoTwoConclusion (G := G) S q barJ barB := by
  classical
  rcases hbarS with rfl
  subst barJ barB
  let V := vSubgroup S
  let J := (elementaryAbelianMaxJ (S : Subgroup G)).map q
  let E := ⁅SectionOne.oddCore barG, J⁆ ⊔ J
  let T : Sylow 2 barG := S.mapSurjective hq
  let : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let := quotientConjugationAction S q hq hker
  have h1 : SectionOne.Hypotheses barG V := quotientConjugationAction_hypotheses h S q hq hker hJne
  let I := {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G)}
  let A : I → Subgroup barG := fun a => a.val.map q
  have hA : ∀ a, SectionOne.oneA (V := V) (T : Subgroup barG) (A a) :=
    fun a => maxElementary_map_mem_oneA h S q hq hker a.val a.property
  have hJgen : J = ⨆ a, A a := by
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mpr
      apply sSup_le
      intro a ha
      exact Subgroup.map_le_iff_le_comap.mp (le_iSup A (⟨a, ha⟩ : I))
    · exact iSup_le fun a => Subgroup.map_mono (le_sSup a.property)
  obtain ⟨hJinf, hEN, hEnorm, n, D, hprod, hDin, hD, hDN, hmodule⟩ :=
    SectionOne.offender_generated_selected_product h1 T A hA J hJgen
  change IsInternalDirectProductFamily E D at hprod
  let N := SectionOne.oneSevenGenerated (G := barG) (V := V)
  let : N.Normal := (SectionOne.oneSeven_global_product h1 T).1
  have hJS : J ≤ (T : Subgroup barG) := hJinf ▸ inf_le_left
  have hJN : J ≤ N := (show J ≤ E from le_sup_right).trans hEN
  have hweak : ∀ b : barG, J.map (MulAut.conj b).toMonoidHom ≤ (T : Subgroup barG) →
      J.map (MulAut.conj b).toMonoidHom = J := by
    intro b hb
    exact weakly_closed_map_of_surjective S (elementaryAbelianMaxJ (S : Subgroup G))
      (sSup_le fun a ha => ha.1)
      (fun g hg => elementaryAbelianMaxJ_map_eq_of_le (S : Subgroup G) (MulAut.conj g) hg)
      q hq b hb
  have hNE : N ≤ Subgroup.normalizer (E : Set barG) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEN).mp hEnorm
  have hJE : Subgroup.normalizer (J : Set barG) ≤ Subgroup.normalizer (E : Set barG) := by
    let W := SectionOne.oddCore barG
    let : W.Normal := pPrimeCore_normal
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hW : W.map (MulAut.conj b).toMonoidHom = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (show b ∈ Subgroup.normalizer (W : Set barG) by rw [Subgroup.normalizer_eq_top]; trivial)
    have hJ : J.map (MulAut.conj b).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hb
    change (⁅W, J⁆ ⊔ J).map (MulAut.conj b).toMonoidHom = ⁅W, J⁆ ⊔ J
    rw [Subgroup.map_sup, Subgroup.map_commutator, hW, hJ]
  have hE : E.Normal := normal_of_normalized_by_normal_and_weakly_closed_normalizer
    T N J E hJS hJN hweak hNE hJE
  have hJcard : Nat.card J = 2 ^ n := by
    rw [hJinf]
    exact SectionOne.sl2_family_sylow_inf_card T E hE D hDin hprod (fun i => (hD i).1) hDN
  have hBcent : B ≤ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G) := by
    rw [hB]
    exact inf_le_right
  have hBfix : B.map q ≤ fixingSubgroup barG (FixedPoints.subgroup J V : Set V) :=
    baumann_image_fixes_thompson_fixedPoints h S q hq hker B hBcent
  have hJp : IsPGroup 2 J := T.isPGroup'.to_le hJS
  have hBnorm (i : Fin n) : B.map q ≤ Subgroup.normalizer (D i : Set barG) := by
    have hDE : D i ≤ E := by rw [hprod.1]; exact le_iSup D i
    have hJnorm : J ≤ Subgroup.normalizer (D i : Set barG) :=
      (show J ≤ E from le_sup_right).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hDE).mp (hDN i))
    exact hBfix.trans (SectionOne.oneSevenFactor_fixedSpace_normalizes h1 (D i) J (hD i) hJp hJnorm)
  have hBfixE : B.map q ≤ fixingSubgroup barG (FixedPoints.subgroup E V : Set V) := by
    intro b hb
    rw [mem_fixingSubgroup_iff]
    intro v hv
    apply (mem_fixingSubgroup_iff (M := barG)).mp (hBfix hb) v
    change v ∈ FixedPoints.subgroup J V
    rw [FixedPoints.mem_subgroup]
    intro j
    exact (FixedPoints.mem_subgroup (M := E) (a := v)).mp hv
      ⟨j, (show J ≤ E from le_sup_right) j.property⟩
  have hBp : IsPGroup 2 (B.map q) :=
    (S.isPGroup'.to_le (show B ≤ (S : Subgroup G) by rw [hB]; exact inf_le_left)).map q
  have hBcard := SectionOne.moduleProduct_card_bound h1 (B.map q) E D hBnorm
    hmodule hBfixE hBp (fun i => (hD i).2.2.1)
  have hJBoriginal : elementaryAbelianMaxJ (S : Subgroup G) ≤ B := by
    rw [hB]
    refine le_inf (sSup_le fun a ha => ha.1) ?_
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 j hj |>.symm
  have hJB : J = B.map q := Subgroup.eq_of_le_of_card_ge
    (Subgroup.map_mono hJBoriginal) (by rwa [hJcard])
  refine ⟨hE, hJB, n, D, (fun i => (commutatorAction (D i) V).map V.subtype),
    hprod.1, hprod, (fun i => (hD i).1), ?_, ?_⟩
  · intro i
    refine ⟨quotientConjugationAction_commutator_map S q hq hker (D i), ?_⟩
    rw [Subgroup.card_map_of_injective V.subtype_injective]
    exact (hD i).2.2.1
  · have hm := hmodule.map_injective V.subtype V.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
    convert hm using 1
    funext i
    cases i with
    | none => exact (quotientConjugationAction_fixedPoints_map S q hq hker E).symm
    | some i => rfl

end Stellmacher.SectionTwo
