module
public import ABG.ChapterII.Section3.CharacteristicPower
public import ABG.ChapterII.Section3.QNotTwoGroup
public import ABG.ChapterII.Section3.QSylowGeometry
public import ABG.ChapterII.Section3.CentralSylowDihedralQuotient
public import ABG.ChapterII.Section3.CoreFreeCentralQuotient
public import Theory.GroupTheory.SectionLift
public import GorensteinWalter.PGroupExtension
public import GorensteinWalter.DihedralPSL2Core
public import ABG.ChapterII.Section3.QInvolutionCentralizerCover
public import ABG.ChapterII.Section3.QSimpleSections
public import ABG.ChapterII.Section3.QCharacteristicSL2Lift

/-!
# Characteristic powers of Q-subgroups of QD-groups

Every Q-subgroup K of a finite QD-group H of source characteristic power q
has source characteristic power r at most q. The full enlarged Q predicate
is retained, including generalized quaternion Sylow subgroups.

The Sylow-center centralizer supplements the odd core of K and embeds in
an involution centralizer of H. Hence all sections of K/O(K), and of its
central Sylow-center quotient, occur in that involution centralizer. The
proved simple-section exclusions rule out A7 and bound odd PSL2 field
orders there. The central quotient has dihedral Sylow subgroups and trivial
odd core and is not a two-group. Gorenstein--Walter therefore supplies a
normal PSL2 subgroup with the required field bound (order three is bounded
separately). The nonsplit central-cover and uniqueness results lift this to
an actual characteristic SL2 subgroup of K/O(K), which is the defining datum.

This is ABG II.3 Lemma 2, article pages 23--24. The centralizer supplement
is used through its actual quotient equivalence; no assertion that it has
a stronger Sylow shape and no later semilinear-structure theorem is needed.
-/

namespace ABG
open GorensteinWalter
universe u

public theorem qSubgroup_sourceCharacteristicPower_le
    {H : Type u} [Group H] [Finite H] (hH : IsQDGroup H)
    {q : ℕ} (hq : HasSourceCharacteristicPower H q)
    (K : Subgroup H) (hK : IsQGroup K) :
    ∃ r ≤ q, HasSourceQCharacteristicPower K r := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, M, f, hf, i, hi⟩ := qGroup_oddCore_quotient_centralizer_cover K hK
  have hqx := HasSourceCharacteristicPower.at_involution hH hq x hx
  obtain ⟨hCx, T, hT⟩ := qd_involutionCentralizer_isQGroup hH x hx
  have hsec := qGroup_simple_section_exclusions hCx T hT q hqx
  let E := K ⧸ pPrimeCore 2 K
  have hQE : IsQGroup E := hK.oddCore_quotient
  have hcore : pPrimeCore 2 E = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2)
  let S : Sylow 2 E := Classical.choice inferInstance
  let N := subgroupCenter (S : Subgroup E)
  have hcentral : N ≤ Subgroup.center E := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hQE S
    rw [hcore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  have hNN : N.Normal := by
    constructor
    intro y hy g
    have hyg := Subgroup.mem_center_iff.mp (hcentral hy) g
    simpa [hyg, mul_assoc] using hy
  let : N.Normal := hNN
  have hNtwo : IsPGroup 2 N :=
    (S.isPGroup'.to_subgroup (Subgroup.center S)).of_equiv
      (Subgroup.equivMapOfInjective _ (S : Subgroup E).subtype
        (S : Subgroup E).subtype_injective)
  have hdih : GorensteinWalter.HasDihedralSylowTwo (E ⧸ N) :=
    hasDihedralSylowTwo_quotient_sylow_center_of_model S N rfl
      (qGroup_sylow_center_quotient_geometry hQE S).2.2
  have hquotcore : pPrimeCore 2 (E ⧸ N) = ⊥ :=
    oddCore_quotient_eq_bot_of_central_two_subgroup N hcentral hNtwo hcore
  have hnotTwo : ¬ IsPGroup 2 (E ⧸ N) := fun h =>
    hQE.not_isPGroup (isPGroup_of_normal_subgroup_of_quotient N hNtwo h)
  let fN : M →* E ⧸ N := (QuotientGroup.mk' N).comp f
  have hfN : Function.Surjective fN := (QuotientGroup.mk'_surjective N).comp hf
  have hnotA : ¬ Nonempty ((E ⧸ N) ≃* alternatingGroup (Fin 7)) := by
    rintro ⟨e⟩
    let a : (⊤ : Subgroup (E ⧸ N)) →* alternatingGroup (Fin 7) :=
      e.toMonoidHom.comp (⊤ : Subgroup (E ⧸ N)).subtype
    have ha : Function.Surjective a := e.surjective.comp (by intro y; exact ⟨⟨y, trivial⟩, rfl⟩)
    obtain ⟨U, g, hg⟩ := MonoidHom.exists_section_of_surjective_of_injective fN hfN i hi ⊤ a ha
    exact hsec.1 U g hg
  obtain ⟨F, iF, fF, hF, Lbar, hLN, ⟨eLbar⟩⟩ :=
    exists_normal_psl2_of_not_twoGroup_not_a7 hdih hquotcore hnotTwo hnotA
  let : Field F := iF
  let : Finite F := fF
  let : Lbar.Normal := hLN
  have hbound : Nat.card F ≤ q := by
    by_cases hlarge : 3 < Nat.card F
    · obtain ⟨U, g, hg⟩ := MonoidHom.exists_section_of_surjective_of_injective
        fN hfN i hi Lbar eLbar.toMonoidHom eLbar.surjective
      exact hsec.2 F hF hlarge U g hg
    · obtain ⟨F0, iF0, fF0, hF0, hF0q, _⟩ := hqx
      let : Field F0 := iF0
      let : Finite F0 := fF0
      have h3 := odd_prime_power_three_le _ hF0
      omega
  obtain ⟨L, hLc, heL⟩ :=
    qGroup_characteristic_sl2_of_normal_psl2 hQE hcore S N rfl hcentral F hF Lbar eLbar
  exact ⟨Nat.card F, hbound, F, iF, fF, hF, rfl, L, hLc, heL⟩

end ABG
