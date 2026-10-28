module
public import Stellmacher.SectionFiveToSeven.SixOneSelectedFactor
public import Stellmacher.SectionFiveToSeven.SixOneOddOrbit
public import Stellmacher.SectionFiveToSeven.SixOneHallOrbitNormalizer
public import Stellmacher.SectionFiveToSeven.SixOneOrbitClosureContradiction
public import Theory.GroupTheory.Hall.OddSylowComplement

/-!
# Stellmacher (6.1): Baumann noncontainment in the second core

Under Hypothesis Two, B(S) is not contained in O₂(P₂). The proof assumes
that containment and uses the actual join P₁∨P₂, whose two-core is trivial;
it does not assume that this join is the whole ambient group.

The core-containment reduction gives S=S₀. The selected-factor theorem
produces a native local group E, with actual Sylow image B(S), and its
four-element residual module W₁, normalized by L₁=⟨B(S)^P₁⟩. Choose an odd
Hall complement U to the supplied Sylow subgroup of P₂. Baumann heredity
makes P₂ normalize B(S). The explicit (2.5) conjugation argument puts
W=⟨W₁^U⟩ in B(S) and makes E and U normalize it. Two applications of the
shared-omega (5.4) and cross-normalizer (3.9) argument make L₁ normalize W.

The exact products P₁=SL₁ and P₂=SU then make ⟨W^S⟩ normal in the actual
join P₁∨P₂. It is a nontrivial two-subgroup, contradicting the trivial core.
All selected-factor, native-action, and orbit-transfer assertions are
supplied by proved leaves retaining their original subgroup maps.

Source: Stellmacher, *2-Local structure of N-groups*, Journal of Algebra
190 (1997), (6.1), p.30; `refs/latex/stellmacher-n-group.tex` and the scan
`refs/files/stellmacher-n-group.pdf`, PDF page20. The scan confirms the
noncontainment and that order four concerns [O₂(E),O²(E)].
-/

open scoped Pointwise
namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem second_normalizes_baumann
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) (hB : baumannIn S ≤ twoCoreIn P2) :
    P2 ≤ Subgroup.normalizer (baumannIn S : Set H) := by
  have hQ2S : twoCoreIn P2 ≤ S := by
    obtain ⟨_, T2, hT2⟩ := h.fiveOne.P2_mem.1.2.1
    rw [← hT2]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := P2)).le_sylow_of_normal T2)
  have hBeq : baumannIn (twoCoreIn P2) = baumannIn S := by
    simpa [baumannIn, omegaOneCenter, omegaOneCenterAmbient] using
      baumann_eq_of_intermediate S (twoCoreIn P2) hB hQ2S
  have hQ2P2 : twoCoreIn P2 ≤ P2 := Subgroup.map_subtype_le _
  have hQ2normal : ((twoCoreIn P2).subgroupOf P2).Normal := by
    rw [twoCoreIn, subgroupOf_map_subtype_eq]
    infer_instance
  have hnorm := ((Subgroup.normal_subgroupOf_iff_le_normalizer hQ2P2).mp hQ2normal).trans
    (normalizer_le_normalizer_baumann (twoCoreIn P2))
  change P2 ≤ Subgroup.normalizer (baumannIn (twoCoreIn P2) : Set H) at hnorm
  rwa [hBeq] at hnorm

/-- **Stellmacher (6.1).** The Baumann subgroup of the amalgam is not
contained in the 2-core of `P₂`. -/
public theorem lemma_six_one
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) :
    ¬ baumannIn S ≤ twoCoreIn P2 := by
  intro hB
  obtain ⟨hS, _hJ⟩ := sixOne_coreContainment_reduction S0 S P1 P2 h hB
  obtain ⟨K, T, hT, hEL, hgen, hsec, hP, hA, hFamily,
    hWcard, hW1B, hWomega, hLW1, hprod1⟩ := sixOne_selected_factor S0 S P1 P2 h hB
  let f : K →* H := P1.subtype.comp K.subtype
  have hf : Function.Injective f := P1.subtype_injective.comp K.subtype_injective
  let W1 := (⁅pCore 2 K, twoResidualAmbient (⊤ : Subgroup K)⁆).map f
  let L := sectionSixL (baumannIn S) P1
  have hP2B := second_normalizes_baumann S0 S P1 P2 h hB
  obtain ⟨hSP2, T2, hT2⟩ := h.fiveOne.P2_mem.1.2.1
  have hsolvP2 := (lemma_five_three S0 S P1 P2 h).2.2.1
  obtain ⟨U2, hU2odd, hcompl⟩ := Subgroup.exists_odd_complement_sylow_two hsolvP2 T2
  let U := U2.map P2.subtype
  have hUodd : Odd (Nat.card U) := by
    rw [Subgroup.card_map_of_injective P2.subtype_injective]
    exact hU2odd
  have hUP2 : U ≤ P2 := Subgroup.map_subtype_le U2
  have hUB : U ≤ Subgroup.normalizer (baumannIn S : Set H) := hUP2.trans hP2B
  have hUT : U ≤ Subgroup.normalizer (((T : Subgroup K).map f : Subgroup H) : Set H) := by
    rw [hT]
    exact hUB
  obtain ⟨hW1W, hWB, hEW, hUW⟩ := sixOne_odd_orbit_data hsec T hP hA f hf U hUodd hUT
  let W := conjugateClosure W1 U
  change W1 ≤ W at hW1W
  change W ≤ (T : Subgroup K).map f at hWB
  rw [hT] at hWB
  change f.range ≤ Subgroup.normalizer (W : Set H) at hEW
  change U ≤ Subgroup.normalizer (W : Set H) at hUW
  have hW1ne : W1 ≠ ⊥ := by
    intro hb
    have hc1 : Nat.card W1 = 1 := Subgroup.card_eq_one.mpr hb
    have hc4 : Nat.card W1 = 4 := hWcard
    omega
  have hWne : W ≠ ⊥ := fun hb => hW1ne (le_bot_iff.mp (hW1W.trans_eq hb))
  have hS0ne : (S0 : Subgroup H) ≠ ⊥ := hS ▸ h.fiveOne.S_nontrivial
  let N := Subgroup.normalizer (S0 : Set H)
  have hNlocal : IsTwoLocal N := ⟨(S0 : Subgroup H), hS0ne, S0.isPGroup', rfl⟩
  obtain ⟨M, hNM, hMmax⟩ := Finite.exists_le_maximal hNlocal
  have hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M :=
    ⟨hMmax, (S0 : Subgroup H).le_normalizer.trans hNM⟩
  have hLW : L ≤ Subgroup.normalizer (W : Set H) :=
    sixOne_hall_orbit_normalizer S0 S P1 P2 h hS f.range U W1 M
      hFamily hEL hgen hUB hW1B hW1ne hWomega hLW1 hEW hM
  have hprod2 : (P2 : Set H) = (S : Set H) * (U : Set H) := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨s, u⟩, he⟩ := hcompl.2 (⟨x, hx⟩ : P2)
      exact Set.mem_mul.mpr ⟨s, hT2 ▸ Subgroup.mem_map_of_mem P2.subtype s.property,
        u, Subgroup.mem_map_of_mem P2.subtype u.property, congrArg Subtype.val he⟩
    · rintro ⟨s, hs, u, hu, rfl⟩
      exact P2.mul_mem (hSP2 hs) (hUP2 hu)
  exact sixOne_orbitClosure_contradiction S0 S P1 P2 h L U W
    (hWB.trans inf_le_left) hWne hLW hUW hprod1 hprod2

end Stellmacher.SectionsFiveToSeven
