module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySpans
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryFixed
public import CFSG.Quasithin.Chapter7.Section01To05.WeakClosure
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Actual binary doubled offender spans and innerness

The original component and automizer marking transports the H.4.3 dimensions
to the whole source orbit. Given the still-explicit source bounds w ≤ 1 and
r ≥ 3, the fundamental weak-closure inequality forces w=1 and r=3. The
fixed-space span has dimension at least five, while the equality case bounds
its corank below by one. It is therefore the reverse normalizer hyperplane.
Its quotient by the common fixed space has rank two, excluding the outer
four-group whose fixed space has dimension at most two. The inner fixed
space has order eight. A finite weak-closure minimum supplies an actual
noncommuting conjugate pair with all these properties.

This completes the outer-offender step and fixed-space-span step of 7.6.1
on the original chosen orbit. The bounds w ≤ 1, r ≥ 3, the centralizer-core
construction and pair-generation argument remain with the final owner
`qt-d-1222-nonff-doubled`; no complete binary exclusion is asserted here.
Source: Aschbacher–Smith H.4.3, 7.5.3, 7.6.1 and 7.7.1,
printed pp.380,700–703.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original orbit has binary dimension six. -/
theorem sourceOrbit_binary_dimension
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 6 := by
  obtain ⟨_,_,_,_,_,E,_⟩ := D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  rw [E.finrank_eq]
  simp [BinaryLinearThree.NaturalDual.Space, BinaryLinearThree.Vector,
    Matrix.PSL3Two.Fano.Vector, Module.finrank_prod]

/-- Both H.4.3 bounds on the literal source orbit, for its actual full automizer. -/
theorem sourceOrbit_binary_four_dimensions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup (Automizer D.sourceOrbit))
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4) :
    5 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan (automizerRepresentation D.sourceOrbit) A) ∧
      (A ≤ inducedAutomizer D.sourceOrbit L →
        Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation D.sourceOrbit) A) = 3) ∧
      (¬ A ≤ inducedAutomizer D.sourceOrbit L →
        Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation D.sourceOrbit) A) ≤ 2) := by
  obtain ⟨_,_,_,q,hq,E,f,hE,hfL,_,_,_,_⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let i := D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp
    (inclusion D.sourceOrbit_component_normalizes)
  have hi : A ≤ inducedAutomizer D.sourceOrbit L ↔
      ∀ a ∈ A, f a ∈ MulAut.innerSubgroup BinaryLinearThree.Group := by
    constructor
    · intro hAL a ha
      obtain ⟨n,hn,he⟩ := hAL ha
      rw [← he]
      exact ⟨q ⟨n,hn⟩,(hfL ⟨n,hn⟩).symm⟩
    · intro hAI a ha
      obtain ⟨g,hg⟩ := hAI a ha
      obtain ⟨l,rfl⟩ := hq g
      have he : i l = a := f.injective ((hfL l).trans hg)
      rw [← he]
      exact mem_map_of_mem _ l.property
  obtain ⟨hs,hfix,hout⟩ := doubledBinary_four_dimensions
    (automizerRepresentation D.sourceOrbit) i q hq E hE f hfL A hA hc
  exact ⟨hs,fun hh => hfix (hi.mp hh),fun hh => hout (fun hi' => hh (hi.mpr hi'))⟩

private theorem two_le_localM_of_nonFF
    {W : Subgroup G} [IsElementaryAbelian 2 W]
    (hdim : 2 ≤ Module.finrank (ZMod 2) (Additive W))
    (hn : ¬ IsFFModule (automizerRepresentation W)) : 2 ≤ localM W := by
  apply le_csInf ⟨_,Set.mem_insert _ _⟩
  rintro n (rfl | ⟨a,ha,rfl⟩)
  · exact hdim
  · obtain ⟨hA,hr,_,_⟩ := involution_actor_rank_and_fixedCodim (automizerRepresentation W) a ha
    by_contra hh
    apply hn
    exact ⟨zpowers a,hA,by omega⟩

/-- The source parameter bounds force the equality case w=1, r=3.
The two global bounds remain with the §7.7 construction in this task. -/
theorem sourceOrbit_binary_forced_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hw : globalW D.sourceOrbit T ≤ 1) (hr : 3 ≤ globalR D.sourceOrbit) :
    globalW D.sourceOrbit T = 1 ∧ globalR D.sourceOrbit = 3 ∧
      globalW D.sourceOrbit T < globalS D.sourceOrbit ∧
      globalR D.sourceOrbit = globalW D.sourceOrbit T +
        (primeRank 2 (Automizer D.sourceOrbit) : ℕ∞) := by
  have hFF := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
  have hq := D.sourceOrbit_binary_automizer_rank_eq h hd F hF hmodel
  have hfw := lemma_E_3_29 D.sourceOrbit_weakClosure_setup (Or.inr hFF)
  have hR : globalR D.sourceOrbit = 3 :=
    le_antisymm (fwci_upper_bound D.sourceOrbit_weakClosure_setup hFF (by omega) hw) hr
  have hwt : globalW D.sourceOrbit T ≠ ⊤ := ne_top_of_le_ne_top (by simp) hw
  have hcast := ENat.natCast_toNat hwt
  have hn : 3 ≤ 2 + (globalW D.sourceOrbit T).toNat := by
    rw [hR,hq,← hcast,← ENat.natCast_add] at hfw
    exact_mod_cast hfw
  have hwn : (globalW D.sourceOrbit T).toNat ≤ 1 := by
    rw [← hcast] at hw
    exact_mod_cast hw
  have hW : globalW D.sourceOrbit T = 1 := by
    rw [← hcast,show (globalW D.sourceOrbit T).toNat = 1 by omega]
    rfl
  have hm := two_le_localM_of_nonFF (by rw [D.sourceOrbit_binary_dimension h hd F hF hmodel]; decide) hFF
  refine ⟨hW,hR,?_,by rw [hW,hR,hq]; rfl⟩
  rw [hW,globalS,lt_min_iff,hR]
  exact ⟨by decide,by exact_mod_cast (show 1 < localM D.sourceOrbit by omega)⟩


/-- The equality-case offender is inner, and its element fixed spaces form the
literal reverse normalizer hyperplane. This discharges the outer-four-group
step of 7.6.1 from the two still-explicit global parameter bounds. -/
theorem sourceOrbit_binary_offender_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hw : globalW D.sourceOrbit T ≤ 1) (hr : 3 ≤ globalR D.sourceOrbit)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g) :
    let W := D.sourceOrbit
    let Wg := W.map (MulAut.conj g).toMonoidHom
    let A := offenderNormalizer W g
    let A₁ := offenderFixedSpan W g
    rank (inducedAutomizer W A) = 2 ∧
      inducedAutomizer W A ≤ inducedAutomizer W L ∧
      Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) = 8 ∧
      A₁ = W ⊓ normalizer (Wg : Set G) ∧
      IsWOffender Wg (g • T : Sylow 2 G) A₁ ∧
      subgroupCorank W A₁ = 1 ∧ A₁.relIndex W = 2 ∧ rank A₁ = 5 := by
  dsimp only
  let W := D.sourceOrbit
  let A := offenderNormalizer W g
  let I := inducedAutomizer W A
  let S := offenderFixedSpan W g
  have hFF := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
  obtain ⟨hweq,hreq,hs,heq⟩ := D.sourceOrbit_binary_forced_parameters h hd F hF hmodel hnon hw hr
  have hq := D.sourceOrbit_binary_automizer_rank_eq h hd F hF hmodel
  have hdim := D.sourceOrbit_binary_dimension h hd F hF hmodel
  have hc := offender_equality_conclusions D.sourceOrbit_weakClosure_setup hFF hg hs heq
  have hI : rank I = 2 := hc.1.trans hq
  let hIE : IsElementaryAbelian 2 I := offender_inducedAutomizer_elementary W g
  have hIc : Nat.card I = 4 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 I).exists_card_eq
    have hn' := hI
    rw [rank,hn,Nat.log_pow (by decide)] at hn'
    rw [hn,hn']
    rfl
  obtain ⟨hspan,hinner,houter⟩ := D.sourceOrbit_binary_four_dimensions h hd F hF hmodel I hIE hIc
  change 5 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan (automizerRepresentation W) I) at hspan
  have hsum := (fixedSpaceSpan (automizerRepresentation W) I).finrank_quotient_add_finrank
  have hlo := hc.2.2.2.1
  rw [hweq,offenderFixedSpan_corank] at hlo
  have hlo' : 1 ≤ Module.finrank (ZMod 2) (Additive W ⧸ fixedSpaceSpan (automizerRepresentation W) I) :=
    by exact_mod_cast hlo
  have hcor : subgroupCorank W S = 1 := by
    rw [offenderFixedSpan_corank]
    change Module.finrank (ZMod 2) (Additive W ⧸ fixedSpaceSpan (automizerRepresentation W) I) = 1
    change Module.finrank (ZMod 2) (Additive W) = 6 at hdim
    omega
  have hspanEq : Module.finrank (ZMod 2) (fixedSpaceSpan (automizerRepresentation W) I) = 5 := by
    change Module.finrank (ZMod 2) (Additive W) = 6 at hdim
    omega
  obtain ⟨hS,hrev,hquot⟩ := hc.2.2.2.2.2 (by rw [hcor,hweq]; rfl)
  have hUle : W ⊓ centralizer (A : Set G) ≤ S := by
    change D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) ≤ offenderFixedSpan D.sourceOrbit g
    rw [hc.2.2.2.2.1,hS]
    exact inf_le_inf_left W (Subgroup.centralizer_le_normalizer _)
  have hU : Nat.log 2 (Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G)) =
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation W) I) := by
    rw [← ambientSubmodule_fixedSpace W A (show A ≤ _ from inf_le_right)]
    exact ambientSubmodule_log_card W _
  have hSlog : rank S = 5 := (ambientSubmodule_log_card W _).trans hspanEq
  let : IsElementaryAbelian 2 S := offender_elementary_of_le (offenderFixedSpan_le W g)
  have hquot' : 5 - Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation W) I) = 2 := by
    rw [subgroupCorank, ← log_card_sub_log_card_eq_log_relIndex _ _ hUle] at hquot
    change Nat.log 2 (Nat.card S) - Nat.log 2 (Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G)) = _ at hquot
    rw [hU,hq] at hquot
    change rank S - _ = _ at hquot
    rwa [hSlog] at hquot
  have hIL : I ≤ inducedAutomizer W L := by
    by_contra hh
    have hh' := houter hh
    change Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation W) I) ≤ 2 at hh'
    omega
  have hfixed := (D.sourceOrbit_binary_inner_four_centralizer h hd F hF hmodel A
    inf_le_right hIL hIE hIc).1
  refine ⟨hI,hIL,hfixed,hS,hrev,hcor,?_,hSlog⟩
  rw [subgroupCorank_eq_quotient_finrank] at hcor
  rw [relIndex_eq_two_pow_quotient_finrank W S,hcor]
  rfl


/-- An actual noncommuting conjugate pair with the source inner offender and
reverse normalizer hyperplane. The witness is obtained from the weak-closure
minimum, rather than assumed as additional geometry. -/
theorem sourceOrbit_binary_exists_offender_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hw : globalW D.sourceOrbit T ≤ 1) (hr : 3 ≤ globalR D.sourceOrbit) :
    ∃ g : G,
      ⁅D.sourceOrbit,D.sourceOrbit.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g) ≤
        inducedAutomizer D.sourceOrbit L ∧
      Nat.card (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) :
        Subgroup G) = 8 ∧
      offenderFixedSpan D.sourceOrbit g = D.sourceOrbit ⊓
        normalizer (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) ∧
      (offenderFixedSpan D.sourceOrbit g).relIndex D.sourceOrbit = 2 ∧
      rank (offenderFixedSpan D.sourceOrbit g) = 5 := by
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top D.sourceOrbit_weakClosure_setup
    (ne_top_of_le_ne_top (by simp) hw)
  obtain ⟨_,hi,hc,hs,_,_,hindex,hrank⟩ :=
    D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hg
  exact ⟨g,hg.1,hi,hc,hs,hindex,hrank⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
