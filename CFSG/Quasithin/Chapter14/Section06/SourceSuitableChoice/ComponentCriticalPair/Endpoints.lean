module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.TerminalGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCritical

/-!
# Literal critical conjugates and lifting a specified matching pair

The original F.9 endpoint supplies a conjugate of U that fails to commute with U.
It retains the same conjugator on the two local groups, their modules and the
commutator bound. The source right conjugator is explicitly inverted when it is
used in a left-conjugation crossing record.

For the same suitable u, noncentral two-core action interchanges its two lifts
modulo Z. Thus a specified Mc-match modulo Z lifts to an exact Mc-match, which
constructs the crossing record and forces C_G(u) outside Mc. These statements
assume neither noncommutation nor global fusion control.

The rank-one/rank-two argument producing the specified match is still an input.
A normalized endpoint fixes the original edge; translating an endpoint by Mc
in that argument requires transporting the conjugates as well.

Source: Aschbacher--Smith, F.9.10--13 and 14.6.24(4), printed pp.321--322,1041.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- When Vplus=V, criticality forces the two literal conjugate spans not to commute. -/
theorem critical_spans_do_not_commute
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis) (hplus : D.Vplus = D.V)
    (i : h.CriticalEndpoint) :
    ¬ D.UH ≤ centralizer (i.conjugate D.UH : Set G) := by
  intro hc
  apply i.noncentral
  have hVU : D.V ≤ D.UH := by
    change D.V ≤ conjugateSpanBy D.Vplus D.H
    rw [hplus]
    exact le_conjugateSpanBy _ _
  have hz : ⁅i.conjugate D.UH,D.V⁆ = ⊥ := by
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact hVU.trans hc
  rw [hz]
  exact bot_le

omit [Finite G] in
/-- Convert the book's right conjugator g into the left conjugator g⁻¹.
The same inverse is used in the marked matching pair. -/
theorem right_conjugate_matching_iff (H : Subgroup G) (u g : G) :
    (∃ x ∈ H, x⁻¹ * u * x = g * u * g⁻¹) ↔
      ∃ x ∈ H, (MulAut.conj x) u = (MulAut.conj (g⁻¹)⁻¹) u := by
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨x⁻¹,H.inv_mem hx,by simpa only [MulAut.conj_apply,inv_inv] using he⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨x⁻¹,H.inv_mem hx,by simpa only [MulAut.conj_apply,inv_inv] using he⟩

/-- Core movement fuses the two lifts of every specified quotient match.
Only this pair is matched; no global fusion-control hypothesis is used. -/
theorem match_of_match_mod_point
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (u : G) (hu : u ∈ D.UH)
    (hmove : ¬ D.QH ≤ centralizer ({u} : Set G)) (v : G)
    (hm : ∃ x ∈ D.H, (MulAut.conj x) u * v⁻¹ ∈ D.V₁) :
    ∃ x ∈ D.H, (MulAut.conj x) u = v := by
  classical
  obtain ⟨x,hx,he⟩ := hm
  by_cases he1 : (MulAut.conj x) u * v⁻¹ = 1
  · exact ⟨x,hx,mul_inv_eq_one.mp he1⟩
  obtain ⟨q,hq,hqn⟩ := SetLike.not_le_iff_exists.mp hmove
  let z := ⁅q,u⁆
  have hz : z ∈ D.V₁ := by
    have hh := h.commutator_UH_QH_le_point (commutator_mem_commutator hu hq)
    simpa only [commutatorElement_inv] using D.V₁.inv_mem hh
  have hzne : z ≠ 1 := by
    intro he
    apply hqn
    exact mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp he)
  obtain ⟨z₀,_,huniq⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp h.point_card
  have hez : (MulAut.conj x) u * v⁻¹ = z := by
    exact congrArg Subtype.val ((huniq ⟨_,he⟩ (fun hh => he1 (congrArg Subtype.val hh))).trans
      (huniq ⟨z,hz⟩ (fun hh => hzne (congrArg Subtype.val hh))).symm)
  have hzsq : z * z = 1 := by
    have hs := pow_card_eq_one' (x := (⟨z,hz⟩ : D.V₁))
    rw [h.point_card] at hs
    simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one, pow_two] using congrArg Subtype.val hs
  have hxz : (MulAut.conj x) z = z := by
    change x * z * x⁻¹ = z
    rw [← h.H_centralizes hx z hz]
    simp
  have hqu : (MulAut.conj q) u = z * u := by
    simp [z,commutatorElement_def,MulAut.conj_apply,mul_assoc]
  refine ⟨x*q,D.H.mul_mem hx (pCoreIn_le 2 D.H hq),?_⟩
  calc
    (MulAut.conj (x*q)) u = (MulAut.conj x) ((MulAut.conj q) u) := by
      simp [MulAut.conj_apply,mul_assoc]
    _ = z * (MulAut.conj x) u := by rw [hqu,map_mul,hxz]
    _ = z * (z*v) := by rw [mul_inv_eq_iff_eq_mul.mp hez]
    _ = v := by rw [← mul_assoc,hzsq,one_mul]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The original terminal source has an actual noncommuting critical conjugate;
its edge placements and commutator containment use that same conjugator. -/
theorem source_terminal_critical_conjugate :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    3 ≤ h.b ∧ Odd h.b ∧
      ∃ i : h.CriticalEndpoint,
        i.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ Mc ∧
        conjugateSpanBy (localModule T M) Mc ≤ i.conjugate Mc ∧
        ⁅conjugateSpanBy (localModule T M) Mc,
          i.conjugate (conjugateSpanBy (localModule T M) Mc)⁆ ≤
          conjugateSpanBy (localModule T M) Mc ⊓
            i.conjugate (conjugateSpanBy (localModule T M) Mc) ∧
        ¬ conjugateSpanBy (localModule T M) Mc ≤
          centralizer (i.conjugate (conjugateSpanBy (localModule T M) Mc) : Set G) := by
  obtain ⟨hb,ho,⟨i⟩⟩ := source_rankTwo_critical_track_bounds
    hG T hempty hM hunique hmany hcard e hab Mc
      (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  exact ⟨hb,ho,i,i.large_le hb,i.reverse_le hb,i.commutator hb,
    critical_spans_do_not_commute _ rfl i⟩

/-- A specific H-matching pair at a critical endpoint supplies all the crossing
geometry. Neither noncommutation nor global fusion control is a premise. -/
theorem source_crossing_of_critical_match
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) Mc)
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)
    (hm : ∃ x ∈ Mc, (MulAut.conj x) u = (MulAut.conj i.representative⁻¹) u) :
    Nonempty (SourceCrossingGeometry (localModule T M) Mc Mc u) := by
  let U := conjugateSpanBy (localModule T M) Mc
  have hn : Mc ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hpre : (MulAut.conj i.representative⁻¹) u ∈ U := by
    obtain ⟨x,hx,he⟩ := hm
    rw [← he]
    exact (hn hx u).mp hu
  have hmem : u ∈ i.conjugate U := by
    refine ⟨(MulAut.conj i.representative⁻¹) u,hpre,?_⟩
    simp [MulAut.conj_apply,mul_assoc]
  exact ⟨⟨U,le_rfl,hn,i.representative,hmem,hm,
    critical_spans_do_not_commute _ rfl i⟩⟩

/-- The actual critical pair escapes Mc as soon as its two specified vectors
are Mc-conjugate. This is the Mc half of original 14.6.24(4). -/
theorem source_centralizer_not_le_terminal_of_critical_match
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) Mc)
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)
    (hm : ∃ x ∈ Mc, (MulAut.conj x) u = (MulAut.conj i.representative⁻¹) u) :
    ¬ centralizer ({u} : Set G) ≤ Mc := by
  obtain ⟨f⟩ := source_crossing_of_critical_match hG T hempty hM hunique hmany hcard e hab u hu i hm
  let := hab
  exact centralizer_not_le_of_crossing_match f.A Mc
    (conjugateSpanBy (localModule T M) Mc) Mc f.contained f.normalizes
    (le_normalizer_conjugateSpanBy _ _) u f.g f.matching f.crossing

/-- A match on the original quotient by Z lifts to the actual crossing record
for the same suitable u and the same critical endpoint. -/
theorem source_crossing_of_critical_match_mod_point
    (u : G)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u)
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)
    (hm : ∃ x ∈ Mc,
      (MulAut.conj x) u * ((MulAut.conj i.representative⁻¹) u)⁻¹ ∈ centralInvolutions T) :
    Nonempty (SourceCrossingGeometry (localModule T M) Mc Mc u) ∧
      ¬ centralizer ({u} : Set G) ≤ Mc := by
  have hm' := match_of_match_mod_point
    (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab)
      u hu.1 hu.2.2.2.1 _ hm
  exact ⟨source_crossing_of_critical_match hG T hempty hM hunique hmany hcard e hab u hu.1 i hm',
    source_centralizer_not_le_terminal_of_critical_match
      hG T hempty hM hunique hmany hcard e hab u hu.1 i hm'⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
