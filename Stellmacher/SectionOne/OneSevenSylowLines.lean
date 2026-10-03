module

public import Stellmacher.SectionOne.OneSevenSylowOffender
public import Stellmacher.SectionOne.OneSevenFactorPair
public import Stellmacher.SectionOne.SL2FamilySylowCoordinates
public import Theory.GroupAction.Lemmas

/-!
# Sylow commutator lines on one-seven factor supports

Let a normal subgroup `E` be an indexed internal product of one-seven factors
`D i`, each normal in `E`, and let `T` be an ambient Sylow two-subgroup.  On
the support `[V, D i]`, every action difference from `T ∩ E` lies in the
order-two coordinate line `[V, T ∩ D i]`, and some element of `T ∩ E` acts
nontrivially on that support.

Indexed Sylow coordinates generate `T ∩ E`.  Normality keeps the chosen
support invariant, while a distinct coordinate fixes it by the one-seven
factor-pair theorem, so the difference bound propagates from coordinates to
the whole intersection.  The coordinate line has order two by the faithful
involution result.  If the whole intersection fixed the support, then it would
also fix the coprime derived-fixed complement, contradicting that nontrivial
coordinate line.

This is the intrinsic support-control input for the commutator-line argument
in Stellmacher (4.6), Journal of Algebra 190 (1997), p. 26, following
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

universe u

private theorem differences_mem_of_generators
    {G V I : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (B : Subgroup G) (K : I → Subgroup G) (U R : Subgroup V)
    (hB : B = iSup K)
    (hU : ∀ b ∈ B, ∀ v ∈ U, b • v ∈ U)
    (hK : ∀ i, ∀ b ∈ K i, ∀ v ∈ U, v⁻¹ * (b • v) ∈ R) :
    ∀ b ∈ B, ∀ v ∈ U, v⁻¹ * (b • v) ∈ R := by
  let P : Subgroup G :=
    { carrier := {b | b ∈ B ∧ ∀ v ∈ U, v⁻¹ * (b • v) ∈ R}
      one_mem' := ⟨B.one_mem, by
        intro v hv
        simp only [one_smul, inv_mul_cancel]
        exact R.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, haR⟩ ⟨hb, hbR⟩
        refine ⟨B.mul_mem ha hb, fun v hv => ?_⟩
        have hh := R.mul_mem (hbR v hv) (haR (b • v) (hU b hb v hv))
        simpa only [mul_smul, mul_assoc, mul_inv_cancel_left] using hh
      inv_mem' := by
        rintro b ⟨hb, hbR⟩
        refine ⟨B.inv_mem hb, fun v hv => ?_⟩
        have hh := R.inv_mem (hbR (b⁻¹ • v) (hU b⁻¹ (B.inv_mem hb) v hv))
        simpa only [smul_inv_smul, mul_inv_rev, inv_inv] using hh }
  have hBP : B ≤ P := by
    rw [hB]
    exact iSup_le fun i b hb => ⟨(hB.symm ▸ le_iSup K i) hb, hK i b hb⟩
  intro b hb
  exact (hBP hb).2

private theorem action_commutator_mono
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    {A B : Subgroup G} (hAB : A ≤ B) : commutatorAction A V ≤ commutatorAction B V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  apply Subgroup.closure_mono
  rintro v ⟨a, w, rfl⟩
  exact ⟨⟨a, hAB a.property⟩, w, rfl⟩

/-- The Sylow intersection acts on each one-seven support through its
order-two coordinate line, and acts nontrivially there. -/
public theorem oneSevenFactor_sylow_line_control
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (T : Sylow 2 G) (E : Subgroup G) [E.Normal]
    {n : ℕ} (D : Fin n → Subgroup G)
    (hprod : IsInternalDirectProductFamily E D) (hinj : Function.Injective D)
    (hD : ∀ i, IsOneSevenFactor (V := V) (D i))
    (hDN : ∀ i, ((D i).subgroupOf E).Normal) :
    ∀ i, let B := (T : Subgroup G) ⊓ E
      let Q := (T : Subgroup G) ⊓ D i
      let U := commutatorAction (D i) V
      let R := commutatorAction Q V
      Nat.card R = 2 ∧ R ≤ U ∧
      (∀ b ∈ B, ∀ v ∈ U, v⁻¹ * (b • v) ∈ R) ∧
      ∃ b ∈ B, ∃ v ∈ U, b • v ≠ v := by
  obtain ⟨hBgen, hQc⟩ :=
    sl2_family_sylow_coordinates T E inferInstance D hprod (fun i => (hD i).1)
  intro i
  let B := (T : Subgroup G) ⊓ E
  let Q := (T : Subgroup G) ⊓ D i
  let U := commutatorAction (D i) V
  let R := commutatorAction Q V
  have hRc : Nat.card R = 2 :=
    oneSevenFactor_involution_commutator_card_two h.action_faithful (D i) Q (hD i)
      inf_le_right (hQc i)
  have hRU : R ≤ U := action_commutator_mono inf_le_right
  have hDiE : D i ≤ E := hprod.1.symm ▸ le_iSup D i
  have hEN : E ≤ Subgroup.normalizer (D i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDiE).mp (hDN i)
  have hUinv : IsInvariant B V U :=
    commutatorAction_isInvariant_of_normalizing_actor B (D i) (inf_le_right.trans hEN)
  have hcontrol : ∀ b ∈ B, ∀ v ∈ U, v⁻¹ * (b • v) ∈ R := by
    apply differences_mem_of_generators B (fun j => (T : Subgroup G) ⊓ D j) U R hBgen
    · intro b hb v hv
      exact (hUinv.invariant ⟨b, hb⟩ v).mp hv
    · intro j b hb v hv
      by_cases hji : j = i
      · subst j
        rw [show R = commutatorAction Q V from rfl, commutatorAction_eq_closure]
        exact Subgroup.subset_closure ⟨⟨b, hb⟩, v, rfl⟩
      · have hfix := oneSevenFactor_commutatorAction_le_fixedPoints h (D j) (D i)
          (hD j) (hD i) (fun he => hji (hinj he)) hv
        have hfixed := (FixedPoints.mem_subgroup (M := D j) (a := v)).mp hfix ⟨b, hb.2⟩
        change b • v = v at hfixed
        rw [hfixed, inv_mul_cancel]
        exact R.one_mem
  refine ⟨hRc, hRU, hcontrol, ?_⟩
  by_contra hmove
  push Not at hmove
  let F := (commutator (D i)).map (D i).subtype
  let C := FixedPoints.subgroup F V
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    dsimp only [F]
    rw [(hD i).2.1.2.1, hm]
    exact (show Nat.Coprime 3 2 by decide).pow_right m
  have hcompl : IsCompl C U := by
    dsimp only [C, U, F]
    rw [oneSevenFactor_full_commutator_eq_derived (D i) (hD i)]
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop inferInstance
  have hCU : C ⊔ U ≤ FixedPoints.subgroup Q V := by
    apply sup_le
    · intro v hv
      rw [FixedPoints.mem_subgroup]
      intro q
      exact oneSevenFactor_fixes_derived_fixedPoints (D i) (hD i) q q.property.2 v hv
    · intro v hv
      rw [FixedPoints.mem_subgroup]
      intro q
      exact hmove q ⟨q.property.1, hDiE q.property.2⟩ v hv
  have hRbot : R = ⊥ := by
    rw [show R = commutatorAction Q V from rfl, commutatorAction_eq_closure]
    apply le_bot_iff.mp
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨q, v, rfl⟩
    have hv : v ∈ FixedPoints.subgroup Q V :=
      hCU (hcompl.sup_eq_top.symm ▸ Subgroup.mem_top v)
    have hf := (FixedPoints.mem_subgroup (M := Q) (a := v)).mp hv q
    change v⁻¹ * (q • v) = 1
    exact inv_mul_eq_one.mpr hf.symm
  have hone := Subgroup.card_eq_one.mpr hRbot
  omega

end Stellmacher.SectionOne
