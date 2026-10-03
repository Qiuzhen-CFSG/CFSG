module
public import Stellmacher.SectionOne.OneSevenFactorAction
public import Stellmacher.SectionOne.LemmaOneFour
public import Stellmacher.SectionOne.OneSevenFactorUniqueness

/-!
# Pairwise separation of the factors in Stellmacher (1.7)

Two members of the refined Ω-star family are equal or commute. Their
derived subgroups lie in the three-core. When those subgroups differ,
Lemma (1.4) gives disjoint action commutators; the full factors fix each
other's action support and therefore commute by faithfulness. When the
derived subgroups coincide, the faithful four-element action identifies
both factors with the same group of order six.

This is the pairwise step of the global direct-product construction in
Stellmacher (1.7), journal p.19, following
`refs/latex/stellmacher-n-group.tex`.
The cross-support fixation is also exposed for the coordinatewise module
spanning argument used with opposite Sylow subgroups in (2.3).
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

private theorem smul_mem_commutatorAction_of_commutes
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (H : Subgroup G) (a : G) (ha : ∀ b ∈ H, a * b = b * a)
    (v : V) (hv : v ∈ commutatorAction H V) :
    a • v ∈ commutatorAction H V := by
  have hle : commutatorAction H V ≤ (commutatorAction H V).comap
      (MulDistribMulAction.toMulAut G V a).toMonoidHom := by
    nth_rw 1 [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := _)).mpr ?_
    rintro z ⟨b, w, rfl⟩
    change a • (w⁻¹ * (b • w)) ∈ commutatorAction H V
    rw [smul_mul', smul_inv']
    have hab : a • (b • w) = b • (a • w) := by
      change a • ((b : G) • w) = (b : G) • (a • w)
      rw [← mul_smul, ha b b.property, mul_smul]
    rw [hab, commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨b, a • w, rfl⟩
  exact hle hv

private theorem disjoint_commutatorAction_le_fixedPoints
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (D E : Subgroup G)
    (hcomm : ∀ d ∈ D, ∀ e ∈ E, d * e = e * d)
    (hdisj : Disjoint (commutatorAction D V) (commutatorAction E V)) :
    commutatorAction E V ≤ FixedPoints.subgroup D V := by
  intro v hv
  rw [FixedPoints.mem_subgroup]
  intro d
  have hdv : (d : G) • v ∈ commutatorAction E V :=
    smul_mem_commutatorAction_of_commutes E d (hcomm d d.property) v hv
  have hdeltaE : v⁻¹ * ((d : G) • v) ∈ commutatorAction E V :=
    (commutatorAction E V).mul_mem ((commutatorAction E V).inv_mem hv) hdv
  have hdeltaD : v⁻¹ * ((d : G) • v) ∈ commutatorAction D V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨d, v, rfl⟩
  have hone : v⁻¹ * ((d : G) • v) = 1 := hdisj.le_bot ⟨hdeltaD, hdeltaE⟩
  exact (inv_mul_eq_one.mp hone).symm

private theorem oneSevenFactor_commute_of_derived_ne
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (D E : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) (hE : IsOneSevenFactor (V := V) E)
    (hne : (commutator D).map D.subtype ≠ (commutator E).map E.subtype) :
    ∀ d ∈ D, ∀ e ∈ E, d * e = e * d := by
  let F : Subgroup G := (commutator D).map D.subtype
  let K : Subgroup G := (commutator E).map E.subtype
  have hF : oneOmega (V := V) F := hD.2.1
  have hK : oneOmega (V := V) K := hE.2.1
  have hFKdisj : Disjoint F K := omega_pair_disjoint hF hK hne
  have hKF : K ≤ Subgroup.normalizer (F : Set G) :=
    hK.1.trans (oneSevenFactor_oddCore_normalizes_derived D hD)
  have hFK : F ≤ Subgroup.normalizer (K : Set G) :=
    hF.1.trans (oneSevenFactor_oddCore_normalizes_derived E hE)
  have hcommBot : ⁅F, K⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hKF)
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hFK)).trans hFKdisj.le_bot
  have hcomm : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f := by
    intro f hf k hk
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot hf) k hk).symm
  have hActionDisj : Disjoint (commutatorAction F V) (commutatorAction K V) :=
    omega_pair_action_disjoint h hF hK hne
      (oneSevenFactor_derived_le_threeCore D hD)
      (oneSevenFactor_derived_le_threeCore E hE) le_rfl
  have hKfixed : commutatorAction K V ≤ FixedPoints.subgroup F V :=
    disjoint_commutatorAction_le_fixedPoints F K hcomm hActionDisj
  have hFfixed : commutatorAction F V ≤ FixedPoints.subgroup K V :=
    disjoint_commutatorAction_le_fixedPoints K F
      (fun k hk f hf => (hcomm f hf k hk).symm) hActionDisj.symm
  have hDfix (d : G) (hd : d ∈ D) (v : V) (hv : v ∈ commutatorAction E V) :
      d • v = v := by
    apply oneSevenFactor_fixes_derived_fixedPoints D hD d hd v
    apply hKfixed
    rwa [oneSevenFactor_full_commutator_eq_derived E hE] at hv
  have hEfix (e : G) (he : e ∈ E) (v : V) (hv : v ∈ commutatorAction D V) :
      e • v = v := by
    apply oneSevenFactor_fixes_derived_fixedPoints E hE e he v
    apply hFfixed
    rwa [oneSevenFactor_full_commutator_eq_derived D hD] at hv
  let ρ : G →* MulAut V := MulDistribMulAction.toMulAut G V
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff (f := ρ)).mp (by
    rw [← fixingSubgroup_univ_eq_ker_toMulAut]
    exact h.action_faithful)
  intro d hd e he
  apply hρinj
  rw [map_mul, map_mul]
  ext v
  have hδd : v⁻¹ * (d • v) ∈ commutatorAction D V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨(⟨d, hd⟩ : D), v, rfl⟩
  have hδe : v⁻¹ * (e • v) ∈ commutatorAction E V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨(⟨e, he⟩ : E), v, rfl⟩
  have hde := hDfix d hd _ hδe
  have hed := hEfix e he _ hδd
  change d • (e • v) = e • (d • v)
  calc
    d • (e • v) = d • (v * (v⁻¹ * (e • v))) := by simp
    _ = (d • v) * (v⁻¹ * (e • v)) := by rw [smul_mul', hde]
    _ = (e • v) * (v⁻¹ * (d • v)) := by ac_rfl
    _ = e • (v * (v⁻¹ * (d • v))) := by rw [smul_mul', hed]
    _ = e • (d • v) := by simp

/-- Distinct factors in the family used by (1.7) commute elementwise. -/
public theorem oneSevenFactor_eq_or_commute
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (D E : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) (hE : IsOneSevenFactor (V := V) E) :
    D = E ∨ ∀ d ∈ D, ∀ e ∈ E, d * e = e * d := by
  by_cases hderived : (commutator D).map D.subtype = (commutator E).map E.subtype
  · exact Or.inl (oneSevenFactor_eq_of_derived_eq h D E hD hE hderived)
  · exact Or.inr (oneSevenFactor_commute_of_derived_ne h D E hD hE hderived)

/-- A distinct one-seven factor fixes the full action support of its partner. -/
public theorem oneSevenFactor_commutatorAction_le_fixedPoints
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (D E : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) (hE : IsOneSevenFactor (V := V) E)
    (hne : D ≠ E) :
    commutatorAction E V ≤ FixedPoints.subgroup D V := by
  have hcomm := (oneSevenFactor_eq_or_commute h D E hD hE).resolve_left hne
  apply disjoint_commutatorAction_le_fixedPoints D E hcomm
  rw [oneSevenFactor_full_commutator_eq_derived D hD,
    oneSevenFactor_full_commutator_eq_derived E hE]
  have hderived : (commutator D).map D.subtype ≠ (commutator E).map E.subtype :=
    fun heq => hne (oneSevenFactor_eq_of_derived_eq h D E hD hE heq)
  exact omega_pair_action_disjoint h hD.2.1 hE.2.1 hderived
    (oneSevenFactor_derived_le_threeCore D hD)
    (oneSevenFactor_derived_le_threeCore E hE) le_rfl

end Stellmacher.SectionOne
