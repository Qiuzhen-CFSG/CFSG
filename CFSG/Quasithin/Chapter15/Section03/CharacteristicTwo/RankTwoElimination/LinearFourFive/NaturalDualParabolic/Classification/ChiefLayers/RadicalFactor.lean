module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.ChiefLayers.Contract

/-!
# The radical as the common dual chief factor

Displacement identifies the shear kernel with maps from V/⟨x⟩ to ⟨x⟩.
Taking the coefficient of the marked nonzero vector x gives an actual
isomorphism O₂(P)/O₂(L) ≃ (V/⟨x⟩)*. Conjugation precomposes by the inverse
of the existing quotientActor, so this is the contragredient for precisely
the common marking used by the two module factors.

The intrinsic core is identified with its subtype image E in G, and the
old core maps to exactly N = O₂(L) inside E. Transitivity on nonzero
covectors excludes every intermediate P-normal subgroup. Two distinct
nonzero covectors also witness noncentrality. Thus N < E is a noncentral
chief interval in the original ambient group, with normality relative to P.

This is the radical chief factor used in Aschbacher–Smith, combined
manuscript (1 March 2004), 15.3.24, printed pp.1129–1130. It uses neither
the C.1.34 classification nor an MS-pair realization.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra.BinaryFivePointStabilizer
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- The coefficient isomorphism on the line, normalized by the marked vector x. -/
noncomputable def radicalCoefficient {x : Space 4} (hx : x ≠ 0) :
    line x ≃ₗ[ZMod 2] ZMod 2 := LinearEquiv.coord (ZMod 2) (Space 4) x hx

/-- Postcomposition by the coefficient map identifies displacements with covectors. -/
noncomputable def radicalDisplacementDual {x : Space 4} (hx : x ≠ 0) :
    (pointQuotient x →ₗ[ZMod 2] line x) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (pointQuotient x) :=
  LinearEquiv.congrRight (radicalCoefficient hx)

/-- The covector of an element of the intrinsic parabolic two-core. -/
noncomputable def radicalProjection (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    pCore 2 (point h x) →* Multiplicative (Module.Dual (ZMod 2) (pointQuotient x)) :=
  ((radicalDisplacementDual hx).toAddEquiv.toMultiplicative.toMonoidHom.comp
    (kernelDisplacementEquiv x).toMonoidHom).comp (coreActor h x)

/-- The genuine intrinsic radical quotient, marked as the dual of V/⟨x⟩. -/
noncomputable def radicalQuotientEquiv [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    (pCore 2 (point h x) ⧸ oldCoreInCore h x) ≃*
      Multiplicative (Module.Dual (ZMod 2) (pointQuotient x)) :=
  ((coreQuotientEquivKernel h x).trans (kernelDisplacementEquiv x)).trans
    (radicalDisplacementDual hx).toAddEquiv.toMultiplicative

/-- The intrinsic quotient marking on every original representative. -/
@[simp] theorem radicalQuotientEquiv_mk [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (q : pCore 2 (point h x)) :
    radicalQuotientEquiv h hx (QuotientGroup.mk' _ q) = radicalProjection h hx q := rfl

/-- Every covector is realized by an element of the original parabolic core. -/
theorem radicalProjection_surjective [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) : Function.Surjective (radicalProjection h hx) :=
  (radicalDisplacementDual hx).toAddEquiv.toMultiplicative.surjective.comp
    ((kernelDisplacementEquiv x).surjective.comp (coreActor_surjective h x))

/-- The kernel is the old component core in the two successive subgroup carriers. -/
theorem radicalProjection_ker (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    (radicalProjection h hx).ker = oldCoreInCore h x := by
  ext q
  change radicalProjection h hx q = 1 ↔ q ∈ oldCoreInCore h x
  change (radicalDisplacementDual hx).toAddEquiv.toMultiplicative
    (kernelDisplacementEquiv x (coreActor h x q)) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  exact SetLike.ext_iff.mp (coreActor_ker h x) q

/-- Evaluation of the covector is the coefficient of the shear displacement. -/
@[simp] theorem radicalProjection_apply (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (q : pCore 2 (point h x)) (v : Space 4) :
    (radicalProjection h hx q).toAdd ((line x).mkQ v) =
      radicalCoefficient hx (kernelDisplacement x (coreActor h x q) ((line x).mkQ v)) := by
  change radicalCoefficient hx
    ((kernelDisplacementEquiv x (coreActor h x q)).toAdd ((line x).mkQ v)) = _
  rw [kernelDisplacementEquiv_apply, toAdd_ofAdd]

/-- The marked covector is the coefficient of the actual displacement along x. -/
theorem radicalProjection_displacement (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (q : pCore 2 (point h x)) (v : Space 4) :
    (radicalProjection h hx q).toAdd ((line x).mkQ v) • x =
      (pointActor h x q.val).val v - v := by
  rw [radicalProjection_apply]
  exact (LinearEquiv.coord_apply_smul (ZMod 2) (Space 4) x hx
    (kernelDisplacement x (coreActor h x q) ((line x).mkQ v))).trans
      (kernelDisplacement_mk x (coreActor h x q) v)

/-- Literal conjugation in the intrinsic core by an original element of P. -/
noncomputable def radicalConjugate (h : NaturalDual d L) (x : Space 4)
    (p : point h x) (q : pCore 2 (point h x)) : pCore 2 (point h x) :=
  ⟨p * q.val * p⁻¹,
    (inferInstance : (pCore 2 (point h x)).Normal).conj_mem q.val q.property p⟩

/-- The radical action is the contragredient of the already marked quotient action. -/
theorem radicalProjection_conj (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (p : point h x) (q : pCore 2 (point h x)) :
    (radicalProjection h hx (radicalConjugate h x p q)).toAdd =
      (quotientActor h x p).symm.dualMap (radicalProjection h hx q).toAdd := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change (radicalProjection h hx (radicalConjugate h x p q)).toAdd ((line x).mkQ v) =
      (radicalProjection h hx q).toAdd ((line x).mkQ ((pointActor h x p).val.symm v))
    rw [radicalProjection_apply, radicalProjection_apply]
    apply congrArg (radicalCoefficient hx)
    apply Subtype.ext
    rw [kernelDisplacement_mk, kernelDisplacement_mk]
    have he := coreActor_conj h x p q
    have hev := congrArg (fun a : pointStabilizer x => a.val v) he
    change (coreActor h x (radicalConjugate h x p q)).val.val v =
      (pointActor h x p).val ((coreActor h x q).val.val ((pointActor h x p).val.symm v)) at hev
    rw [hev]
    have hf := fixes_line x (pointActor h x p)
      ((coreActor h x q).val.val ((pointActor h x p).val.symm v) -
        (pointActor h x p).val.symm v)
      ((mem_kernel_iff x (coreActor h x q).val).mp (coreActor h x q).property _)
    rw [map_sub, LinearEquiv.apply_symm_apply] at hf
    exact hf

/-- The quotient marking uses precisely the common actor of the two module factors. -/
theorem radicalQuotientEquiv_conj [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (p : point h x) (q : pCore 2 (point h x)) :
    (radicalQuotientEquiv h hx (QuotientGroup.mk' _ (radicalConjugate h x p q))).toAdd =
      (commonActorEquiv h x (QuotientGroup.mk' _ p)).symm.dualMap
        (radicalQuotientEquiv h hx (QuotientGroup.mk' _ q)).toAdd :=
  radicalProjection_conj h hx p q

/-- The intrinsic core identified with its subtype image E in the ambient group. -/
noncomputable def radicalCoreEquiv (h : NaturalDual d L) (x : Space 4) :
    pCore 2 (point h x) ≃* (point h x).pCoreIn 2 :=
  (pCore 2 (point h x)).equivMapOfInjective (point h x).subtype Subtype.val_injective

/-- The intrinsic-to-ambient identification preserves the original group element. -/
@[simp] theorem radicalCoreEquiv_apply (h : NaturalDual d L) (x : Space 4)
    (q : pCore 2 (point h x)) :
    (radicalCoreEquiv h x q : G) = (q.val : G) := rfl

/-- The old core maps to exactly N viewed inside the ambient E. -/
theorem radicalCoreEquiv_oldCore (h : NaturalDual d L) (x : Space 4) :
    (oldCoreInCore h x).map (radicalCoreEquiv h x).toMonoidHom =
      (L.pCoreIn 2).subgroupOf ((point h x).pCoreIn 2) := by
  ext q
  obtain ⟨r, rfl⟩ := (radicalCoreEquiv h x).surjective q
  constructor
  · rintro ⟨s, hs, he⟩
    have hh : s = r := (radicalCoreEquiv h x).injective he
    exact hh ▸ hs
  · intro hr
    exact mem_map.mpr ⟨r, hr, rfl⟩

/-- The same covector projection on the ambient subgroup E. -/
noncomputable def ambientRadicalProjection (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    (point h x).pCoreIn 2 →* Multiplicative (Module.Dual (ZMod 2) (pointQuotient x)) :=
  (radicalProjection h hx).comp (radicalCoreEquiv h x).symm.toMonoidHom

/-- The intrinsic and ambient projections agree under the subtype identification. -/
@[simp] theorem ambientRadicalProjection_core (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (q : pCore 2 (point h x)) :
    ambientRadicalProjection h hx (radicalCoreEquiv h x q) = radicalProjection h hx q := by
  simp [ambientRadicalProjection]

/-- The projection from the ambient core E is onto the whole dual space. -/
theorem ambientRadicalProjection_surjective [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) : Function.Surjective (ambientRadicalProjection h hx) :=
  (radicalProjection_surjective h hx).comp (radicalCoreEquiv h x).symm.surjective

/-- The ambient projection kills exactly the relative subgroup N of E. -/
theorem ambientRadicalProjection_ker (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    (ambientRadicalProjection h hx).ker = (L.pCoreIn 2).subgroupOf ((point h x).pCoreIn 2) := by
  ext q
  obtain ⟨r, rfl⟩ := (radicalCoreEquiv h x).surjective q
  change ambientRadicalProjection h hx (radicalCoreEquiv h x r) = 1 ↔ _
  rw [ambientRadicalProjection_core]
  exact SetLike.ext_iff.mp (radicalProjection_ker h hx) r

/-- The original point parabolic normalizes its ambient two-core. -/
theorem radicalCore_normalized (h : NaturalDual d L) (x : Space 4) :
    point h x ≤ normalizer ((point h x).pCoreIn 2 : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 (point h x))).mp
    (pointCore_normal h x)

/-- Ambient conjugation has the same contragredient marking. -/
theorem ambientRadicalProjection_conj (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (p : point h x) (q : (point h x).pCoreIn 2) :
    (ambientRadicalProjection h hx (conjugate _ _ (radicalCore_normalized h x) p q)).toAdd =
      (quotientActor h x p).symm.dualMap (ambientRadicalProjection h hx q).toAdd := by
  obtain ⟨r, rfl⟩ := (radicalCoreEquiv h x).surjective q
  have he : conjugate _ _ (radicalCore_normalized h x) p (radicalCoreEquiv h x r) =
      radicalCoreEquiv h x (radicalConjugate h x p r) := rfl
  rw [he, ambientRadicalProjection_core, ambientRadicalProjection_core]
  exact radicalProjection_conj h hx p r

/-- The component core is normal relative to the ambient parabolic core. -/
instance componentCoreInPointCore_normal (h : NaturalDual d L) (x : Space 4) :
    ((L.pCoreIn 2).subgroupOf ((point h x).pCoreIn 2)).Normal :=
  normal_subgroupOf_of_le_normalizer ((pCoreIn_le 2 (point h x)).trans
    ((normal_subgroupOf_iff_le_normalizer (componentCore_le_point h x)).mp
      (componentCore_normal h x)))

/-- The actual ambient section E/N, with its specified dual marking. -/
noncomputable def ambientRadicalQuotientEquiv [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    ((point h x).pCoreIn 2 ⧸ (L.pCoreIn 2).subgroupOf ((point h x).pCoreIn 2)) ≃*
      Multiplicative (Module.Dual (ZMod 2) (pointQuotient x)) :=
  (QuotientGroup.quotientMulEquivOfEq (ambientRadicalProjection_ker h hx).symm).trans
    (@QuotientGroup.quotientKerEquivOfSurjective ((point h x).pCoreIn 2) inferInstance
      (Multiplicative (Module.Dual (ZMod 2) (pointQuotient x))) inferInstance
      (ambientRadicalProjection h hx) (ambientRadicalProjection_surjective h hx))

/-- The ambient section marking on representatives. -/
@[simp] theorem ambientRadicalQuotientEquiv_mk [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (q : (point h x).pCoreIn 2) :
    ambientRadicalQuotientEquiv h hx (QuotientGroup.mk' _ q) =
      ambientRadicalProjection h hx q := rfl

/-- The two quotient markings agree on each intrinsic-core representative. -/
@[simp] theorem ambientRadicalQuotientEquiv_core_mk [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (q : pCore 2 (point h x)) :
    ambientRadicalQuotientEquiv h hx (QuotientGroup.mk' _ (radicalCoreEquiv h x q)) =
      radicalQuotientEquiv h hx (QuotientGroup.mk' _ q) :=
  ambientRadicalProjection_core h hx q

private theorem radical_orbit (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (q : (point h x).pCoreIn 2) (hq : (ambientRadicalProjection h hx q).toAdd ≠ 0)
    (v : Module.Dual (ZMod 2) (pointQuotient x)) (hv : v ≠ 0) :
    ∃ p : point h x,
      (ambientRadicalProjection h hx (conjugate _ _ (radicalCore_normalized h x) p q)).toAdd = v := by
  obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq hq hv
  obtain ⟨a, rfl⟩ := (dualGroupEquiv (V := pointQuotient x)).surjective g
  obtain ⟨p, rfl⟩ := quotientActor_surjective h x a
  exact ⟨p, (ambientRadicalProjection_conj h hx p q).trans hg⟩

private theorem radical_mem_of_projection_eq (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (D : Subgroup G) (hND : L.pCoreIn 2 ≤ D)
    (q r : (point h x).pCoreIn 2)
    (he : ambientRadicalProjection h hx q = ambientRadicalProjection h hx r)
    (hr : (r : G) ∈ D) : (q : G) ∈ D := by
  have hk : q * r⁻¹ ∈ (ambientRadicalProjection h hx).ker := by
    change ambientRadicalProjection h hx (q * r⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [ambientRadicalProjection_ker] at hk
  have hm := D.mul_mem (hND hk) hr
  change ((q : G) * (r : G)⁻¹) * (r : G) ∈ D at hm
  simpa only [inv_mul_cancel_right] using hm

private theorem radical_chief (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (D : Subgroup G) (hND : L.pCoreIn 2 ≤ D) (hDE : D ≤ (point h x).pCoreIn 2)
    (hDn : (D.subgroupOf (point h x)).Normal) :
    D = L.pCoreIn 2 ∨ D = (point h x).pCoreIn 2 := by
  by_cases hDN : D ≤ L.pCoreIn 2
  · exact Or.inl (le_antisymm hDN hND)
  right
  obtain ⟨a, ha, haN⟩ := SetLike.not_le_iff_exists.mp hDN
  let q : (point h x).pCoreIn 2 := ⟨a, hDE ha⟩
  have hq : (ambientRadicalProjection h hx q).toAdd ≠ 0 := by
    intro hz
    have hk : q ∈ (ambientRadicalProjection h hx).ker := hz
    rw [ambientRadicalProjection_ker] at hk
    exact haN hk
  apply le_antisymm hDE
  intro b hb
  let r : (point h x).pCoreIn 2 := ⟨b, hb⟩
  by_cases hr : (ambientRadicalProjection h hx r).toAdd = 0
  · have hk : r ∈ (ambientRadicalProjection h hx).ker := hr
    rw [ambientRadicalProjection_ker] at hk
    exact hND hk
  obtain ⟨p, hp⟩ := radical_orbit h hx q hq (ambientRadicalProjection h hx r).toAdd hr
  apply radical_mem_of_projection_eq h hx D hND r
    (conjugate _ _ (radicalCore_normalized h x) p q)
    (congrArg Multiplicative.ofAdd hp.symm)
  exact hDn.conj_mem (⟨a, pCoreIn_le 2 (point h x) q.property⟩ : point h x) ha p

private theorem radical_noncentral [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    ¬ ⁅point h x, (point h x).pCoreIn 2⁆ ≤ L.pCoreIn 2 := by
  classical
  let V := Module.Dual (ZMod 2) (pointQuotient x)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  have hc : Fintype.card V = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (radicalQuotientEquiv h hx).toEquiv).symm.trans (coreQuotient_card h hx)
  have h0 : ({0} : Finset V).card < (Finset.univ : Finset V).card := by simp [hc]
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card h0
  have ha0 : a ≠ 0 := by simpa only [Finset.mem_singleton] using ha
  have h1 : ({0, a} : Finset V).card < (Finset.univ : Finset V).card := by
    have hp : ({0, a} : Finset V).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, hc]
    omega
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
  have hb0 : b ≠ 0 ∧ b ≠ a := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hb
  obtain ⟨q, hq⟩ := ambientRadicalProjection_surjective h hx (Multiplicative.ofAdd a)
  have hqa : (ambientRadicalProjection h hx q).toAdd = a := congrArg Multiplicative.toAdd hq
  obtain ⟨p, hp⟩ := radical_orbit h hx q (hqa ▸ ha0) b hb0.1
  intro hn
  let r := conjugate _ _ (radicalCore_normalized h x) p q
  have hk : r * q⁻¹ ∈ (ambientRadicalProjection h hx).ker := by
    rw [ambientRadicalProjection_ker]
    exact hn (commutator_mem_commutator p.property q.property)
  have he : ambientRadicalProjection h hx r = ambientRadicalProjection h hx q := by
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    exact hk
  exact hb0.2 (hp.symm.trans ((congrArg Multiplicative.toAdd he).trans hqa))

/-- The radical interval is chief and noncentral for the original point parabolic. -/
theorem radical_interval_chief [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    IsNoncentralChiefInterval h x (L.pCoreIn 2) ((point h x).pCoreIn 2) where
  strict := componentCore_lt_pointCore h hx
  upper_le := pCoreIn_le 2 (point h x)
  lower_normal := componentCore_normal h x
  upper_normal := pointCore_normal h x
  chief := radical_chief h hx
  noncentral := radical_noncentral h hx

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
end
