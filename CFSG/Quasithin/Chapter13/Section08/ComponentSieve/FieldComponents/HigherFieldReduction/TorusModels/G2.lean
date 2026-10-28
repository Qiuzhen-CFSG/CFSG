module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelResidual
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelFixer
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelCommutator
public import Theory.SpecificGroups.SL2.EvenBorelResidual.TwoPowerField
public import Theory.GroupAction.InnerSylow
public import Theory.GroupAction.CyclicCommutatorTransport
public import Theory.GroupTheory.SylowKernelCore

/-!
# Intrinsic G₂ Borel calculations for 13.8.20

For the actual octonion model, the Borel at a specified Sylow two-subgroup
is its normalizer, is two-perfect when q > 2, has that Sylow as its two-core,
and has quotient Fˣ × Fˣ. The imported action calculations derive Borel
placement from Sylow stabilization and identify the resulting field action.
They also prove the outer-actor commutator bound in the standard marking,
including G₂(4), and reduce the exact source residual-torus fixation condition
to fixation of O³(Fˣ).

The actor assembly excludes nontrivial two-power field actors outside degrees
two and six, transports the fixation statement to every Sylow marking, and
retains the exact inner Sylow image. The outer commutator bound is transported
in the same way, including both exceptional degrees. Inner–field coverage
remains the explicit earlier input permitted by this calculation's contract.
The imported `central_kernel_le_torusCentralizer` retains C_T(K) on ambient
lifting.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
The concrete G₂ construction is the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.G2
open Subgroup Atlas.G2 Atlas.G2.EvenBorelTorus Atlas.G2.LieAutomorphismExtensions
open Theory.GroupAction.OddCommutatorImage
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Field F] [Finite F] [CharP F 2] in
private theorem card_gt_two {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    2 < Nat.card F := by
  rw [hF]
  have h : (2 : ℕ) ^ 1 < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn
  simpa using h

/-- The Borel at the specified Sylow, with no model-identification premise. -/
abbrev borelAt (S : Sylow 2 (Model F)) : Subgroup (Model F) :=
  normalizer (S : Set (Model F))

/-- The source two-residual is the whole intrinsic G₂ Borel. -/
theorem borelAt_residual {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Model F)) : borelResidual (borelAt S) = borelAt S := by
  rw [borelResidual, residualIn, sylowNormalizer_twoResidual (card_gt_two hF hn) S,
    ← MonoidHom.range_eq_map, range_subtype]

omit [Finite F] [CharP F 2] in
/-- The Borel's two-core is precisely the specified Sylow subgroup. -/
theorem borelAt_twoCore (S : Sylow 2 (Model F)) : (borelAt S).pCoreIn 2 = S :=
  sylowNormalizer_twoCoreIn S

/-- Both B₀ and the source B have the same intrinsic two-core. -/
theorem residual_borelAt_twoCore {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Model F)) : (borelResidual (borelAt S)).pCoreIn 2 = S := by
  rw [borelAt_residual hF hn S, borelAt_twoCore]

/-- The actual quotient of the source residual B, in any Sylow marking. -/
noncomputable def residualBorelAtQuotientEquiv {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 (Model F)) :
    borelResidual (borelAt S) ⧸ pCore 2 (borelResidual (borelAt S)) ≃* (Fˣ × Fˣ) := by
  let e := MulEquiv.subgroupCongr (borelAt_residual hF hn S)
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (sylowNormalizerQuotientEquiv S)

/-- Cardinality follows from the constructed multiplicative equivalence. -/
theorem card_residualBorelAtQuotient {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 (Model F)) :
    Nat.card (borelResidual (borelAt S) ⧸ pCore 2 (borelResidual (borelAt S))) =
      (2 ^ n - 1) ^ 2 := by
  rw [Nat.card_congr (residualBorelAtQuotientEquiv hF hn S).toEquiv,
    Nat.card_prod, Nat.card_units, hF, pow_two]

/-- The same residual equality in the root-coordinate marking. -/
theorem standard_borelResidual {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    borelResidual (borel (K := F)) = borel := by
  rw [borelResidual, residualIn, borel_twoResidual (card_gt_two hF hn),
    ← MonoidHom.range_eq_map, range_subtype]

/-- This is the source numerator O³(B)O₂(B), interpreted in the actual model.
No Borel placement or torus-action premise is assumed. -/
theorem standard_source_fixer_iff {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : unipotent.map (semilinearAction z).toMonoidHom = unipotent) :
    (∀ x ∈ residualIn 3 (borelResidual (borel (K := F))) ⊔
        (borelResidual (borel (K := F))).pCoreIn 2,
      semilinearAction z x * x⁻¹ ∈ (borelResidual (borel (K := F))).pCoreIn 2) ↔
      ∀ u ∈ pResidual 3 Fˣ, Units.map z.right.toMonoidHom u = u := by
  rw [standard_borelResidual hF hn]
  exact semilinear_fixes_fullSection_iff z hz

/-- Outer actors have large actual Borel commutators, including at q = 4.
This bound holds in all degrees, hence in both source exceptional degrees. -/
theorem standard_outer_commutator_gt_three {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (α : MulAut (Model F)) (hα : unipotent.map α.toMonoidHom = unipotent)
    (hout : α ∉ MulAut.innerSubgroup (Model F)) :
    let C := commutatorSubgroup (zpowers α) (Model F) (borelResidual (borel (K := F)))
    3 < Nat.card (C ⧸ pCore 2 C) := by
  rw [standard_borelResidual hF hn]
  exact outer_commutator_quotient_gt_three hcover α hα hout


omit [Finite F] [CharP F 2] in
private theorem inner_core_fixes_at (B : Subgroup (Model F))
    {s : Model F} (hs : s ∈ B.pCoreIn 2) :
    ∀ x ∈ (residualIn 3 B ⊔ B.pCoreIn 2),
      (MulAut.conj s) x * x⁻¹ ∈ B.pCoreIn 2 := by
  intro x hx
  have hxb : x ∈ B := (sup_le (map_subtype_le _) (pCoreIn_le 2 B)) hx
  let b : B := ⟨x,hxb⟩
  obtain ⟨u,hu,rfl⟩ := hs
  refine ⟨u * b * u⁻¹ * b⁻¹, ?_, rfl⟩
  have hc := (inferInstance : (pCore 2 B).Normal).conj_mem u⁻¹
    ((pCore 2 B).inv_mem hu) b
  change u * b * u⁻¹ * b⁻¹ ∈ pCore 2 B
  simpa only [mul_assoc] using (pCore 2 B).mul_mem hu hc

/-- Standard G2 fixer, for an actor stabilizing the standard positive-root Sylow. -/
theorem standard_fixer_is_inner {n k : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (α : MulAut (Model F))
    (hstable : unipotent.map α.toMonoidHom = unipotent)
    (hpow : α ^ (2 ^ k) = 1)
    (hfix : FixesResidualTorus α) :
    α ∈ unipotent.map (MulAut.conj : Model F →* MulAut (Model F)) := by
  obtain ⟨z,rfl⟩ := hcover α
  have hfpow : z.right ^ (2 ^ k) = 1 :=
    field_part_two_power (card_gt_two hF hn) z k (by simpa using hpow)
  have hffix : ∀ u ∈ pResidual 3 Fˣ, Units.map z.right.toMonoidHom u = u :=
    (semilinear_fixesResidualTorus_iff z hstable).mp hfix
  have hσ : z.right = 1 := by
    by_contra hne
    rcases FiniteField.BinaryTorusTwoPower.degree_eq_two_or_six_of_fixed_residual
      z.right hn hF hne hfpow hffix with h | h
    · exact hn2 h
    · exact hn6 h
  exact (inner_sylow_iff_field_part_one (card_gt_two hF hn) z hstable k
    (by simpa using hpow)).mpr hσ

/-- The actual source fixer at an arbitrary Sylow marking. -/
def FixesResidualTorusAt (S : Sylow 2 (Model F)) (α : MulAut (Model F)) : Prop :=
  ∀ x ∈ residualIn 3 (borelResidual (borelAt S)) ⊔
      (borelResidual (borelAt S)).pCoreIn 2,
    α x * x⁻¹ ∈ (borelResidual (borelAt S)).pCoreIn 2

private theorem standard_borelAt :
    borelAt (Atlas.G2.LieParabolicSetup.sylow (F := F)) = borel := by
  change normalizer (unipotent (K := F) : Set (Model F)) = borel
  exact SylowNormalizer.normalizer_unipotent

private theorem standard_borelResidualAt {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    borelResidual (borelAt (Atlas.G2.LieParabolicSetup.sylow (F := F))) = borel := by
  rw [standard_borelAt, standard_borelResidual hF hn]

private theorem fixesAt_to_standard {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Model F)) (α : MulAut (Model F))
    (_hstable : (S : Subgroup (Model F)).map α.toMonoidHom = S)
    (hfix : FixesResidualTorusAt S α) :
    FixesResidualTorus (MulAut.congr (MulAut.conj (Classical.choose
      (sylow_normalizer_conjugate S))).symm α) := by
  let g := Classical.choose (sylow_normalizer_conjugate S)
  have hg := Classical.choose_spec (sylow_normalizer_conjugate S)
  let e : Model F ≃* Model F := MulAut.conj g
  let β : MulAut (Model F) := MulAut.congr e.symm α
  have hU : (unipotent : Subgroup (Model F)).map e.toMonoidHom = S := hg.1
  have hB0 : borel.map e.toMonoidHom = borelAt S := hg.2
  have hB : (borelResidual (borelAt (Atlas.G2.LieParabolicSetup.sylow (F := F)))).map e.toMonoidHom =
      borelResidual (borelAt S) := by
    rw [standard_borelAt]
    unfold borelResidual residualIn
    rw [map_embedded_pResidual, hB0]
  have hR : (residualIn 3 (borelResidual (borelAt (Atlas.G2.LieParabolicSetup.sylow (F := F))))).map e.toMonoidHom =
      residualIn 3 (borelResidual (borelAt S)) := by
    unfold residualIn
    rw [map_embedded_pResidual, hB]
  have hein : Function.Injective e.toMonoidHom := by
    intro x y h
    exact e.injective h
  have hC : ((borelResidual (borelAt (Atlas.G2.LieParabolicSetup.sylow (F := F)))).pCoreIn 2).map e.toMonoidHom =
      (borelResidual (borelAt S)).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ e.toMonoidHom hein, hB]
  have hCstd : (borel.pCoreIn 2).map e.toMonoidHom =
      (borelResidual (borelAt S)).pCoreIn 2 := by
    rw [← standard_borelResidualAt hF hn]
    exact hC
  have hβ : β = MulAut.congr e.symm α := rfl
  change ∀ b : borel, b ∈ pResidual 3 borel →
      β b.val * b.val⁻¹ ∈ borel.pCoreIn 2
  intro b hb
  have hbmem : b.val ∈ residualIn 3 (borelResidual (borelAt (Atlas.G2.LieParabolicSetup.sylow (F := F)))) := by
    rw [standard_borelResidualAt hF hn]
    exact mem_map_of_mem borel.subtype hb
  have hemem : e b.val ∈ residualIn 3 (borelResidual (borelAt S)) := by
    have hm := mem_map_of_mem e.toMonoidHom hbmem
    rw [hR] at hm
    exact hm
  have h := hfix (e b.val) (mem_sup_left hemem)
  apply (mem_map_iff_mem (f := e.toMonoidHom) hein).mp
  change e (β b.val * b.val⁻¹) ∈ (borel.pCoreIn 2).map e.toMonoidHom
  rw [hCstd]
  simpa [β, MulAut.congr] using h


/-- At an arbitrary specified Sylow, source fixation detects exactly the inner
Sylow actors outside the two exceptional field degrees. -/
theorem fixesResidualTorusAt_iff_innerSylow {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (S : Sylow 2 (Model F)) (A : Subgroup (MulAut (Model F)))
    (hA : IsPGroup 2 A)
    (hstable : ∀ a ∈ A, (S : Subgroup (Model F)).map a.toMonoidHom = S)
    (hinner : (S : Subgroup (Model F)).map (MulAut.conj : Model F →* MulAut (Model F)) ≤ A)
    {α : MulAut (Model F)} (hα : α ∈ A) :
    FixesResidualTorusAt S α ↔
      α ∈ (S : Subgroup (Model F)).map (MulAut.conj : Model F →* MulAut (Model F)) := by
  constructor
  · intro hfix
    let g := Classical.choose (sylow_normalizer_conjugate S)
    let e : Model F ≃* Model F := MulAut.conj g
    let β : MulAut (Model F) := MulAut.congr e.symm α
    have hg := Classical.choose_spec (sylow_normalizer_conjugate S)
    have hβstable : unipotent.map β.toMonoidHom = unipotent :=
      MulAut.aligned_actor_stable e unipotent (S : Subgroup (Model F)) hg.1 α
        (hstable α hα)
    obtain ⟨k,hk⟩ := hA ⟨α,hα⟩
    have hαpow : α ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hβpow : β ^ (2 ^ k) = 1 := by
      change (MulAut.congr e.symm α) ^ (2 ^ k) = 1
      rw [← map_pow, hαpow, map_one]
    have hβfix : FixesResidualTorus β := by
      simpa [β, e, g] using
        (fixesAt_to_standard hF hn S α (hstable α hα) hfix)
    have hβU := standard_fixer_is_inner hF hn hn2 hn6 hcover β hβstable hβpow hβfix
    have hβinner : β ∈ MulAut.innerSubgroup (Model F) := by
      obtain ⟨u,hu,huβ⟩ := hβU
      exact ⟨u,huβ⟩
    have hαinner : α ∈ MulAut.innerSubgroup (Model F) :=
      MulAut.inner_of_aligned_inner e α hβinner
    exact MulAut.mem_innerSylow_of_mem_inner S A hA hinner hα hαinner
  · rintro ⟨s,hs,rfl⟩
    unfold FixesResidualTorusAt
    apply inner_core_fixes_at (borelResidual (borelAt S))
    rw [residual_borelAt_twoCore hF hn S]
    exact hs


/-- Outer actors in either source exceptional degree have a large actual
commutator quotient at every Sylow marking. -/
theorem exceptional_outer_commutator_gt_three {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (_hex : n = 2 ∨ n = 6)
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (S : Sylow 2 (Model F)) (A : Subgroup (MulAut (Model F)))
    (_hA : IsPGroup 2 A)
    (hstable : ∀ a ∈ A, (S : Subgroup (Model F)).map a.toMonoidHom = S)
    (_hinner : (S : Subgroup (Model F)).map
      (MulAut.conj : Model F →* MulAut (Model F)) ≤ A)
    {α : MulAut (Model F)} (hα : α ∈ A)
    (hout : α ∉ MulAut.innerSubgroup (Model F)) :
    let C := commutatorSubgroup (zpowers α) (Model F)
      (borelResidual (borelAt S))
    3 < Nat.card (C ⧸ pCore 2 C) := by
  let g := Classical.choose (sylow_normalizer_conjugate S)
  let e : Model F ≃* Model F := MulAut.conj g
  let β : MulAut (Model F) := MulAut.congr e.symm α
  have hg := Classical.choose_spec (sylow_normalizer_conjugate S)
  have hβstable : unipotent.map β.toMonoidHom = unipotent :=
    MulAut.aligned_actor_stable e unipotent (S : Subgroup (Model F)) hg.1 α
      (hstable α hα)
  have hβouter : β ∉ MulAut.innerSubgroup (Model F) := congr_outer e.symm α hout
  have hβbound := standard_outer_commutator_gt_three hF hn hcover β hβstable hβouter
  have hB : borel.map e.toMonoidHom = borelResidual (borelAt S) := by
    rw [borelAt_residual hF hn S]
    exact hg.2
  have hcongr : MulAut.congr e β = α := by
    ext x
    simp [β, MulAut.congr]
  have hcard := card_cyclic_commutator_quotient e β borel
  dsimp only at hcard hβbound
  rw [standard_borelResidual hF hn] at hβbound
  rw [hcongr, hB] at hcard
  dsimp only
  rw [← hcard]
  exact hβbound
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.G2
