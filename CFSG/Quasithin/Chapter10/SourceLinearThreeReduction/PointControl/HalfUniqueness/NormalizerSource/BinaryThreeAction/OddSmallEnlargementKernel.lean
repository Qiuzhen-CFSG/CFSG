module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallTrivialImage
public import Theory.GroupTheory.PCoreFrattiniDisplacement

/-!
# Absorbing the original module in the enlargement core

Write `Q = O₂(K)`, `R = O₂(E)` and `R₀ = O₂(L₀T)`. The collapsed original
parabolic satisfies `O₂(H) = QR₀`, while `R ≤ O₂(H)` and `R₀` centralizes
the original module `V`. Consequently `[V,Q] ≤ Φ(Q)` gives
`[V,R] ≤ Φ(Q) ≤ Φ(R)`. Characteristic two for the actual enlargement then
places `V` in `R` by the exact Frattini-action kernel.

The final source theorem retains the original witnesses and the noncentral
action of `R` on `V`. Containment in `R` does not assert containment in `K`
or finish the normalization argument.
Source: Aschbacher--Smith 10.2.5, printed p.748; Burnside's basis theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The collapsed parabolic transfers the original displacement into the
Frattini subgroup of the actual enlargement core. -/
theorem Data.trivial_image_enlargement_frattini_displacement
    (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (ha : moduleFrattiniImage D H = ⊥) :
    ⁅D.fullModule,(enlargement T L H).pCoreIn 2⁆ ≤
      (frattini ((enlargement T L H).pCoreIn 2)).map
        ((enlargement T L H).pCoreIn 2).subtype := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let R := (enlargement T L H).pCoreIn 2
  let R₀ := (localJoin T L).pCoreIn 2
  have hQR : Q ≤ R := pCoreIn_mono_of_normalizes h.enlargedResidual_le_enlargement
    (le_normalizer_conjugateSpanBy _ _)
  have hphi : (frattini Q).map Q.subtype ≤ (frattini R).map R.subtype :=
    frattini_image_le_of_le hQR (isPGroup_pCoreIn 2 _)
  have hRQ : R ≤ Q ⊔ R₀ := h.enlargement_core_le_parabolic_core.trans
    (h.collapsed_parabolic_core_eq_join f hi hP hc).le
  have hR₀H : R₀ ≤ H := (join_core_le_stabilizer D).trans (inf_le_left.trans h.sylow_le)
  have hR₀Q : R₀ ≤ normalizer (Q : Set G) :=
    (hR₀H.trans le_sup_right).trans (enlargement_normalizes_core T L H)
  have hR₀C : R₀ ≤ centralizer (D.fullModule : Set G) := by
    rintro _ ⟨q,hq,rfl⟩
    rw [←f.kernel_eq_join_core,f.kernel_eq_action_kernel,joinAction_ker] at hq
    exact hq
  have hVQ := (h.moduleFrattiniImage_eq_bot_iff s.full_eq_local).mp ha
  apply commutator_le.mpr
  intro v hv r hr
  have hrprod : r ∈ (Q : Set G) * (R₀ : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left Q R₀ hR₀Q]
    exact hRQ hr
  obtain ⟨q,hq,c,hc,he⟩ := hrprod
  rw [←he,commutatorElement_mul_right_eq_mul_conj,
    (mem_centralizer_iff_commutator_eq_one.mp (hR₀C hc)) v hv,
    mul_one,mul_inv_cancel_right]
  exact hphi (hVQ (commutator_mem_commutator hv hq))

/-- The actual enlargement has characteristic two, so the transferred
Frattini displacement forces the original module into its two-core. -/
theorem Data.trivial_image_fullModule_le_enlargement_core
    (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (ha : moduleFrattiniImage D H = ⊥) :
    D.fullModule ≤ (enlargement T L H).pCoreIn 2 := by
  have he : enlargement T L H ∈ He G := lemma_1_1_4_6 T (D.simpleQTKE.evenCharacteristic T)
    ⟨h.enlargement_mem_H hn,h.sylow_le.trans le_sup_right⟩
  exact le_pCoreIn_of_frattini_displacement _ _ (h.fullModule_le_enlargement s.full_eq_local)
    (mem_He_iff.mp he) (h.trivial_image_enlargement_frattini_displacement f hi hP hc ha)

variable {I : Subgroup G}

/-- The native low-torus exclusion supplies the trivial image; no module
placement or trivial-action premise is added to the original local inputs. -/
theorem Data.fullModule_le_enlargement_core
    (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    D.fullModule ≤ (enlargement T L H).pCoreIn 2 :=
  h.trivial_image_fullModule_le_enlargement_core f hn hs.toLocalInput hP hc
    (h.moduleFrattiniImage_eq_bot f hn hs hK hp ho hm hmod hP hc)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open BinaryThreeAction BinaryThreeAction.Parabolics Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original enlargement absorbs the original module in its normal
two-core, retaining that core's genuinely noncentral action. -/
theorem SourceCubicNormalizerEnlargement.exists_enlargement_core_absorption
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ _h : Data D H,
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      moduleFrattiniImage D H = ⊥ ∧
      D.fullModule ≤ (enlargement T L H).pCoreIn 2 ∧
      ⁅D.fullModule,(enlargement T L H).pCoreIn 2⁆ ≤
        (frattini ((enlargement T L H).pCoreIn 2)).map
          ((enlargement T L H).pCoreIn 2).subtype ∧
      ¬ (enlargement T L H).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  have ha := h.moduleFrattiniImage_eq_bot f hn hs hK hp ho hm h24 hP hcollapse
  exact ⟨H,P,h,hs.toLocalInput,ha,
    h.trivial_image_fullModule_le_enlargement_core f hn hs.toLocalInput hP hcollapse ha,
    h.trivial_image_enlargement_frattini_displacement f hs.toLocalInput hP hcollapse ha,
    h.collapsed_enlargement_core_moves_fullModule hn hmodel hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
