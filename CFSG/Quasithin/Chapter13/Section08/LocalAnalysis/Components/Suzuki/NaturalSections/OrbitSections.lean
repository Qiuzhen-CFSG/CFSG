module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FaithfulSections
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SectionRecognition

/-!
# Saturating Suzuki orbit sections

A component orbit with trivial centralizer acts faithfully on every
noncentral section. The full B.5 classification excludes FF-modules
for the single Suzuki actor, its product, and their two-group extensions.
The fixed-codimension bound therefore forces every nonzero invariant
commutator-generated submodule to be the entire moved space. In
particular an actual Irr⁺ section has full T-orbit span.

For a normal single component, an invariant Irr⁺ section is already
the entire moved space. Combining this with the full B.4 recognition
constructs its natural central quotient. The source geometry must still
supply the trivial two-core, bounded actor and invariant section; these
are not consequences of an arbitrary Suzuki representation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.18(6–7), printed pp.325–326, and 13.8.16, pp.952–953.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions

namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.OrbitSections
universe u v
variable {D : Type u} [Group D] [Finite D]

/-- A two-group extension preserves order prime to three. -/
theorem three_free_of_two_quotient (L : Subgroup D) [L.Normal]
    (hq : IsPGroup 2 (D ⧸ L)) (hL : ¬ 3 ∣ Nat.card L) : ¬ 3 ∣ Nat.card D := by
  intro h
  rw [← L.card_mul_index] at h
  rcases Nat.prime_three.dvd_mul.mp h with h | h
  · exact hL h
  · rw [L.index_eq_card] at h
    obtain ⟨n, hn⟩ := hq.exists_card_eq
    rw [hn] at h
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)

/-- The single Suzuki orbit and its two-group supplement have three-free order. -/
theorem three_free_single (L : Subgroup D) [L.Normal]
    (hq : IsPGroup 2 (D ⧸ L)) {m : ℕ} (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m) : ¬ 3 ∣ Nat.card D :=
  three_free_of_two_quotient L hq (RatioRecognition.three_free_of_equiv_suzuki hm e)

/-- The whole product, not a diagonal copy, gives three-free order in the swapped case. -/
theorem three_free_pair (L : Subgroup D) [L.Normal]
    (hq : IsPGroup 2 (D ⧸ L)) {m : ℕ} (hm : 0 < m)
    (e : L ≃* (SuzukiMatrixGroup m × SuzukiMatrixGroup m)) : ¬ 3 ∣ Nat.card D := by
  apply three_free_of_two_quotient L hq
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  exact fun h => (Nat.prime_three.dvd_mul.mp h).elim
    (suzukiMatrixGroup_three_free m hm) (suzukiMatrixGroup_three_free m hm)

/-- The given SQTK actor itself is a finite SQTK cover of its faithful action. -/
noncomputable def selfCover {κ : GroupClass.{u}} (h : IsSQTK κ D) : SQTKQuotient κ D where
  Cover := D
  kernel := ⊥
  sqtk := h
  equiv := QuotientGroup.quotientBot

omit [Finite D] in
/-- Noncentral component-orbit sections are faithful when that orbit has trivial centralizer. -/
theorem faithful_of_noncentral_orbit
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) D V) (K T : Subgroup D)
    (hK : IsComponent D K)
    (hC : centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hn : ¬ ∀ k ∈ conjugateSpanBy K T, ∀ v, σ k v = v) :
    Function.Injective σ := by
  have hk := action_kernel_le_centralizer_of_component_orbit σ K T hK hn
  rw [hC] at hk
  have hf := (MonoidHom.ker_eq_bot_iff (actionHom σ)).mp (bot_unique hk)
  intro x y h
  apply hf
  apply imageRepresentation_injective σ
  exact h

omit [Finite D] in
/-- A centerless normal orbit with two-group quotient has trivial centralizer
when the actor has trivial two-core. This applies to both Suzuki orbit sizes. -/
theorem centralizer_eq_bot_of_centerless_two_quotient
    (L : Subgroup D) [L.Normal] (hz : center L = ⊥)
    (hq : IsPGroup 2 (D ⧸ L)) (h₂ : pCore 2 D = ⊥) :
    centralizer (L : Set D) = ⊥ := by
  let C := centralizer (L : Set D)
  let f : C →* D ⧸ L := (QuotientGroup.mk' L).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxL : (x : D) ∈ L := (QuotientGroup.eq_one_iff _).mp hx
    have hxZ : (⟨x, hxL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      exact Subtype.ext ((mem_centralizer_iff.mp x.property) l l.property)
    rw [hz, mem_bot] at hxZ
    exact Subtype.ext (congrArg (fun l : L => (l : D)) hxZ)
  have hC : IsPGroup 2 C := hq.of_injective f hf
  have hle : C ≤ pCore 2 D := le_sSup ⟨inferInstance, hC⟩
  exact bot_unique (hle.trans h₂.le)

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) D V)

/-- F.9.18(6--7)'s saturation step with the full B.5 classification:
every nonzero invariant full-commutator submodule is the entire moved space.
The two proper sections are proved faithful before applying FF exclusion. -/
theorem generated_submodule_eq_moved
    {κ : GroupClass.{u}} (hB5 : CompleteClassificationInput.{u,v} κ)
    (hD : IsSQTK κ D) (h₂ : pCore 2 D = ⊥) (hthree : ¬ 3 ∣ Nat.card D)
    (K T : Subgroup D) (hK : IsComponent D K)
    (hC : centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (W : Subrepresentation ρ) (hW : W.toSubmodule ≠ ⊥)
    (hgen : subspaceCommutator ρ W.toSubmodule (conjugateSpanBy K T) = W.toSubmodule) :
    W.toSubmodule = subspaceCommutator ρ ⊤ (conjugateSpanBy K T) := by
  by_contra hne
  have hw := faithful_of_noncentral_orbit W.toRepresentation K T hK hC
    (subrepresentation_action_nontrivial ρ W _ hW hgen)
  have hq := faithful_of_noncentral_orbit W.quotientRepresentation K T hK hC
    (quotient_action_nontrivial ρ W _ hgen hne)
  have hnfW := RatioRecognition.not_ff_of_three_free W.toRepresentation hB5 hw h₂
    ⟨selfCover hD⟩ hthree
  have hnfQ := RatioRecognition.not_ff_of_three_free W.quotientRepresentation hB5 hq h₂
    ⟨selfCover hD⟩ hthree
  rcases ff_alternative_of_codim_bound ρ W hA hbound with h | h | h
  · exact hnfW h.1
  · exact hnfW ⟨h.choose, h.choose_spec.1, h.choose_spec.2.le⟩
  · exact hnfQ ⟨h.choose, h.choose_spec.1, h.choose_spec.2.le⟩

/-- The T-orbit of every actual Irr⁺ section is the entire commutator
space under the source ratio bound and the full B.5 exclusion. This is
the saturation argument of F.9.18(7), without a splitting assumption. -/
theorem irrPlus_orbit_eq_moved
    {κ : GroupClass.{u}} (hB5 : CompleteClassificationInput.{u,v} κ)
    (hD : IsSQTK κ D) (h₂ : pCore 2 D = ⊥) (hthree : ¬ 3 ∣ Nat.card D)
    (K T : Subgroup D) (hK : IsComponent D K)
    (hC : centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hgen : conjugateSpanBy K T ⊔ T = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ (conjugateSpanBy K T) I) :
    Cases.orbitSpan ρ T I = subspaceCommutator ρ ⊤ (conjugateSpanBy K T) := by
  let W := Cases.orbitSubrepresentation ρ (le_normalizer_conjugateSpanBy K T) hI hgen
  exact generated_submodule_eq_moved ρ hB5 hD h₂ hthree K T hK hC A hA hbound W
    (Cases.orbitSpan_ne_bot ρ hI)
    (Cases.orbitSpan_full_commutator ρ (le_normalizer_conjugateSpanBy K T) hI)

/-- An invariant Irr⁺ section fills the entire moved space in the
single Suzuki orbit. The complete B.5 input excludes both proper sections. -/
theorem invariant_irrPlus_eq_moved
    {κ : GroupClass.{u}} (hB5 : CompleteClassificationInput.{u,v} κ)
    (hD : IsSQTK κ D) (h₂ : pCore 2 D = ⊥)
    (K : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hquot : IsPGroup 2 (D ⧸ K)) {m : ℕ} (hm : 0 < m)
    (eK : K ≃* SuzukiMatrixGroup m)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hstable : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ I)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    I = subspaceCommutator ρ ⊤ K := by
  have hz := SectionRecognition.center_eq_bot_of_equiv_suzuki eK
  have hC := centralizer_eq_bot_of_centerless_two_quotient K hz hquot h₂
  have hthree := three_free_single K hquot hm eK
  have hcomp : IsComponent D K := ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩
  have horbit : conjugateSpanBy K ⊥ = K :=
    le_antisymm (conjugateSpanBy_le le_rfl bot_le) (le_conjugateSpanBy K ⊥)
  let W : Subrepresentation ρ := ⟨I, fun g _ hv => (hstable (mem_top g) _).2 hv⟩
  have hsat : I = subspaceCommutator ρ ⊤ K := by
    have hs := generated_submodule_eq_moved ρ hB5 hD h₂ hthree K ⊥ hcomp
      (by simpa only [horbit] using hC) A hA hbound W (hI.ne_bot ρ)
      (by simpa only [horbit] using hI.choose_spec.1)
    simpa only [horbit] using hs
  exact hsat

/-- In the single-component invariant branch, saturation and recognition
identify the central quotient of the entire moved space. The input I is
an arbitrary invariant Irr⁺ section, not an assumed natural module. -/
theorem natural_moved_of_invariant_irrPlus
    {U : Type u} [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
    (σ : Representation (ZMod 2) D U)
    {κ : GroupClass.{u}} (hB5 : CompleteClassificationInput.{u,u} κ)
    (hB42 : CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.FullB42.{u,u} κ)
    (hB45 : RatioRecognition.SmallRatioSource.FullB45.{u,u} κ)
    (hD : IsSQTK κ D) (h₂ : pCore 2 D = ⊥)
    (K : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hquot : IsPGroup 2 (D ⧸ K)) {m : ℕ} (hm : 0 < m)
    (eK : K ≃* SuzukiMatrixGroup m)
    (I : Submodule (ZMod 2) U) (hI : IsIrrPlus σ K I)
    (hstable : (⊤ : Subgroup D) ≤ subspaceStabilizer σ I)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic σ A)
    (hbound : fixedCodim σ A ≤ 2 * rank A) :
    Nonempty (ActionEquiv (centralQuotientRepresentation σ K
      (subspaceCommutator σ ⊤ K)
      (subspaceCommutator_invariant_normalizer σ
        (le_subspaceStabilizer σ ⊤ (by simp)) K.le_normalizer)) (natural m)) := by
  have hsat := invariant_irrPlus_eq_moved σ hB5 hD h₂ K hquot hm eK I hI hstable A hA hbound
  have hC := centralizer_eq_bot_of_centerless_two_quotient K
    (SectionRecognition.center_eq_bot_of_equiv_suzuki eK) hquot h₂
  subst I
  exact SectionRecognition.invariant_natural_section σ K hm eK hD hquot
    _ hI hstable A hA hquad hbound (by rw [hC]; exact disjoint_bot_right) hB42 hB45

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.OrbitSections

end
