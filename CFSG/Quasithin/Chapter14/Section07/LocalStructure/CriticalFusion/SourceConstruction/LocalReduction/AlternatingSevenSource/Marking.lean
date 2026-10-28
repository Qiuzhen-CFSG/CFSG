module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Local
public import Theory.SpecificGroups.Alternating.SevenComponent.Extension

/-!
# The original A₇ component and its seven-letter quotient action

Source 14.7.48 identifies the actual C-component with the two-residual of
its original local I. Conjugation on C/O₂(C) therefore extends the given
A₇ marking to I, with kernel exactly O₂(I). Factoring this action through
the literal quotient gives a faithful seven-letter marking whose range
is A₇ or S₇. The component formula retains the supplied intrinsic marking.
No complement to either two-core is chosen.

Source: Aschbacher–Smith, 14.7.48–50, printed pp.1064–1065,
refs/quasithin.pdf. This constructs the group markings used in 14.7.50;
the rank-four and rank-six exclusion arguments remain separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem range_cases {X : Type*} [Group X]
    (f : X →* Equiv.Perm (Fin 7)) (h : alternatingGroup (Fin 7) ≤ f.range) :
    f.range = alternatingGroup (Fin 7) ∨ f.range = ⊤ := by
  have hd : f.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact Or.inr (index_eq_one.mp h1)
  · left
    apply le_antisymm _ h
    have hi := relIndex_mul_index h
    rw [alternatingGroup.index_eq_two,h2] at hi
    have he : (alternatingGroup (Fin 7)).relIndex f.range = 1 := by omega
    exact (relIndex_eq_one.mp he)

/-- The actual local quotient acts faithfully on seven letters, with its
component map equal to the supplied intrinsic A₇ marking. -/
theorem local_permutation_marking_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7)) :
    ∃ j : (I ⧸ pCore 2 I) →* Equiv.Perm (Fin 7),
      Function.Injective j ∧
      (∀ c : C, j (QuotientGroup.mk' (pCore 2 I) c.val) =
        (e (QuotientGroup.mk' (pCore 2 C) c)).val) ∧
      C.map (j.comp (QuotientGroup.mk' (pCore 2 I))) = alternatingGroup (Fin 7) ∧
      (j.range = alternatingGroup (Fin 7) ∨ j.range = ⊤) := by
  have hc := (local_component_eq_residual_at d h hab structural previous faithful earlier
    source47 I hI C hC).1
  let : C.Normal := hc ▸ inferInstance
  have hquot : IsPGroup 2 (I ⧸ C) := hc ▸ isPGroup_quotient_pResidual 2
  obtain ⟨f,hf⟩ := alternatingGroup.SevenComponent.exists_extension C e
  have hk := alternatingGroup.SevenComponent.extension_kernel_eq_twoCore C e hquot f hf
  let j := QuotientGroup.lift (pCore 2 I) f hk.ge
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply _root_.eq_bot_iff.mpr
    intro x hx
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 I) x
    exact (QuotientGroup.eq_one_iff x).mpr (hk ▸ hx)
  have hm : C.map (j.comp (QuotientGroup.mk' (pCore 2 I))) = alternatingGroup (Fin 7) := by
    ext x
    constructor
    · rintro ⟨c,hc,rfl⟩
      change f c ∈ alternatingGroup (Fin 7)
      rw [hf ⟨c,hc⟩]
      exact (e (QuotientGroup.mk' (pCore 2 C) ⟨c,hc⟩)).property
    · intro hx
      obtain ⟨z,hz⟩ := e.surjective ⟨x,hx⟩
      obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C) z
      exact ⟨c.val,c.property,(hf c).trans (congrArg Subtype.val hz)⟩
  refine ⟨j,hj,hf,hm,range_cases j ?_⟩
  rw [←hm]
  rintro x ⟨c,hc,rfl⟩
  exact ⟨QuotientGroup.mk' (pCore 2 I) c,rfl⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
