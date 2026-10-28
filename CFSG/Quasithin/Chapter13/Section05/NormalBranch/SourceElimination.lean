module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.NormInput
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.OriginalTransfer
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.ResidualEndpoint
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Normalizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental

/-!
# Elimination of the original normal A₆ counterexample branch

The original 13.5.15 theorem supplies all nine local conclusions. Its
recognized U₄(3) alternative is excluded by the counterexample datum.
In the remaining S₆ extension, transfer fuses every involution with the
original point. The cubic norm construction gives an involution a and a
two-subgroup X of O²(C_G(a)) with Φ(X)=V₂. Fusion carries X into U_H,
whose Frattini subgroup has order at most two, contradicting |V₂|=4.

Every quotient, action and local subgroup comes from the original source
datum. No completed local conclusion, weak closure, fusion statement,
transfer witness or ambient model classification is an extra hypothesis.
The second theorem is the ordinary-A₆ nonnormality input to 13.5.18.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition 13.5.16 and Lemma 13.5.18, printed pp.921–922.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceElimination
open Section08.SourceCompletion ExtensionSixSource
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆)
include d h e hseed

/-- The actual original normal-A₆ branch cannot occur in the supplied
counterexample. Both alternatives of 13.5.15 are discharged internally. -/
theorem original_normal_a6_false (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) : False := by
  obtain ⟨_,_,b⟩ := SourceConclusions.source13_5_15 d h e hseed hn hU
  have hS := original_extension_model d h e hseed hn hU
  have hpoint : D.V₁ ≠ ⊥ := by
    intro hb
    have hc := h.point_card
    simp [hb] at hc
  obtain ⟨z,hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hpoint
  have hz1' : (z : G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  obtain ⟨a,X,ha,hX,hXR,hphi⟩ :=
    exists_terminal_frattini_witness d h e hseed hn hU b hS z z.property hz1'
  have hza := original_ambient_involutions_fused d h e hseed hn hU
    z z.property hz1' a ha
  exact original_fused_residual_frattini_obstruction d h e hseed hn hU
    z.property hz1' hza.symm X hX hXR hphi

/-- The ordinary-A₆ case of the source nonnormality reduction 13.5.18. -/
theorem original_normal_a6_not_normal (hU : ¬IsMulCommutative D.UH) :
    ¬(D.L₁.subgroupOf D.H).Normal := by
  intro hn
  exact original_normal_a6_false d h e hseed hn hU

omit h in
/-- The literal family nonnormality premise of
`ComponentReduction.local_normalizer_core`. The F.9 setup for each member
is the same earlier-source input already required by that consumer. -/
theorem original_normal_a6_family_not_normal
    (hF : ∀ J ∈ Section08.Source.Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ({D with H := J} : ChapterF.Section09.Setup G).Hypothesis) :
    ∀ J ∈ Section08.Source.Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ¬IsMulCommutative (Section08.Source.UH J D.Vplus) →
        ¬(D.L₁.subgroupOf J).Normal := by
  intro J hJ hU
  exact original_normal_a6_not_normal (D := {D with H := J}) d (hF J hJ) e hseed hU

omit h e hseed in
/-- The chosen source module belongs to the literal two-core of N_G(L). -/
theorem original_module_le_maximal_core : D.V ≤ M.pCoreIn 2 := by
  rw [d.local_normalizer]
  exact d.chosen.le_componentCore.trans
    (pCoreIn_mono_of_normalizes D.L.le_normalizer le_rfl)

/-- Original ordinary-A₆ application of 13.5.19: the former universal
13.5.16 recognition premise is supplied by the source contradiction. -/
theorem original_normal_a6_normalizer_conclusions
    (hF : ∀ J ∈ Section08.Source.Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ({D with H := J} : ChapterF.Section09.Setup G).Hypothesis)
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hcentral : ⁅D.V,M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁) :
    Section08.Source.starImage D.H (D.H ⊓ normalizer (D.L₁ : Set G)) =
      normalizer (Section08.Source.starImage D.H D.L₁ : Set (Section08.Source.Hstar D.H)) ∧
    D.V ≤ (D.H ⊓ normalizer (D.L₁ : Set G)).pCoreIn 2 := by
  exact ⟨ComponentReduction.local_normalizer_image D h,
    ComponentReduction.local_normalizer_core D h M
      (original_module_le_maximal_core d) hbound hcentral hF
      (original_normal_a6_family_not_normal d e hseed hF)⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceElimination
