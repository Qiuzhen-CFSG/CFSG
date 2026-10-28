module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearShortThompson

/-!
# Residual movement for the original linear short branch

Use the literal source plane normalizer N_LT(V₂), where V₂ is the preimage
of the actual T-invariant natural-quotient plane. The augmentation action
constructs the simultaneous Sylow and radical marking. If J₁(T) stayed in
this radical, its small maximum images would give A(O₂(LT)) ⊆ A(T).
The independent inner-plane alignment then supplies the cubic chief budget,
and the proved short-block contradiction forces the full two-residual to
be moved by J₁(T). The literal identity K₂=L₂ is derived from the plane
normalizer rather than supplied as a marking premise.

This supplies the full linear overgroup conclusion from the selected linear
component and shortness. The pushing-up alternative producing shortness,
model selection and the general source 13.4.7 interfaces remain obligations.
Source: Aschbacher–Smith 13.2.2(10), p.878, and 13.4.7(4), pp.902–903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- Failure of J₁ movement in the original plane gives the source maximum
family inclusion, with the action and both image markings constructed. -/
theorem original_plane_maximum_family_of_thompson_one_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2) :
    elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G) := by
  obtain ⟨q,hk,hker,hY,hT,hQ⟩ :=
    exists_original_plane_action_marking h structural D m eL W hW hTW
  rw [←hB] at hQ
  exact original_core_maximum_family_of_thompson_one_bound
    h structural D m q hk hker hY hT hQ hJ

variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

/-- The original linear short-branch conclusion with all action, Sylow,
second-parabolic marking and maximum-family premises discharged. -/
theorem original_pair_linear_short_conclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hb : ChapterC.IsShort L)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) :
    ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
        (pResidual 2 B).map B.subtype ∧
      Solvable.LinearAmalgamConclusion T (A ⊔ B) ∧
      ¬ A ⊔ B ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  have hc : ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
      (pResidual 2 B).map B.subtype := by
    apply (original_residual_thompson_one_iff hTB eB).mpr
    intro hn
    obtain ⟨eL⟩ := Solvable.ordinary_of_short_core_marking D m hb
    have hf := original_plane_maximum_family_of_thompson_one_bound
      h structural D m eL W hW hTW hB hn
    let J := L ⊓ normalizer (m.naturalPreimage W : Set G)
    have hTJ := m.sylow_normalizes_inner_plane W hTW
    obtain ⟨g,hg⟩ := m.natural_plane_alignment W hW hTW
    have hi := m.aligned_inner_plane_image W g hg
    have hBJ : B = J ⊔ (T : Subgroup G) :=
      hB.trans (Solvable.second_flag_normalizer_eq D _ hTW)
    have hK₂ : (pResidual 2 B).map B.subtype = (pResidual 2 J).map J.subtype := by
      rw [hBJ]
      exact Solvable.second_parabolic_full_residual J hTJ
    exact original_pair_linear_short_block_impossible h₀ D (m.relabel g) h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
      hb hf J inf_le_left hTJ hi hK₂
  exact ⟨hc,original_pair_linear_amalgam_conclusion h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL hc,
    not_thompson_one_normalizer_of_residual_movement hTB eB le_sup_right hc⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
