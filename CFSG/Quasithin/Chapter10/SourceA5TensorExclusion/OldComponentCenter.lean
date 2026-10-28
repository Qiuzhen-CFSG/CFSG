module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaCenterFree

/-!
# The original old residual centralizes the Sylow omega-center

Tensor non-FF forces J(T) to centralize the local module. The original
3.1.8 movement implication then puts Ω₁Z(T) in the center of each original
H-star member. In particular its literal two-residual centralizes Ω₁Z(T).
This is the fixed seed used in source 9.2.7 and the first reduction of 9.3.1.
Source: Aschbacher–Smith, printed pp.730–732, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}

theorem hstar_centralizes_sylowOmega (m : SourceA5TensorModel D e)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  have h127 := source_module_nonsolvable_uniqueness D
  have hq := D.qrcHypotheses h127 hH
  have hmax := (D.lemma_3_2_3_uniqueness h127).1
  have hu := (D.lemma_3_2_3_uniqueness h127).2.2
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G) := by
    rw [m.module_eq]
    exact m.thompson_centralizes_fullModule
  have hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      (center H).map H.subtype := by
    by_contra hn
    exact hq.thompson_moves_of_noncentral_omega D.simpleQTKE hmax hu D.module_ne_bot hn hJ
  intro h hh z hz
  obtain ⟨zH,hzH,rfl⟩ := hZ hz
  exact (congrArg Subtype.val (mem_center_iff.mp hzH ⟨h,hh⟩)).symm

theorem old_residual_centralizes_sylowOmega (m : SourceA5TensorModel D e)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    (pResidual 2 H).map H.subtype ≤
      centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
  (map_subtype_le _).trans (m.hstar_centralizes_sylowOmega hH)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
