module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearSourceConclusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ThompsonBaumann
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ThompsonResidual

/-!
# The source residual reductions on the actual linear pair

The proved linear module structure makes J(T) normal in the original join.
Its full Sylow action kernel then identifies Baum(T) with Baum(O₂(X)),
excludes characteristic subgroups of Baum(T) normal in LT, and forces
J(T) to move the original LT two-core quotient. Thus alternative
13.2.2(10I) is eliminated using the original groups.

Once 13.2.2(10III) supplies nontrivial residual movement through its actual
map on B, the index-three argument lifts it to O²(B)=[O²(B),J₁(T)]. This
feeds the complete linear overgroup conclusion, without a hypothesis that
the entire map kernel is a two-group, and also excludes J₁-normality.
The block alternative (10II), derivation of the earlier trichotomy, model
selection, and the literal K₂=L₂ applicability remain source obligations.
These results do not construct PlaneAmalgamSource1347.
Source: Aschbacher–Smith 13.2.2(10), p.878; 13.4.7(2),(4), pp.902–903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource NoncentralChiefRefinement
open Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
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

/-- The original linear join excludes the characteristic-normal source
alternative and forces noncentral Thompson action in the original LT. -/
theorem original_pair_linear_baumann_obstructions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    ChapterB.baumann (T : Subgroup G) = ChapterB.baumann ((A ⊔ B).pCoreIn 2) ∧
      A ⊔ B ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      (∀ C : Subgroup (ChapterB.baumann (T : Subgroup G)), C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf
          (L ⊔ (T : Subgroup G))).Normal) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hn := original_pair_linear_thompson_normal h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  obtain ⟨hb,hbN⟩ := original_pair_baumann_of_thompson_normal h₀ D m
    hTA hTB eA eB hne hindexA hindexB hn
  refine ⟨hb,hbN,?_,thompson_not_le_original_core_of_outside_normalizer h D hout hn⟩
  intro C hC hCne
  let := hC
  exact no_characteristic_baumann_normal_of_outside_join h D hout hbN C hCne

/-- The actual residual image premise supplies the full original linear
conclusion and rules out J₁-normality in the same join. -/
theorem original_pair_linear_conclusion_of_residual_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    {F : Type*} [Group F] (f : B →* F) (hf : (pResidual 2 B).map f ≠ ⊥)
    (hmove : ⁅(pResidual 2 B).map f,
      ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf B).map f⁆ =
        (pResidual 2 B).map f) :
    Solvable.LinearAmalgamConclusion T (A ⊔ B) ∧
      ¬ A ⊔ B ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  have hc := original_residual_thompson_one_of_image hTB eB f hf hmove
  exact ⟨original_pair_linear_amalgam_conclusion h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL hc,
    not_thompson_one_normalizer_of_residual_movement hTB eB le_sup_right hc⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
