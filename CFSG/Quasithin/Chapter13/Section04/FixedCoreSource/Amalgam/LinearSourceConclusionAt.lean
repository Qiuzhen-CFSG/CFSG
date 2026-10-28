module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearSourceConclusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearOvergroupFormulaAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearThompsonAt

/-!
# The complete guarded linear amalgam consumer

Actual component family memberships, J(T) normality and the full
overgroup product give the exact LinearAmalgamConclusion.
PlaneNonsolvableSourceAt supplies the component model and residual
movement from the actual nonsolvable original plane pair.
Source: Aschbacher--Smith 13.4.7(1ii),(2),(4), pp.899--903.
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

/-- The actual linear component supplies the complete consumer conclusion
once the source clause-(4) residual identity is available. -/
theorem original_pair_linear_amalgam_conclusion_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcomm : let K₂ := (pResidual 2 B).map B.subtype
      ⁅K₂,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = K₂) :
    Solvable.LinearAmalgamConclusion T (A ⊔ B) := by
  obtain ⟨_,hf,hstar,hTC,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  refine ⟨⟨K.map (A ⊔ B).subtype,?_,hf,hstar,hTC,?_,⟨eK⟩⟩,?_,?_⟩
  · exact ⟨map_subtype_le K, by
      simpa only [subgroupOf,comap_map_eq_self_of_injective (A ⊔ B).subtype_injective] using hK⟩
  · exact (original_pair_component_is_residual h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).2
  · exact original_pair_linear_thompson_normal_at h₀ h structural D m
      hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  · intro Y hY
    exact (original_pair_linear_overgroup_formula_at h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK
      h structural hout hindexL hcomm Y hY).2

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
