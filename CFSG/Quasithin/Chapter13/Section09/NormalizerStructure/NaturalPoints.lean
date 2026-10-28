module
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.Action
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.FiveBasis

/-!
The five literal orbit points have exactly the full-product binary relation, with original t the product of the first two and original z the last point. The actual conjugation action induces every permutation of these points. This is the natural S5-module certificate consumed by the centralizer splitting in Aschbacher–Smith 13.9.10, printed p.973.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

theorem normalizerOrbitAction_surjective {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    Function.Surjective m.normalizerOrbitAction := by
  intro σ
  obtain ⟨g,hg⟩:=m.normalizerS5Action_surjective hG
    ((m.normalizerFiveCoordinates hG).permCongrHom σ)
  exact ⟨g,(m.normalizerFiveCoordinates hG).permCongrHom.injective hg⟩

theorem exists_natural_five_points {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃e:Fin 5≃m.normalizerOrbit,
      m.t=((e 0).val:G)*((e 1).val:G) ∧ ((e 4).val:G)=m.z ∧
      ∀a:Fin 5→Fin 2,
        ((e 0).val^(a 0).val*(e 1).val^(a 1).val*(e 2).val^(a 2).val*
          (e 3).val^(a 3).val*(e 4).val^(a 4).val=1 ↔ a=0 ∨ a=1) := by
  obtain ⟨b,hb⟩:=m.normalizerOrbit_generating_class hG
  have hm (i:Fin 5):m.BParametersEquiv (fiveParameters b i)∈m.normalizerOrbit := by
    rw [m.mem_normalizerOrbit_iff_isConj]
    change IsConj m.z (m.embedding (parametersToW (fiveParameters b i)))
    by_cases hi:i=4
    · subst i
      rw [fiveParameters_four_z]
      exact IsConj.refl _
    · have hc:=m.embedding.map_isConj
        ((parameters_class_iff (if b then 4 else 2) (fiveParameters b i)).mpr
          ⟨fiveParameters_ne_one b i,by rw [fiveParameters_index,if_neg hi]⟩)
      have hf:IsConj m.z (m.embedding (representative (if b then 4 else 2))) := by
        simpa only [fusionFlags,decide_eq_true_eq] using hb
      exact hf.trans hc
  let f:Fin 5→m.normalizerOrbit:=fun i=>⟨m.BParametersEquiv (fiveParameters b i),hm i⟩
  have hf:Function.Injective f := by
    intro i j he
    exact fiveParameters_injective b (m.BParametersEquiv.injective (congrArg Subtype.val he))
  have hbij:Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf,by rw [Nat.card_fin,Nat.card_coe_set_eq,m.normalizerOrbit_card_five hG]⟩
  let e:=Equiv.ofBijective f hbij
  refine ⟨e,?_,?_,?_⟩
  · change m.t=m.embedding (parametersToW (fiveParameters b 0))*
      m.embedding (parametersToW (fiveParameters b 1))
    rw [←map_mul,fiveParameters_pair_t]
    rfl
  · change m.embedding (parametersToW (fiveParameters b 4))=m.z
    rw [fiveParameters_four_z]
    rfl
  · intro a
    change (m.BParametersEquiv (fiveParameters b 0)^(a 0).val*
      m.BParametersEquiv (fiveParameters b 1)^(a 1).val*
      m.BParametersEquiv (fiveParameters b 2)^(a 2).val*
      m.BParametersEquiv (fiveParameters b 3)^(a 3).val*
      m.BParametersEquiv (fiveParameters b 4)^(a 4).val=1 ↔ _)
    rw [←map_pow,←map_pow,←map_pow,←map_pow,←map_pow,←map_mul,←map_mul,←map_mul,←map_mul,
      m.BParametersEquiv.map_eq_one_iff]
    exact fiveWord_relation b a

end CFSG.Quasithin.Chapter13.Section09.Marking
