module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ComponentFixedFree
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingParabolicPair
public import Theory.Representation.ConjugateSpanFixedFree

/-!
# Full component movement on the original fixed-line orbits

Restrict the common Sylow to the actual component. It fixes every seed in
Ω₁Z(T), and each seed orbit is elementary inside the reduced omega module.
The proved absence of component-fixed vectors passes to each orbit, so
Sylow averaging gives its full commutator equality. Removing the original
Sylow supplement gives the same equality on the entire omega module.

This works for every selected component, including the ordinary A₆ row;
no linear-module equivalence or extra movement premise is assumed. The
actual preceding source inputs, fixed indices, escape and prime-to-three
residual clause are retained. Model selection and Thompson normality in
the remaining rows are still required for the universal amalgam outputs.
Source: Aschbacher--Smith 13.4.7, printed pp.900--901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- Every original omega-center seed orbit is fully moved by the same component. -/
theorem original_pair_component_seed_moved
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)

    (F : Subgroup G) (hF : F ≤ omegaOneCenterAmbient (T : Subgroup G)) :
    let C := K.map (A ⊔ B).subtype
    ⁅conjugateSpanBy F C,C⁆ = conjugateSpanBy F C := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  let E := conjugateSpanBy F C
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hr := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : IsElementaryAbelian 2 (U.subgroupOf X) := hr.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUX).symm.toMonoidHom (subgroupOfEquivOfLe hUX).symm.injective
  have hEU : E ≤ U := conjugateSpanBy_mono hF (map_subtype_le K)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (inclusion hEU) (inclusion_injective hEU)
  have hfree := original_pair_component_fixed_free h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK
  obtain ⟨S,hS,_,_,_⟩ := original_pair_component_parabolic_restriction
    h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB K hK
  apply Representation.conjugateSpan_commutator_eq_of_fixed_free F C S
  · intro f hf s hs
    obtain ⟨c,hc,rfl⟩ := hs
    have hcT : c.val ∈ (T : Subgroup G) := by
      rw [hS] at hc
      exact hc
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hF hf)).2.2 c.val hcT
  · exact le_bot_iff.mp ((inf_le_inf_right _ hEU).trans hfree.le)


/-- The entire original omega module is its commutator with the actual component. -/
theorem original_pair_component_whole_moved
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
 :
    let C := K.map (A ⊔ B).subtype
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
    ⁅U,C⁆ = U := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hn := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2.2.2.1
  have hg := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) :=
    le_trans (le_centralizer_iff.mp (fun _ hz =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)) (Subgroup.centralizer_le_normalizer _)
  have he : conjugateSpanBy Z X = conjugateSpanBy Z C := by
    change X = C ⊔ (T : Subgroup G) at hg
    rw [hg]
    exact conjugateSpanBy_sup_of_normalizes_seed Z C (T : Subgroup G) hTZ hn
  change ⁅conjugateSpanBy Z X,C⁆ = conjugateSpanBy Z X
  rw [he]
  exact original_pair_component_seed_moved h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK Z le_rfl

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
