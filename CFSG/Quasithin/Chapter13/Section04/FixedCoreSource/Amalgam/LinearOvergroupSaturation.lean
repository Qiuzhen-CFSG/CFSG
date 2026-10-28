module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearNearMaximum
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearOvergroupAction
public import Theory.GroupTheory.ElementaryReplacementSaturation

/-!
# The first omega-module equality case and the remaining replacement

The exact source hypothesis K₂=[K₂,J₁(T)] forces some near-maximum elementary
subgroup E to move the original omega module. The non-FF comparison makes
W C_E(W) maximum in T and gives [K,E]=K. If E has the same kernel on the
larger omega module U, maximality and the three-subgroups lemma give U=W.
Otherwise that same maximum replacement acts nontrivially on U while its
commutator with K lies in C_G(U). This retains the concrete obstruction used
in the second case of the printed proof; that case still needs exclusion.

Source: Aschbacher–Smith 13.4.7(2), printed p.902. The residual commutator
hypothesis is retained, to be supplied for K₂=L₂ by source clause (4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
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

include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK

variable (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)

include hres

variable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
include h structural hout hindexL eK

/-- The equal-kernel branch of source 13.4.7(2) identifies the two actual
omega modules, using the selected near-maximum subgroup in the common Sylow. -/
theorem original_pair_linear_overgroup_eq_of_same_actor_kernel
    (E : Subgroup G) (hE : E ∈ ChapterB.thompsonFamily (T : Subgroup G) 1)
    (hneE : ¬ E ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G))
    (hker : E ⊓ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G) =
      E ⊓ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y : Set G)) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y =
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) := by
  let C := K.map (A ⊔ B).subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z (A ⊔ B)
  let U := conjugateSpanBy Z Y
  have hTY : (T : Subgroup G) ≤ Y := (hTA.trans le_sup_left).trans hY.2
  have hUY : U ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  obtain ⟨hr,_,_⟩ := original_pair_overgroup_component_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres Y hY
  let := hr.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUY).symm.toMonoidHom (subgroupOfEquivOfLe hUY).symm.injective
  let := hE.2.1
  have hUT : U ≤ (T : Subgroup G) := by
    intro u hu
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTY)
      (hr.le_pCore (show (⟨u,hUY hu⟩ : Y) ∈ U.subgroupOf Y from hu))
  obtain ⟨hCE,hmax⟩ := original_pair_linear_near_maximum_replacement h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK E hE hneE
  exact eq_of_maximum_replacement_of_full_actor (T : Subgroup G) W U E C
    (conjugateSpanBy_mono le_rfl hY.2) hUT hE.1
    ((hE.1.trans (hTA.trans le_sup_left)).trans (le_normalizer_conjugateSpanBy Z (A ⊔ B)))
    ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z (A ⊔ B)))
    (((map_subtype_le K).trans hY.2).trans (le_normalizer_conjugateSpanBy Z Y))
    hmax hker hCE
    (original_pair_linear_overgroup_whole_moved h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres h structural hout hindexL eK Y hY)

/-- The source residual commutator selects an actual near-maximum actor.
Either the omega modules coincide, or its maximum elementary replacement
acts nontrivially on the larger module while centralizing the component there. -/
theorem original_pair_linear_overgroup_replacement_dichotomy
    (hcomm : let K₂ := (pResidual 2 B).map B.subtype
      ⁅K₂,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = K₂)
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G)) :
    let C := K.map (A ⊔ B).subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let W := conjugateSpanBy Z (A ⊔ B)
    let U := conjugateSpanBy Z Y
    ∃ E ∈ ChapterB.thompsonFamily (T : Subgroup G) 1,
      ¬ E ≤ centralizer (W : Set G) ∧ ⁅C,E⁆ = C ∧
      let R := W ⊔ (E ⊓ centralizer (W : Set G))
      R ≤ (A ⊔ B : Subgroup G).pCoreIn 2 ∧
      R ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) ∧
      (U = W ∨ (¬ R ≤ centralizer (U : Set G) ∧ ⁅R,C⁆ ≤ centralizer (U : Set G))) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  let U := conjugateSpanBy Z Y
  let K₂ := (pResidual 2 B).map B.subtype
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hTY : (T : Subgroup G) ≤ Y := hTX.trans hY.2
  have hZY : Z ≤ Y := fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hUY : U ≤ Y := conjugateSpanBy_le hZY Y.le_normalizer
  have hWU : W ≤ U := conjugateSpanBy_mono le_rfl hY.2
  have hXW : X ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy Z X
  have hYC : Y ≤ normalizer (C : Set G) := original_pair_component_overgroup_normal
    h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB K hK Y hY
  have hJ : ¬ ChapterB.thompsonJ (T : Subgroup G) 1 ≤ centralizer (W : Set G) := by
    intro hh
    have hK₂X : K₂ ≤ X := (map_subtype_le _).trans le_sup_right
    have hc : K₂ ≤ centralizer (W : Set G) := by
      exact hcomm.symm.le.trans ((commutator_mono (le_refl K₂) hh).trans
        (le_normalizer_iff_commutator_le_right.mp
          ((hK₂X.trans hXW).trans (normalizer_le_normalizer_centralizer W))))
    have hZ : Z ≤ centralizer (K₂ : Set G) :=
      (le_conjugateSpanBy Z X).trans (le_centralizer_iff.mp hc)
    have he := omega_fixed_twoResidual B hTB
    have hfix : Z ⊓ centralizer (B : Set G) = Z :=
      he.symm.trans (inf_eq_left.mpr hZ)
    have hi : (Z ⊓ centralizer (B : Set G)).relIndex Z = 2 := hindexB
    rw [hfix,relIndex_self] at hi
    omega
  obtain ⟨E,hE,hneE⟩ : ∃ E ∈ ChapterB.thompsonFamily (T : Subgroup G) 1,
      ¬ E ≤ centralizer (W : Set G) := by
    by_contra! hh
    exact hJ (sSup_le fun E hE => hh E hE)
  obtain ⟨hCE,hmax⟩ := original_pair_linear_near_maximum_replacement h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK E hE hneE
  have hns : ¬ Group.IsSolvable X := by
    intro hh
    let := hh
    exact hK.not_isSolvable inferInstance
  have hfull := original_pair_full_action_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hres hns
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let := hred.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hWX).symm.toMonoidHom (subgroupOfEquivOfLe hWX).symm.injective
  have hRcore : W ⊔ (E ⊓ centralizer (W : Set G)) ≤ X.pCoreIn 2 := by
    rw [←hfull]
    exact sup_le (le_inf hWX (le_centralizer W))
      (le_inf ((inf_le_left.trans hE.1).trans hTX) inf_le_right)
  refine ⟨E,hE,hneE,hCE,hRcore,hmax,?_⟩
  by_cases hker : E ⊓ centralizer (W : Set G) = E ⊓ centralizer (U : Set G)
  · exact Or.inl (original_pair_linear_overgroup_eq_of_same_actor_kernel h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres h structural hout hindexL eK
      E hE hneE Y hY hker)
  · right
    let F := E ⊓ centralizer (W : Set G)
    have hFY : F ≤ Y := (inf_le_left.trans hE.1).trans hTY
    refine ⟨?_,?_⟩
    · intro hh
      apply hker
      exact le_antisymm (le_inf inf_le_left (le_sup_right.trans hh))
        (inf_le_inf_left E (centralizer_le hWU))
    · obtain ⟨hr,_,hCK⟩ := original_pair_overgroup_component_kernel h₀ D m h1332
        hTA hTB eA eB hne hindexA hindexB K hK hres Y hY
      let := hr.elementary
      let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
        (subgroupOfEquivOfLe hUY).symm.toMonoidHom (subgroupOfEquivOfLe hUY).symm.injective
      have hWC : W ≤ centralizer (U : Set G) := hWU.trans (le_centralizer U)
      have hCCW : C ≤ normalizer (centralizer (W : Set G) : Set G) :=
        ((map_subtype_le K).trans hXW).trans (normalizer_le_normalizer_centralizer W)
      have hFC : ⁅F,C⁆ ≤ C.pCoreIn 2 := by
        rw [←original_pair_component_action_kernel h₀ D m h1332
          hTA hTB eA eB hne hindexA hindexB hres K hK]
        exact le_inf (le_normalizer_iff_commutator_le_right.mp (hFY.trans hYC))
          ((commutator_mono inf_le_right le_rfl).trans
            (le_normalizer_iff_commutator_le_left.mp hCCW))
      apply commutator_sup_le_of_relative_normal Y W F C (centralizer (U : Set G))
        ((le_normalizer_conjugateSpanBy Z Y).trans (normalizer_le_normalizer_centralizer U))
        (hWU.trans hUY) hFY
      · exact ((commutator_mono hWC le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp
            ((((map_subtype_le K).trans hY.2).trans (le_normalizer_conjugateSpanBy Z Y)).trans
              (normalizer_le_normalizer_centralizer U))))
      · exact hFC.trans (hCK.symm.le.trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
