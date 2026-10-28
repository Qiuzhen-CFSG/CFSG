module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.OvergroupKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearFixedFree
public import Theory.GroupTheory.Commutator.ConjugateSpan

/-!
# Component movement on the omega module of a local overgroup

The component has no fixed vectors on the original omega-center. The
larger span remains elementary and lies in the common Sylow subgroup;
Sylow fixed-point detection therefore excludes component-fixed vectors
on that larger span as well.

In the linear case, the original span equals its commutator with the
component. The component is normal in every local overgroup, so this
commutator generation persists on the larger conjugate span. These are
facts about the actual overgroup and original component, without a new
module marking. Equality of the larger span with the original six-space
and the overgroup supplement remain to be proved.

Source: Aschbacher–Smith 13.4.7(2), printed p.902. The earlier universal
Structural1222 and Source1332OneTwo inputs remain explicit for assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
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

/-- No nonzero vector of the larger omega module is fixed by the original
component. This still does not identify the two omega modules. -/
theorem original_pair_overgroup_component_fixed_free
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G)) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y ⊓
      centralizer (K.map (A ⊔ B).subtype : Set G) = ⊥ := by
  let C := K.map (A ⊔ B).subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z Y
  have hTY : (T : Subgroup G) ≤ Y := (hTA.trans le_sup_left).trans hY.2
  have hUY : U ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  obtain ⟨hr,_,_⟩ := original_pair_overgroup_component_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres Y hY
  let := hr.elementary
  have he : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUY).symm.toMonoidHom (subgroupOfEquivOfLe hUY).symm.injective
  have hUT : U ≤ (T : Subgroup G) := by
    intro u hu
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTY)
      (hr.le_pCore (show (⟨u,hUY hu⟩ : Y) ∈ U.subgroupOf Y from hu))
  have hTC := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2.2.2.1
  have hfree := original_pair_component_fixed_free h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK
  have hZ : Z ⊓ centralizer (C : Set G) = ⊥ := le_bot_iff.mp
    ((inf_le_inf_right _ (le_conjugateSpanBy Z (A ⊔ B))).trans_eq hfree)
  exact inf_centralizer_eq_bot_of_omega_disjoint T C U he hUT
    (hTY.trans (le_normalizer_conjugateSpanBy Z Y)) hTC hZ

/-- The original linear component fully moves the omega module of every
local overgroup, since it moves the original module containing the seed. -/
theorem original_pair_linear_overgroup_whole_moved
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G)) :
    let C := K.map (A ⊔ B).subtype
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y
    ⁅U,C⁆ = U := by
  let C := K.map (A ⊔ B).subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U₀ := conjugateSpanBy Z (A ⊔ B)
  let U := conjugateSpanBy Z Y
  have hCY : C ≤ Y := (map_subtype_le K).trans hY.2
  have hYC := original_pair_component_overgroup_normal h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK Y hY
  have hmove := original_pair_linear_whole_moved h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  have hclose : conjugateSpanBy U₀ Y = U := by
    apply le_antisymm
    · exact conjugateSpanBy_le (conjugateSpanBy_mono le_rfl hY.2)
        (le_normalizer_conjugateSpanBy Z Y)
    · exact conjugateSpanBy_mono (le_conjugateSpanBy Z (A ⊔ B)) le_rfl
  have hm := conjugateSpanBy_eq_commutator_of_seed U₀ Y C C hCY hYC le_rfl hmove.symm
  rw [hclose] at hm
  exact hm.symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
