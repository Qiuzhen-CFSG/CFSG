module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderExtraction
public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import CFSG.Quasithin.ChapterD.Section03.SourceFitting
public import Theory.GroupTheory.Fitting.PrimeSubgroups
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Cubic descent to a faithful original seed

A seed on which the normal generalized Fitting subgroup acts faithfully
has no elementary pointwise kernel when the ambient two-core is trivial.
A minimum cubic actor therefore either restricts faithfully to the seed,
or its independent orbit supplies an FF offender on that same seed.
The cubic bound descends in both cases. The orbit lemmas retain the literal
seed when passing from a normal supplement to the faithful orbit action.

The original nonseparated Chapter 10 seed is the consumer in
`CentralHall.Nonlinear.Modules.SeedAnalysis.SeedCubic`.
Source: Aschbacher--Smith D.3.5--7, using D.2.5 and D.2.9,
printed pp.179--182 and195--199.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD
open Chapter3.Section02.ChosenSource325
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem subspaceKernel_eq_bot_of_faithful_fitting
    (K : Subgroup G) [K.Normal] (hF : generalizedFitting G = K)
    (hcore : pCore 2 G = ⊥)
    (I : Submodule (ZMod 2) V) (hKI : K ≤ subspaceStabilizer ρ I)
    (hk : subspaceKernel ρ I K = ⊥) (A : Subgroup G) (hA : IsPGroup 2 A) :
    subspaceKernel ρ I A = ⊥ := by
  have hKC : subspaceKernel ρ I A ≤ centralizer (K : Set G) := by
    intro a ha k hK
    have haf : ∀ v ∈ I, ρ a⁻¹ v = v :=
      ((subspaceKernel ρ I A).inv_mem ha).2
    have hka : k⁻¹ * (a*k*a⁻¹) ∈ subspaceKernel ρ I K := by
      refine ⟨K.mul_mem (K.inv_mem hK) ((inferInstance : K.Normal).conj_mem k hK a),?_⟩
      intro v hv
      simp only [map_mul,Module.End.mul_apply,haf v hv,ha.2 _ ((hKI hK v).2 hv)]
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    have he := inv_mul_eq_one.mp (mem_bot.mp (hk.le hka))
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  let C := centralizer (K : Set G)
  have hCK : C ≤ K := by simpa only [hF] using centralizer_generalizedFitting_le G
  let : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp
    (show C ≤ centralizer (C : Set G) from centralizer_le hCK)
  let : CommGroup C := IsMulCommutative.instCommGroup
  have hCF : C ≤ fittingSubgroup G := le_sSup ⟨inferInstance,inferInstance⟩
  have hp : IsPGroup 2 (subspaceKernel ρ I A) :=
    hA.of_injective (inclusion (subspaceKernel_le ρ I A)) (inclusion_injective _)
  exact bot_unique ((hp.le_pCore_of_le_fitting (hKC.trans hCF)).trans hcore.le)

/-- The literal stabilizer image on a faithful constituent inherits the cubic bound. -/
theorem seed_cubic_bound_of_independent_orbit
    [FiniteDimensional (ZMod 2) V]
    (I : Submodule (ZMod 2) V)
    (hind : sSupIndep (subspaceOrbit ρ ⊤ I))
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hk : ∀ A : Subgroup G, IsPGroup 2 A → subspaceKernel ρ I A = ⊥)
    (hb : cubicRatio ρ ≤ 2) : cubicRatio (subspaceImageRepresentation ρ I) ≤ 2 := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hb
  have hel := hA.1.2.1
  have hc := hA.1.2.2.1
  let : IsElementaryAbelian 2 A := hel.2
  have hker := hk A (IsElementaryAbelian.isPGroup 2 A)
  have hsmall := hA.1.2.2.2.le.trans hb
  by_cases hs : A ≤ subspaceStabilizer ρ I
  · have hn : ¬ I ≤ fixedSpace ρ A := by
      intro hf
      apply hel.1
      apply bot_unique
      intro a ha
      exact hker.le ⟨ha,fun v hv => hf hv ⟨a,ha⟩⟩
    have hr := RPlusBound.restricted ρ
      (show A ∈ RPlusBound ρ 2 from ⟨⟨hel,hsmall⟩,QhatStar.mem_RPlus ρ hA⟩) I hs hn
    have hl : cubicRatio (subspaceImageRepresentation ρ I) ≤
        actionRatio (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) :=
      iInf_le_of_le _ (iInf_le_of_le ⟨hr.1,isCubic_restrictedSubgroup ρ I hc⟩ le_rfl)
    exact hl.trans hr.2
  · obtain ⟨a,ha,hn⟩ := Set.not_subset.mp hs
    have hi : sSupIndep (subspaceOrbit ρ A I) := hind.mono (by
      rintro _ ⟨b,rfl⟩
      exact ⟨⟨b,mem_top _⟩,rfl⟩)
    have hff := isFFModule_of_cubic_moved_summand ρ I A hel hc hi hdim
      ((actionRatio_le_nat_iff ρ hel 2).mp hsmall) hker ha
      (fun he => hn ((subspace_map_eq_iff ρ I a).mp he))
    exact (cubicRatio_le_quadraticRatio _).trans
      (((isFFModule_iff_quadraticRatio_le_one _).mp hff).trans (by norm_num))
end CFSG.Quasithin.ChapterD

namespace Representation.BinaryOffender
open Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem subspaceOrbit_eq_of_normal_supplement
    (K S : Subgroup G) [K.Normal] (hgen : S ⊔ K = ⊤)
    (I : Submodule (ZMod 2) V) (hKI : K ≤ subspaceStabilizer ρ I) :
    subspaceOrbit ρ ⊤ I = subspaceOrbit ρ S I := by
  ext J
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨s,hs,k,hk,he⟩ := mem_sup_of_normal_right.mp (show (g : G) ∈ S ⊔ K by rw [hgen]; exact mem_top _)
    refine ⟨⟨s,hs⟩,?_⟩
    change I.map (ρ s) = I.map (ρ (g : G))
    rw [←he,subspace_map_mul,(subspace_map_eq_iff ρ I k).mpr (hKI hk)]
  · rintro ⟨s,rfl⟩
    exact ⟨⟨s,mem_top _⟩,rfl⟩

theorem independent_orbit_faithful_restriction
    (W I : Submodule (ZMod 2) V)
    (hW : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W) (hIW : I ≤ W)
    (hind : sSupIndep (subspaceOrbit ρ ⊤ I)) :
    sSupIndep (subspaceOrbit (subspaceImageRepresentation ρ W) ⊤ (I.comap W.subtype)) := by
  classical
  let σ := subspaceImageRepresentation ρ W
  let J := I.comap W.subtype
  have hmap (a : subspaceActionImage ρ W) :
      (J.map (σ a)).map W.subtype ∈ subspaceOrbit ρ ⊤ I := by
    obtain ⟨g,rfl⟩ := invariantActionHom_surjective ρ W hW a
    refine ⟨⟨g,mem_top _⟩,?_⟩
    ext v
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨σ (invariantActionHom ρ W hW g) ⟨x,hIW hx⟩,
        ⟨⟨x,hIW hx⟩,hx,rfl⟩,rfl⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x,hx,rfl⟩
  let F : subspaceOrbit σ ⊤ J → subspaceOrbit ρ ⊤ I := fun U =>
    ⟨U.val.map W.subtype,by obtain ⟨a,ha⟩ := U.property; rw [←ha]; exact hmap a⟩
  have hF : Function.Injective F := by
    intro U U' he
    exact Subtype.ext (Submodule.map_injective_of_injective W.subtype_injective
      (congrArg Subtype.val he))
  have hi := ((sSupIndep_iff _).mp hind).comp hF
  apply (sSupIndep_iff _).mpr
  intro U
  apply Submodule.disjoint_def.mpr
  intro v hv hs
  have hzero : (v : V) = 0 := by
    apply Submodule.disjoint_def.mp (hi U) v
    · exact ⟨v,hv,rfl⟩
    · have hm : (v : V) ∈ (⨆ U' : subspaceOrbit σ ⊤ J, ⨆ (_ : U' ≠ U), U'.val).map W.subtype :=
        ⟨v,hs,rfl⟩
      simpa only [Submodule.map_iSup,F,Function.comp_apply] using hm
  exact Subtype.ext hzero
end Representation.BinaryOffender
