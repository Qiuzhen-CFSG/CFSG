module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLine
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponentCenter
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.Representation.BinaryConjugationSection.NormalizerAction
public import Theory.Representation.OrthogonalFourPlusMatrix.Commutant

/-!
# The original tensor Hall kernel fixes the full module

An element centralizing the component section commutes with its determinant
action on V. The additive commutant is the coefficient field. The original
H-star subgroup fixes the Sylow omega-center, so its scalar fixes a nonzero
vector and equals one. This proves the module-centralization premise used by
the original odd-normalizer argument without a separated seed assumption.

Source: Aschbacher--Smith 4.4.14 and 9.2.5, printed pp.625 and 730--731.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Chapter4 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

include m

/-- The actual H-star section kernel centralizes the original tensor module. -/
theorem hstar_sectionKernel_centralizes_fullModule {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ⊓ sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G) := by
  let M := D.maximalLocal
  let R := localOrbit T L
  let V := D.fullModule
  let α := BinaryConjugationSection.normalizerAction m.sectionData.coordinates
    ⟨m.coordinates_injective,m.sectionData.onto⟩
  let f : M →* (Binary.V ≃ₗ[ZMod 2] Binary.V) :=
    α.comp (inclusion D.maximalLocal_normalizes_fullModule)
  have hformula (x : M) (v : V) : f x (m.sectionData.coordinates v).toAdd =
      (m.sectionData.coordinates (V.normalizerMonoidHom
        ⟨x,D.maximalLocal_normalizes_fullModule x.property⟩ v)).toAdd :=
    BinaryConjugationSection.normalizerAction_coordinates _ _ _ _
  have hfker (x : M) (hx : (x : G) ∈ centralizer (V : Set G)) : f x = 1 := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,hv⟩ := m.sectionData.onto (Multiplicative.ofAdd w)
    have hv' : (m.sectionData.coordinates v).toAdd = w := congrArg Multiplicative.toAdd hv
    rw [← hv']
    rw [hformula]
    change (m.sectionData.coordinates (V.normalizerMonoidHom
      ⟨x,D.maximalLocal_normalizes_fullModule x.property⟩ v)).toAdd =
        (m.sectionData.coordinates v).toAdd
    apply congrArg (fun y => (m.sectionData.coordinates y).toAdd)
    apply Subtype.ext
    change (x : G) * (v : G) * (x : G)⁻¹ = v
    rw [←hx v v.property,mul_inv_cancel_right]
  have hR (r : R) : (f ⟨r,R.le_normalizer r.property⟩).toLinearMap =
      Binary.action (m.quotient r) :=
    BinaryConjugationSection.normalizerAction_restrict m.sectionData m.coordinates_injective r
  have hCM : sectionCentralizer R ≤ M :=
    ((le_sectionCentralizer_iff (sectionCentralizer R) R).mp le_rfl).1
  let C := (sectionCentralizer R).subgroupOf M
  let R₀ := R.subgroupOf M
  have hcomm : ⁅C,R₀⁆ ≤ pCore 2 M := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hCM,
      map_subgroupOf_eq_of_le R.le_normalizer]
    exact (((le_sectionCentralizer_iff (sectionCentralizer R) R).mp le_rfl).2).trans
      (pCoreIn_mono_of_normalizes R.le_normalizer le_rfl)
  have hcore : pCore 2 M ≤ f.ker := by
    intro x hx
    apply hfker x
    have hc := le_centralizer_iff.mp ((source_full_module_reduced D).le_reducedPSubgroup.trans
      (reducedPSubgroup_le_centralizer_pCore 2 M)) hx
    intro v hv
    exact congrArg Subtype.val (hc ⟨v,(D.fullModule_le_orbit.trans R.le_normalizer) hv⟩ hv)
  have hcomm' : ⁅C.map f,R₀.map f⁆ = ⊥ := by
    rw [←map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (hcomm.trans hcore)
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hcomm'
  intro b hb
  let bM : M := ⟨b,hCM hb.2⟩
  have hbC : f bM ∈ centralizer (R₀.map f : Set _) :=
    hcentral (mem_map_of_mem f hb.2)
  obtain ⟨c,hc⟩ := centralizer_scalar (f bM).toLinearMap.toAddMonoidHom (by
    intro g w
    obtain ⟨r,rfl⟩ := m.onto g
    have he := congrArg (fun a : Binary.V ≃ₗ[ZMod 2] Binary.V => a w)
      (hbC (f ⟨r,R.le_normalizer r.property⟩) (mem_map_of_mem f r.property))
    change (f ⟨r,R.le_normalizer r.property⟩).toLinearMap (f bM w) =
      f bM ((f ⟨r,R.le_normalizer r.property⟩).toLinearMap w) at he
    rw [hR] at he
    exact he.symm)
  change ∀ w, f bM w = c • w at hc
  obtain ⟨z,hz2,hzV,hzT⟩ := m.exists_central_involution_tensorLine
  have hzΩ : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨m.tensorLine_le_sylow hzV,hz2 ▸ pow_orderOf_eq_one z,hzT⟩
  let v : V := ⟨z,m.tensorLine_le_fullModule hzV⟩
  have hv : (m.sectionData.coordinates v).toAdd ≠ 0 := by
    intro hv
    have hz : z = 1 :=
      (m.sectionData.coordinates_eq_one_iff v).mp (Multiplicative.toAdd.injective hv)
    simp [hz] at hz2
  have hfix : f bM (m.sectionData.coordinates v).toAdd =
      (m.sectionData.coordinates v).toAdd := by
    rw [hformula]
    congr 2
    apply Subtype.ext
    change b*z*b⁻¹=z
    rw [←(m.hstar_centralizes_sylowOmega hH hb.1 z hzΩ),mul_inv_cancel_right]
  have hc1 : c = 1 := by
    have hh := (hc (m.sectionData.coordinates v).toAdd).symm.trans hfix
    exact (smul_left_injective Binary.F hv) (hh.trans (one_smul _ _).symm)
  intro w hw
  let wV : V := ⟨w,hw⟩
  have hfixw : f bM (m.sectionData.coordinates wV).toAdd =
      (m.sectionData.coordinates wV).toAdd := by rw [hc,hc1,one_smul]
  rw [hformula] at hfixw
  have hh := congrArg Subtype.val (m.coordinates_injective
    (Multiplicative.toAdd.injective hfixw))
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

