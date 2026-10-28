module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Normalizer
public import CFSG.Quasithin.Chapter10.SourceWeakClosure
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.SourceOmega
public import Theory.GroupTheory.SylowNormalizerConjugate

/-!
# The original tensor hyperplane obstruction

The original full module satisfies E.6.1. Its determinant coordinates have
no binary transvection in the full local normalizer, so an element of M
centralizing a hyperplane centralizes V. Thus every escaping hyperplane
belongs to the original obstruction family.

If N_T(U) fixes only vectors in U, the central tensor involution lies in U.
The proved E.6.10(4) then supplies an Omega-center element outside U, while
9.2.2 puts that same Omega center inside the fixed space. The final Sylow
conjugacy choice retains the escaping centralizer and the original module.
The remaining matrix fixed-space calculation is supplied by a separate
source consumer, with these literal subgroups and coordinates.

Source: Aschbacher--Smith 9.2.3, printed p.730, using 9.2.2 and E.6.10(4).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ChapterE.Section06 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

theorem tensor_hypothesisE61 :
    HypothesisE61 KnownSimple.IsKnownSimple T D.maximalLocal D.fullModule := by
  have hu := D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_sup_right.trans hu.2.1
  have hVN := D.maximalLocal_normalizes_fullModule
  refine ⟨D.simpleQTKE,hu.1,hTM,?_,m.fullModule_elementary,m.fullModule_le_sylow,
    (normal_subgroupOf_iff_le_normalizer m.fullModule_le_sylow).mpr (hTM.trans hVN),?_,?_⟩
  · intro he
    have hc := m.card_fullModule
    rw [he,Subgroup.card_bot] at hc
    omega
  · intro g hg
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hVN hg))
  · intro N hN hle
    apply hu.2.2 N hN
    apply le_trans _ hle
    exact le_inf (le_inf hu.2.1 (hu.2.1.trans hVN))
      (source_join_normalizes_full_sylow_centralizer D
        (source_module_nonsolvable_uniqueness D))

theorem tensor_hyperplane_image_finrank {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hc : subgroupCorank D.fullModule U = 1) :
    Module.finrank (ZMod 2) (m.sectionData.imageSpace U) = 7 := by
  let := m.fullModule_elementary
  have hi : U.relIndex D.fullModule = 2 ^ 1 := by
    have hh := D.fullModule.relIndex_eq_two_pow_quotient_finrank U
    rw [← subgroupCorank_eq_quotient_finrank, hc] at hh
    exact hh
  have hh := m.sectionData.imageSpace_codimension_of_index U hUV bot_le 1 hi
  rw [Binary.finrank_binary] at hh
  omega

theorem tensor_hyperplane_local_centralizer {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hc : subgroupCorank D.fullModule U = 1) :
    D.maximalLocal ⊓ centralizer (U : Set G) =
      D.maximalLocal ⊓ centralizer (D.fullModule : Set G) := by
  apply le_antisymm
  · rintro c ⟨hcM,hcU⟩
    refine ⟨hcM,?_⟩
    let a : D.maximalLocal := ⟨c,hcM⟩
    let δ := (m.maximalAction a).toLinearMap - LinearMap.id
    have hW : m.sectionData.imageSpace U ≤ δ.ker := by
      intro v hv
      obtain ⟨b,hb,rfl⟩ := (m.sectionData.mem_imageSpace_iff U v).mp hv
      change m.maximalAction a (m.sectionData.coordinates b).toAdd -
        (m.sectionData.coordinates b).toAdd = 0
      rw [m.maximalAction_coordinates]
      have hf : D.fullModule.normalizerMonoidHom
          ⟨a,D.maximalLocal_normalizes_fullModule a.property⟩ b = b := by
        apply Subtype.ext
        change c * (b : G) * c⁻¹ = (b : G)
        rw [← hcU b hb,mul_inv_cancel_right]
      rw [hf,sub_self]
    have hdim := Submodule.finrank_mono hW
    rw [m.tensor_hyperplane_image_finrank hUV hc] at hdim
    have hsum := δ.finrank_range_add_finrank_ker
    rw [Binary.finrank_binary] at hsum
    have hn := m.maximalAction_no_transvection a
    have hzero : Module.finrank (ZMod 2) δ.range = 0 := by
      change Module.finrank (ZMod 2) δ.range ≠ 1 at hn
      omega
    have hz : δ = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero)
    have hid : m.maximalAction a = 1 := by
      apply LinearEquiv.toLinearMap_injective
      exact sub_eq_zero.mp hz
    intro b hb
    let v : D.fullModule := ⟨b,hb⟩
    have hf := m.maximalAction_coordinates a v
    rw [hid] at hf
    have he : v = D.fullModule.normalizerMonoidHom
        ⟨a,D.maximalLocal_normalizes_fullModule a.property⟩ v :=
      m.coordinates_injective (Multiplicative.toAdd.injective hf)
    have he' := congrArg Subtype.val he
    change b = c*b*c⁻¹ at he'
    exact (mul_inv_eq_iff_eq_mul.mp he'.symm).symm
  · exact inf_le_inf_left _ (centralizer_le hUV)

theorem tensor_hyperplane_obstruction {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hc : subgroupCorank D.fullModule U = 1)
    (he : ¬ centralizer (U : Set G) ≤ D.maximalLocal) :
    U ∈ obstructionFamily D.maximalLocal D.fullModule := by
  refine ⟨hUV,?_,he,oddCentralizerCondition_of_eq
    (m.tensor_hyperplane_local_centralizer hUV hc)⟩
  intro hz
  have hd := m.tensor_hyperplane_image_finrank hUV hc
  have him : m.sectionData.imageSpace U = ⊥ := by
    rw [hz]
    ext v
    rw [m.sectionData.mem_imageSpace_iff]
    constructor
    · rintro ⟨b,hb,rfl⟩
      have hb1 : b = 1 := Subtype.ext hb
      simp [hb1]
    · intro hv
      exact ⟨1,by simp,by simpa using hv.symm⟩
  rw [him] at hd
  simp at hd

theorem tensor_hyperplane_fixed_control_false
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hc : subgroupCorank D.fullModule U = 1)
    (he : ¬ centralizer (U : Set G) ≤ D.maximalLocal)
    (hfixed : D.fullModule ⊓ centralizer
      ((T : Subgroup G) ⊓ normalizer (U : Set G) : Set G) ≤ U) : False := by
  have hU := m.tensor_hyperplane_obstruction hUV hc he
  obtain ⟨z,hz,hzline,hzT⟩ := m.exists_central_involution_tensorLine
  have hzV := m.tensorLine_le_fullModule hzline
  have hzfix : z ∈ sylowFixedSpace (T : Subgroup G) D.fullModule := ⟨hzV,hzT⟩
  have hzU : z ∈ U := hfixed ⟨hzV,fun a ha => hzT a ha.1⟩
  have hZ : U ⊓ sylowFixedSpace (T : Subgroup G) D.fullModule ≠ ⊥ := by
    intro hh
    have hh1 : z = 1 := hh.le ⟨hzU,hzfix⟩
    rw [hh1,orderOf_one] at hz
    omega
  have hn := m.tensor_hypothesisE61.source_omega_center_not_le hU hc (Or.inl hZ)
  apply hn
  have hcore : (localJoin T L).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ normalizer (U : Set G) := by
    have hh := D.sylow_centralizer_module (source_module_nonsolvable_uniqueness D)
    rw [m.module_eq] at hh
    rw [← hh]
    exact le_inf inf_le_left (inf_le_right.trans
      ((centralizer_le hUV).trans (Subgroup.centralizer_le_normalizer _)))
  have hOmega := m.omegaCenter_eq_fullModule_inf hout _ hcore inf_le_left
  intro x hx
  have hxo : x ∈ omegaCenterIn ((T : Subgroup G) ⊓ normalizer (U : Set G)) := by
    obtain ⟨hxS,hx2,hxC⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hxS,hxC,hx2⟩
  exact hfixed (hOmega.le hxo)

theorem tensor_hyperplane_normalizer_choice {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hc : subgroupCorank D.fullModule U = 1)
    (he : ¬ centralizer (U : Set G) ≤ D.maximalLocal) :
    ∃ W : Subgroup G, W ≤ D.fullModule ∧ subgroupCorank D.fullModule W = 1 ∧
      ¬ centralizer (W : Set G) ≤ D.maximalLocal ∧
      ¬ 2 ∣ (T : Subgroup G).relIndex
        (D.maximalLocal ⊓ normalizer (W : Set G)) := by
  have hTM := m.tensor_hypothesisE61.sylow_le
  obtain ⟨g,hg,hi⟩ := T.exists_conjugate_normalizer_not_dvd_relIndex
    D.maximalLocal U hTM
  let f := (MulAut.conj g).toMonoidHom
  have hV : D.fullModule.map f = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hg)
  refine ⟨U.map f,(map_mono hUV).trans_eq hV,?_,?_,hi⟩
  · unfold subgroupCorank at hc ⊢
    rw [← hV,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hc
  · intro hh
    apply he
    intro a ha
    have hfa : f a ∈ centralizer (U.map f : Set G) := by
      rintro _ ⟨b,hb,rfl⟩
      exact (map_mul f b a).symm.trans ((congrArg f (ha b hb)).trans (map_mul f a b))
    exact (mem_normalizer_iff.mp (D.maximalLocal.le_normalizer hg) a).mpr (hh hfa)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
