module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaNumerical
public import CFSG.Quasithin.Chapter10.SourceA5MinimalParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.CoreFreeBudget

/-!
# The chief-section argument for the original central Omega core

On the faithful action of J=L₀T on Ω=Ω₁Z(O₂(J)), the embedded tensor module
V is faithful because C_J(V)=C_J(Ω)=O₂(J). The original two-factor marking
forces nonnormality of L, hence J and its reduced image are minimal parabolic.
The original maximal two-local group supplies the actual SQTK cover.

If L₀ moved Ω/V, a nontrivial irreducible subquotient would detect its perfect
image. B.6.9 gives one actor rank there, while the original non-FF tensor
module uses strictly more than one rank. Thus cubic ratio at most two forces
[Ω,L₀]≤V. Every kernel, subspace and quotient is the original one.

Source: Aschbacher--Smith 9.2.2(1), using B.6.8--9 and 3.1.8(1).
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- A surjective marked two-factor tensor cannot have a Sylow-normalized first component. -/
theorem sylow_not_normalizes_component : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := by
  intro hn
  have hXL : localOrbit T L ≤ L := iSup_conjugates_le_of_le_normalizer L T L le_rfl hn
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) Binary.F) := m.firstMarking.symm.surjective.nontrivial
  obtain ⟨g,hg⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) Binary.F)
  obtain ⟨x,hx⟩ := m.onto (1,g)
  let l : L := ⟨x,hXL x.property⟩
  have hh := congrArg Prod.snd (m.first_factor l)
  change (m.quotient x).2 = 1 at hh
  rw [hx] at hh
  exact hg hh

/-- The actual larger-module cubic bound discharges the source commutator input. -/
theorem omegaCenter_core_commutator_le_of_cubicRatio_le_two
    (hb : cubicRatio (ChapterD.UniqueFactor.imageRepresentation (localJoin T L)
      (omegaCenterIn ((localJoin T L).pCoreIn 2)) join_normalizes_omegaCenter_core) ≤ 2) :
    ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),localOrbit T L⁆ ≤ D.fullModule := by
  classical
  let J := localJoin T L
  let Ω := omegaCenterIn (J.pCoreIn 2)
  let hnΩ : J ≤ normalizer (Ω : Set G) := join_normalizes_omegaCenter_core
  let H := ChapterD.internalActionImage J Ω hnΩ
  let q : J →* H := (ChapterD.UniqueFactor.actionHom J Ω hnΩ).rangeRestrict
  let ρ := ChapterD.UniqueFactor.imageRepresentation J Ω hnΩ
  have hq : Function.Surjective q := MonoidHom.rangeRestrict_surjective _
  have hqker : q.ker = pCore 2 J := by
    change (ChapterD.UniqueFactor.actionHom J Ω hnΩ).rangeRestrict.ker = _
    rw [MonoidHom.ker_rangeRestrict]
    exact m.omegaCenter_core_action_ker
  have hcore : pCore 2 H = ⊥ :=
    pCore_range_eq_bot_of_ker_eq_pCore 2 _ m.omegaCenter_core_action_ker
  have hnV : J ≤ normalizer (D.fullModule : Set G) := by
    rw [← m.module_eq]
    exact D.join_normalizes_module
  have hVΩ : D.fullModule ≤ Ω := m.fullModule_le_omegaCenter_core
  let U : Subrepresentation ρ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 (D.fullModule.subgroupOf Ω).toAddSubgroup
    apply_mem_toSubmodule := by
      intro a v hv
      obtain ⟨g,rfl⟩ := hq a
      exact (mem_normalizer_iff.mp (hnV g.property) v.toMul).mp hv }
  have hf : Function.Injective U.toRepresentation := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    obtain ⟨g,rfl⟩ := hq a
    have hgC : (g : G) ∈ centralizer (D.fullModule : Set G) := by
      intro v hv
      let w : U.toSubmodule := ⟨Additive.ofMul ⟨v,hVΩ hv⟩,hv⟩
      have hh := congrArg (fun f : Module.End (ZMod 2) U.toSubmodule =>
        (((f w).val.toMul : Ω) : G)) ha
      change (g : G)*v*(g : G)⁻¹ = v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hgQ := m.centralizer_fullModule_join_eq_core.le ⟨g.property,hgC⟩
    have hgk : g ∈ pCore 2 J := by
      obtain ⟨k,hk,hkg⟩ := hgQ
      exact (Subtype.ext hkg : k = g) ▸ hk
    exact (hqker.symm ▸ hgk : g ∈ q.ker)
  let i : localOrbit T L →* J := inclusion le_sup_left
  let j : localOrbit T L →* H := q.comp i
  have hi : i.range = (localOrbit T L).subgroupOf J := by
    ext g
    constructor
    · rintro ⟨x,rfl⟩
      exact x.property
    · intro hg
      exact ⟨⟨g,hg⟩,rfl⟩
  let : i.range.Normal := by
    rw [hi]
    exact normal_subgroupOf_of_le_normalizer
      (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  let : j.range.Normal := by
    rw [show j.range = i.range.map q from MonoidHom.range_comp _ _]
    exact Subgroup.Normal.map inferInstance q hq
  let f₀ : U.toSubmodule →+ Binary.V := {
    toFun v := (m.sectionData.coordinates ⟨v.val.toMul,v.property⟩).toAdd
    map_zero' := congrArg Multiplicative.toAdd m.sectionData.coordinates.map_one
    map_add' v w := congrArg Multiplicative.toAdd
      (m.sectionData.coordinates.map_mul ⟨v.val.toMul,v.property⟩ ⟨w.val.toMul,w.property⟩) }
  let f := f₀.toZModLinearMap 2
  have hf' : Function.Bijective f := by
    constructor
    · intro v w hvw
      have hh : (⟨v.val.toMul,v.property⟩ : D.fullModule) = ⟨w.val.toMul,w.property⟩ :=
        m.coordinates_injective hvw
      exact Subtype.ext (congrArg (fun x : D.fullModule =>
        Additive.ofMul (⟨x,hVΩ x.property⟩ : Ω)) hh)
    · intro w
      obtain ⟨x,hx⟩ := m.sectionData.onto (Multiplicative.ofAdd w)
      exact ⟨⟨Additive.ofMul ⟨x,hVΩ x.property⟩,x.property⟩,hx⟩
  let b : Representation.Equiv (U.toRepresentation.comp j) (Binary.action.comp m.quotient) := {
    toLinearEquiv := LinearEquiv.ofBijective f hf'
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      exact m.sectionData.equivariant g ⟨v.val.toMul,v.property⟩ }
  have hnon := Binary.image_not_ff_of_marked_normal_range U.toRepresentation j m.quotient m.onto b
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hp : ChapterB.IsMinimalParabolicOver S ⊤ :=
    source_a5_minimal_parabolic D e m.sylow_not_normalizes_component
  have hne : q.ker ≠ ⊤ := by
    rw [hqker]
    intro he
    have hs : (⊤ : Subgroup J) ≤ (S : Subgroup J) := he ▸ fitting_pCore_le_sylow S
    exact (ChapterB.minimalParabolicMax_spec S hp).1.ne_top
      (top_unique (hs.trans (ChapterB.minimalParabolicMax_spec S hp).2))
  have hpH := (ChapterB.minimalParabolic_reduced_image S hp q hq hcore hne).2
  have hmax := (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1
  have hJM : J ≤ D.maximalLocal :=
    sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
  have hsM := D.simpleQTKE.twoLocal_sqtk hmax.1
  have hsJ : IsSQTK KnownSimple.IsKnownSimple J :=
    ⟨hsM.stronglyQuasithin.of_injective (inclusion hJM) (inclusion_injective hJM),
      hsM.isKGroup.of_injective (inclusion hJM) (inclusion_injective hJM)⟩
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple H := {
    Cover := J
    kernel := q.ker
    sqtk := hsJ
    equiv := QuotientGroup.quotientKerEquivOfSurjective q hq }
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect (localOrbit T L) := isPerfect_iSup_conjugates L T
  let : Group.IsPerfect j.range := Group.IsPerfect.ofSurjective
    (f := j.rangeRestrict) j.rangeRestrict_surjective
  have hfix := ChapterB.perfect_fixes_quotient_of_nonFF_and_cubic_le_two
    ⟨c⟩ (S.mapSurjective hq) hpH hcore ρ U hf hnon hb j.range
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g hg v hv
  let w : Additive Ω := Additive.ofMul ⟨v,hv⟩
  have hh := congrArg (fun f : Module.End (ZMod 2) (Additive Ω ⧸ U.toSubmodule) =>
    f (U.toSubmodule.mkQ w)) (hfix (show j ⟨g,hg⟩ ∈ j.range from ⟨⟨g,hg⟩,rfl⟩))
  have hd := (Submodule.Quotient.eq U.toSubmodule).mp hh
  change (((ρ (j ⟨g,hg⟩) w - w).toMul : Ω) : G) ∈ D.fullModule at hd
  rw [toMul_sub, div_eq_mul_inv] at hd
  exact hd
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
