module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorFiveAmbient
public import Theory.Representation.BinaryTensorThree.OddDisplacement
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter

/-!
# The full local centralizer of a large tensor subspace

The odd-order displacement bound makes the induced action fixing a
subspace of codimension at most three a two-group, so its actual E.3.37
parameter is one. The full local centralizer is also a two-group once
the ambient action kernel supplied by 8.3.10(2) is included. The kernel
is embedded in the original C_M(V), never discarded.

The Source application supplies that kernel bound from the same original
point-centralizer argument; QuietTensorStrictR uses the resulting
parameter in E.6.27.
Source: Aschbacher--Smith H.4.12(3) and 8.3.11, printed pp.385,726.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Representation.BinaryOffender
open ChapterE.Section06.FixedPointBounds
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The literal action fixing a subspace of corank at most three is a two-group. -/
theorem quiet_tensor_small_fixed_image_isTwoGroup
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {U X : Subgroup G} (hUV : U ≤ D.fullModule)
    (hXN : X ≤ normalizer (D.fullModule : Set G))
    (hXU : X ≤ centralizer (U : Set G)) (hc : subgroupCorank D.fullModule U ≤ 3) :
    IsPGroup 2 (inducedAutomizer D.fullModule X) := by
  obtain ⟨f,hf⟩ := quiet_tensor_automizer_coordinates D hn e hbase
  let A := inducedAutomizer D.fullModule X
  have hcod : fixedCodim (automizerRepresentation D.fullModule) A ≤ 3 := by
    rw [fixedCodim_inducedAutomizer D.fullModule X hXN]
    exact (Section06.subgroupCorank_antitone
      (le_inf hUV (le_centralizer_iff.mp hXU))).trans hc
  have he := fixedCodim_map_equivariant (automizerRepresentation D.fullModule)
    BinaryTensorThree.action f.toMonoidHom e hf A
  have hp := BinaryTensorThree.isTwoGroup_of_fixedCodim_le_three (A.map f.toMonoidHom)
    (by rwa [←he])
  exact hp.of_injective (f.toMonoidHom.subgroupMap A)
    (fun _ _ h => Subtype.ext (f.injective (congrArg Subtype.val h)))

/-- The original E.3.37 odd Cartan parameter is one on this actual action image. -/
theorem quiet_tensor_small_fixed_nPrime_eq_one
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {U X : Subgroup G} (hUV : U ≤ D.fullModule)
    (hXN : X ≤ normalizer (D.fullModule : Set G))
    (hXU : X ≤ centralizer (U : Set G)) (hc : subgroupCorank D.fullModule U ≤ 3) :
    nPrime (inducedAutomizer D.fullModule X) = 1 := by
  have hp := quiet_tensor_small_fixed_image_isTwoGroup D hn e hbase hUV hXN hXU hc
  apply le_antisymm ?_ one_le_nPrime
  apply nPrime_le_iff.mpr
  intro c w
  have ho : Odd (Nat.card w.cyclicGroup) :=
    w.odd.of_dvd_nat (card_dvd_of_le w.cyclic_le)
  obtain ⟨k,hk⟩ := (hp.to_subgroup w.cyclicGroup).exists_card_eq
  rw [hk] at ho
  have hk0 : k = 0 := by
    by_contra h
    exact (by decide : ¬ Odd (2 : ℕ)) ((Nat.odd_pow_iff h).mp ho)
  have hw : 1 = 2^c-1 := by simpa only [hk,hk0,pow_zero] using w.card
  have hpow : c+1 ≤ 2^c := c.lt_two_pow_self
  omega

/-- Include the full kernel from 8.3.10(2): C_M(U), not just its action image,
is a two-group for every subspace U of corank at most three. -/
theorem quiet_tensor_small_local_centralizer_isTwoGroup
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    (hk : IsPGroup 2 (centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal)))
    {U : Subgroup G} (hUV : U ≤ D.fullModule) (hc : subgroupCorank D.fullModule U ≤ 3) :
    IsPGroup 2 (D.maximalLocal ⊓ centralizer (U : Set G) : Subgroup G) := by
  let C := D.maximalLocal ⊓ centralizer (U : Set G)
  have hCN : C ≤ normalizer (D.fullModule : Set G) :=
    inf_le_left.trans D.maximalLocal_normalizes_fullModule
  let f : C →* Automizer D.fullModule :=
    D.fullModule.normalizerMonoidHom.rangeRestrict.comp (inclusion hCN)
  have hf : f.range ≤ inducedAutomizer D.fullModule C := by
    rintro _ ⟨c,rfl⟩
    exact ⟨inclusion hCN c,c.property,rfl⟩
  have hp : IsPGroup 2 f.range :=
    (quiet_tensor_small_fixed_image_isTwoGroup D hn e hbase hUV hCN inf_le_right hc).to_le hf
  have hker (a : f.ker) : (a.val : G) ∈ centralizer (D.fullModule : Set G) := by
    have hh : inclusion hCN a.val ∈ D.fullModule.normalizerMonoidHom.ker :=
      congrArg (fun x : Automizer D.fullModule => x.val) a.property
    rwa [normalizerMonoidHom_ker] at hh
  let j : f.ker →* centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal) :=
    { toFun := fun a => ⟨⟨a.val.val,a.val.property.1⟩,fun v hv =>
        Subtype.ext (hker a v hv)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal) => a.val.val) hh
  have hpre := hp.comap_of_ker_isPGroup f (hk.of_injective j hj)
  have htop : f.range.comap f = ⊤ := by
    apply top_unique
    intro a _
    exact ⟨a,rfl⟩
  rw [htop] at hpre
  exact hpre.of_surjective (⊤ : Subgroup C).subtype (by intro a; exact ⟨⟨a,mem_top _⟩,rfl⟩)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
