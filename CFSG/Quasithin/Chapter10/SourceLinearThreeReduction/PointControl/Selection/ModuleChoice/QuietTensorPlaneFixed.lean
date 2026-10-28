module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorHeld
public import Theory.Representation.BinaryTensorThree.PlaneFixedTransport

/-!
# The actual plane-radical fixed space in the quiet tensor branch

Align the existing tensor marking with the original Sylow subgroup. The full
preimage R of the two plane radicals lies in T, and its literal fixed space
U = C_V(R) contains the original nonidentity z. The paired plane parabolic
makes U invariant under T. A lifted elementary nine acts faithfully on U,
so the rank bound in the two-local N_G(U) excludes three from C_G(U).
The Source consumer combines this with the checked Held three-free bound,
proving C_G(C_V(R)) ≤ M in the retained Held branch of 8.3.8.

Tensor recognition, the other model branches of 8.3.8, 8.3.9--12, the final
Held exclusion, both quiet exclusions and the two selection outputs remain
source obligations. No natural-coordinate or fixed-kernel shortcut is used.
Source: Aschbacher--Smith, 8.3.8(a)--(c), printed p.725, with the original
minimal module from 3.2.6 and 10.1.1--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
open BinaryTensorThree.PlaneFixed
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The literal plane-radical fixed space in the original full module has
three-free ambient centralizer. The tensor marking is aligned with the
original Sylow, and the faithful elementary-nine actor is constructed. -/
theorem quiet_tensor_plane_fixed_geometry
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ∃ (q : localJoin T L →* Actor)
      (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space),
      Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      ((T : Subgroup G).subgroupOf (localJoin T L)).map q = Matrix.PSL3Two.WreathPair.borel ∧
      (∀ (a : localJoin T L) (v : Additive D.fullModule),
        quietTensorLinearAction D b a (b v) =
          BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v)) ∧
      originalRadical (localJoin T L) q ≤ (T : Subgroup G) ∧
      z ∈ originalFixed D.fullModule (localJoin T L) q ∧
      (T : Subgroup G) ≤ normalizer (originalFixed D.fullModule (localJoin T L) q : Set G) ∧
      ¬ 3 ∣ Nat.card (centralizer (originalFixed D.fullModule (localJoin T L) q : Set G)) := by
  let H := localJoin T L
  have hHV : H ≤ normalizer (D.fullModule : Set G) :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule
  obtain ⟨p,hp,he⟩ := quiet_exists_tensor_marking_of_action_image D e
    (quiet_tensor_action_image_of_orbit_image D hn e hbase)
  have hpk : IsPGroup 2 p.ker := by
    have hf : IsPGroup 2 (quietTensorLinearAction D e).ker := by
      rw [quietTensorLinearAction_ker]
      exact full_module_local_kernel_isTwoGroup D hn
    apply hf.to_le
    intro a ha
    change quietTensorLinearAction D e a = 1
    apply LinearEquiv.ext
    intro X
    obtain ⟨v,rfl⟩ := e.surjective X
    rw [quietTensorLinearAction_apply,he,show p a = 1 from ha,map_one,map_one]
    rfl
  let S : Sylow 2 H := T.subtype le_sup_right
  obtain ⟨q,b,hq,hker,hS,hb⟩ := exists_sylow_marking D.fullModule H hHV p hp e he S
  have hk : IsPGroup 2 q.ker := hker.symm ▸ hpk
  have hR : originalRadical H q ≤ (T : Subgroup G) := by
    have hh := originalRadical_le_sylow H q S hk hS
    simpa only [S,Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)] using hh
  have hzU : z ∈ originalFixed D.fullModule H q :=
    ⟨hzV,fun r hr => mem_centralizer_singleton_iff.mp (hzT (hR hr))⟩
  have hTU := originalFixed_normalized_by_line D.fullModule H hHV q hq b hb
    (T : Subgroup G) le_sup_right (hS.le.trans Matrix.PSL3Two.WreathPair.borel_le_line)
  obtain ⟨A,hA,hcard,hAH,hAU,hfaith⟩ :=
    exists_originalFixed_faithful_nine D.fullModule H hHV q hq b hb hk
  let : IsElementaryAbelian 3 A := hA
  have hne : originalFixed D.fullModule H q ≠ ⊥ := fun heq => hz1 (mem_bot.mp (heq ▸ hzU))
  refine ⟨q,b,hq,hk,hS,?_,hR,hzU,hTU,?_⟩
  · intro a v
    rw [quietTensorLinearAction_apply]
    exact hb a v
  · exact quiet_fixed_space_centralizer_three_free D _ inf_le_left hne A hcard hAU hfaith

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
