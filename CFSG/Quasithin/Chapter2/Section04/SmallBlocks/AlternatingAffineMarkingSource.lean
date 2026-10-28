module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingMarkedSylowSource
public import Theory.SpecificGroups.BinaryFiveAffine.SylowMarking
/-!
# The marked affine model in the single alternating-five case

When the centralizer factor is trivial, the natural augmentation-module
extension is the binary affine five-point model. Sylow conjugacy aligns the
actual Sylow subgroup while its characteristic two-core preserves the module.

Source: Aschbacher–Smith (2.4.29), printed p.545.
-/
@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_marked_affine_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥) :
    ∃ eH : d.H ≃* BinaryFiveAffine.W,
      ((blockU d.block).map d.block.subtype).map eH.toMonoidHom=BinaryFiveAffine.vectorGroup ∧
      (d.S : Subgroup d.H).map eH.toMonoidHom=(BinaryFiveAffine.standardSylow : Subgroup BinaryFiveAffine.W) := by
  let U := (blockU d.block).map d.block.subtype
  let D := centralizer (d.block : Set d.H)
  let : d.block.Normal := hsingle ▸ d.L0_normal
  obtain ⟨q,e,hq,hker,hC,he⟩ := d.single_alternating_marked_action hsingle hA
  obtain ⟨hLq,hkL⟩ := d.single_alternating_residual_action hsingle q hq hker
  rw [d.single_block_core_intrinsic_source hG T hST hsingle] at hkL
  have hki : q.ker ⊓ d.block = U := by
    have hh := congrArg (map d.block.subtype) hkL
    change (q.ker.subgroupOf d.block).map d.block.subtype = U at hh
    rwa [subgroupOf_map_subtype] at hh
  obtain ⟨hd,hDz,hDe,hcore,hDS⟩ :=
    d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA
  let : IsElementaryAbelian 2 D := hDe
  obtain ⟨t,_,ht,ho⟩ := d.single_alternating_odd_involution hsingle hA q e hker hC he
  obtain ⟨E,_,_⟩ := BinaryPermutation.AlternatingFiveExtension.marked_product_equiv
    q U d.block D (map_subtype_le _) hLq hki rfl hDz
    (hker.trans hcore) hd e he t (by rw [←ht]; exact pow_orderOf_eq_one t) ho
  have hDi : D=⊥ := by
    apply (map_eq_bot_iff_of_injective D d.H.subtype_injective).mp
    exact (d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA).trans hD
  let : Subsingleton D := by rw [hDi]; infer_instance
  let : Unique D := ⟨⟨1⟩,fun x=>Subsingleton.elim x 1⟩
  let f : d.H ≃* BinaryFiveAffine.W := E.trans MulEquiv.prodUnique
  have hcore' : pCore 2 d.H=U := by
    change pCore 2 d.H=U⊔D at hcore
    simpa only [hDi,sup_bot_eq] using hcore
  exact BinaryFiveAffine.exists_sylow_marked_equiv f U hcore' d.S

end CFSG.Quasithin.Chapter2
