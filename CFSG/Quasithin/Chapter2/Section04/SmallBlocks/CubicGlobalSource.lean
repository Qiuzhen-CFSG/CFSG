module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NormalizerSource
public import CFSG.Quasithin.ChapterC.Section06.CubicGlobal
/-!
# The global C.6 alternative for the original single cubic shadow

The selected block constructs the actual C.5 action and escaping conjugator.
The original 2.4.4 normalizer barrier supplies C.6 control. The resulting
S₄ or C₂×S₄ model and global Sylow alternative therefore concern the literal
H and T, with no recognition or Thompson-stability premise.

Source: Aschbacher--Smith 2.4.5(3), C.6.1, printed pp.528,164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_cubic_global_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K := d.block.map d.H.subtype
    let N₀ := (T : Subgroup G) ⊓ normalizer (R : Set G)
    let Q := twoCore d.H
    let D := R ⊓ centralizer (K : Set G)
    R.relIndex N₀ = 2 ∧ ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      primeRank 2 D ≤ 1 ∧ Q = K.pCoreIn 2 ⊔ D ∧
      (∀ y ∈ N₀, y ∉ R →
        elementaryAbelianMaxJ R = Q ⊔ Q.map (MulAut.conj y⁻¹).toMonoidHom ∧
        elementaryAbelianMaxSubgroups R = {Q,Q.map (MulAut.conj y⁻¹).toMonoidHom}) ∧
      ((R.relIndex (T : Subgroup G) = 2 ∧ elementaryAbelianMaxJ R = elementaryAbelianMaxJ T ∧
          Nonempty (d.H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∨
        (Nonempty (d.H ≃* Equiv.Perm (Fin 4)) ∧ (IsDihedralGroup T ∨ IsSemidihedralGroup T))) := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,F,hF,h,x,hx,hnc⟩ := d.single_rankOne_configuration hG T hST.le hsingle
    (Or.inr hK) M₀ hSM hMT hi
  exact ChapterC.Section06.cubic_global_from_original c h hK T T.isPGroup' hST hMT
    (fun W hW hWR hHW => lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
      W hW hWR ((normal_subgroupOf_iff_le_normalizer
        (hWR.trans (map_subtype_le _))).mpr hHW)) hi x hx hnc

end CFSG.Quasithin.Chapter2
