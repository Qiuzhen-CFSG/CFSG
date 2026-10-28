module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NaturalConfiguration
public import CFSG.Quasithin.ChapterC.Section06.NaturalGlobal

/-!
# Original 2.4.8(1) and the initial Thompson geometry of (3)

For the actual single natural block, choose an index-two overgroup of its
Sylow image inside T. The proved C.5 source constructs its marking and
escaping conjugate. The original 2.4.4 normalizer control then lets the full
natural C.6 argument identify that overgroup with T. Thus S has index two
in T, J(S)=J(T)=Baum(S), and the original two-core pair is the full maximum
elementary family in both S and T, for every x in T-S.

Source: Aschbacher--Smith 2.4.8(1) and the first paragraph of its proof,
printed p.529. Replacing Q by U in (3) uses the subsequent torus argument.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_natural_global_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ}
    (hK : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ChapterB.baumann S = elementaryAbelianMaxJ S ∧
      twoCore d.H = (d.block.map d.H.subtype).pCoreIn 2 ⊔
        (S ⊓ centralizer (d.block.map d.H.subtype : Set G)) ∧
      ∀ x ∈ (T : Subgroup G), x ∉ S →
        elementaryAbelianMaxJ S = twoCore d.H ⊔
          (twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom ∧
        elementaryAbelianMaxSubgroups S =
          {twoCore d.H,(twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom} ∧
        elementaryAbelianMaxSubgroups (T : Subgroup G) =
          {twoCore d.H,(twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom} := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,F,hF,h,_,x,hx,hnc⟩ := d.single_natural_configuration hG T hST.le hsingle
    hK M₀ hSM hMT hi
  exact ChapterC.Section06.natural_global_from_original c h hK T T.isPGroup' hMT
    (fun W hW hWS hHW => lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
      W hW hWS ((normal_subgroupOf_iff_le_normalizer
        (hWS.trans (map_subtype_le _))).mpr hHW)) hi x hx hnc

theorem MinimalBlockSetup.lemma_2_4_8_1
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ}
    (hK : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    S.relIndex (T : Subgroup G) = 2 ∧
      (T : Subgroup G) ≤ normalizer (S : Set G) ∧
      (T : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  have hi := (d.single_natural_global_source hG T hST hsingle hK).1
  have hn : (S.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST.le).mp hn
  exact ⟨hi,hTS,hTS.trans (normalizer_le_normalizer_elementaryAbelianMaxJ S)⟩

end CFSG.Quasithin.Chapter2
