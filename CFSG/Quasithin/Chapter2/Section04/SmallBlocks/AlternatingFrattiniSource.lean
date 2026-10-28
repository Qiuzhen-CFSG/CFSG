module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingMarkedSylowSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingExtraspecialSource
public import Theory.SpecificGroups.SymmetricFourWreath.NormalElementaryGeometry
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Overgroups
public import Theory.Frattini.SquareImage

/-!
# The original single A5 Frattini subgroup lies in the Borel core

The marked Sylow model maps the original selected subgroup to the dihedral
wreath group times its block centralizer. When that centralizer is trivial,
the standard two sign flags have kernel equal to the original quaternion
Borel core. Their exponent-two image kills the Frattini subgroup, giving the
literal ambient bound needed by square transfer.

Source: Aschbacher–Smith, 2.4.29, printed pp.545–546.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_frattini_le_core
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let S := (d.S : Subgroup d.H).map d.H.subtype
    (frattini S).map S.subtype ≤ P := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let D := centralizer (d.block : Set d.H)
  have hDe := (d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA).2.2.1
  let : IsElementaryAbelian 2 D := hDe
  obtain ⟨e,he⟩ := d.single_alternating_marked_ambient_sylow_model hG T hM hTM hu hST hsingle hA
  obtain ⟨hPS,hSP⟩ := d.single_borel_core_placement hsingle
  let Q := P.subgroupOf S
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer hPS).mpr hSP
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  let hq := hp.map (subgroupOfEquivOfLe hPS).symm
  let : IsExtraspecial 2 Q := hq.extraspecial
  have hcQ : Nat.card Q = 32 := hq.card
  let a := (MonoidHom.fst SymmetricFourWreath.P D).comp e.toMonoidHom
  have hker : a.ker = ⊥ := by
    rw [he,d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA,hD]
    simp
  have hQ : Q = SymmetricFourWreath.coreInP.comap a := by
    have hh := SymmetricFourWreath.core_sup_factor_eq_comap_of_equiv_prod e Q hcQ
    rwa [hker,sup_bot_eq] at hh
  let f := SymmetricFourWreath.sylowFlags.comp a
  have hphi : frattini S ≤ f.ker := by
    apply Theory.GroupTheory.frattini_le_ker_of_square_image
    intro s
    have hs : ∀ x : SymmetricFourWreath.C2 × SymmetricFourWreath.C2, x ^ 2 = 1 := by decide
    exact hs (f s)
  have hfk : f.ker = Q := by
    rw [← MonoidHom.comap_ker,SymmetricFourWreath.sylowFlags_ker,←hQ]
  have hm := map_mono (f:=S.subtype) (hphi.trans_eq hfk)
  rwa [map_subgroupOf_eq_of_le hPS] at hm
end CFSG.Quasithin.Chapter2
