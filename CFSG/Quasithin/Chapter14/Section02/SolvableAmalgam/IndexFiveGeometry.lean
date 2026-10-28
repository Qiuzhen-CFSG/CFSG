module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NonabelianGeometry
public import Theory.SpecificGroups.SymmetricFive.ElementaryFiveNormalizer

/-!
# Elementary index bound in the original index-five branch

The selected Chapter 14 hypotheses give the literal opposite-vertex
elementary image E in H/O₂(H), with an elementary A≤U=⟨V^H⟩ satisfying
[U:A]=2|E|. Each actual index-five model, D₁₀ or Sz(2), has elementary
two-subgroups of order at most two. Thus nonabelian U has such an A
with index at most four. The original opposite-vertex hypotheses are
retained throughout.

Source: Aschbacher–Smith 14.2.20(1), printed p.987, using G.2.3.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
variable {G : Type*} [Group G] [Finite G]

theorem source_index_five_elementary_subgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hmodel : Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H)) :
    ∃ A : Subgroup G, A ≤ conjugateSpanBy (localModule T M) H ∧
      IsElementaryAbelian 2 A ∧ A.relIndex (conjugateSpanBy (localModule T M) H) ≤ 4 := by
  obtain ⟨E,hE,A,hAU,hA,hindex⟩ :=
    source_nonabelian_elementary_image hG T hempty hM hu hmany hcard e H hH hne
  let : IsElementaryAbelian 2 E := hE
  have hbound : Nat.card E ≤ 2 := by
    rcases hmodel with hmodel | hmodel
    · obtain ⟨f⟩ := hmodel
      let : IsElementaryAbelian 2 (E.map f.toMonoidHom) := IsElementaryAbelian.map _
      have hh := elementary_dihedral_five_card_le_two (E.map f.toMonoidHom)
      rwa [card_map_of_injective f.injective] at hh
    · obtain ⟨f⟩ := hmodel
      let : IsElementaryAbelian 2 (E.map f.toMonoidHom) := IsElementaryAbelian.map _
      have hh := elementary_suzuki_zero_card_le_two (E.map f.toMonoidHom)
      rwa [card_map_of_injective f.injective] at hh
  exact ⟨A,hAU,hA,hindex ▸ (by omega)⟩

end CFSG.Quasithin.Chapter14.Section02
