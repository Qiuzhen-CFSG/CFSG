module
public import CFSG.Quasithin.Chapter14.Section06.SourceDihedralFactors
public import Theory.GroupTheory.DihedralPairNormalizer

/-!
# The cubic pair kernel and the remaining quintic obstruction

In the original plane branch, the primitive odd residual lies in Jhat
and is self-centralizing. An element fixing both D₆ factors acts innerly
on each; after multiplying by their inner representatives it centralizes
Jhat, so belongs to Jhat. Thus the actual factor-permutation kernel is
Jhat in the cubic case.

The nonsingleton source theorem already supplies the dihedral actors,
support dimensions and exchanging Sylow element. Applying the kernel
argument to those same actors leaves only two D₁₀ factors of dimension
four. Any failure of kernel equality then supplies a literal kernel
element outside Jhat, conjugating a marked rotation to its square or
cube. Excluding this quintic configuration requires the full ambient
geometry; this module does not claim original 14.6.12 in that case.

Source: Aschbacher--Smith 14.6.12(2), printed p.1031, and D.2.17(1)--(2),
printed p.188 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {M : Subgroup G}
namespace SourcePairCompatibility
/-- The literal unresolved quintic configuration. The kernel element acts
outerly on a marked factor rotation; no ambient model conclusion is assumed. -/
structure QuinticOuterAction
    {J : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index) where
  two_factors : Nat.card d.Index = 2
  dihedral : ∀ k, Nonempty ((f.ambientFactor d k).actor ≃* DihedralGroup 5)
  dimension : ∀ k, Module.finrank (ZMod 2) (f.ambientFactor d k).space = 4
  factor : d.Index
  marking : (f.ambientFactor d factor).actor ≃* DihedralGroup 5
  element : J ⧸ pCore 2 J
  fixes_factors : element ∈ π.ker
  outside_join : element ∉ ChapterD.Jhat a.representation
  rotation_action :
    element * (marking.symm (DihedralGroup.r 1) : J ⧸ pCore 2 J) * element⁻¹ =
        (marking.symm (DihedralGroup.r 1) : J ⧸ pCore 2 J)^2 ∨
    element * (marking.symm (DihedralGroup.r 1) : J ⧸ pCore 2 J) * element⁻¹ =
        (marking.symm (DihedralGroup.r 1) : J ⧸ pCore 2 J)^3
end SourcePairCompatibility
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab


theorem source_ratio_pair_cubic_kernel
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (_hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (hker : ChapterD.Jhat a.representation ≤ π.ker)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (hcubic : ∀ k, Nonempty ((f.ambientFactor d k).actor ≃* DihedralGroup 3)) :
    ChapterD.Jhat a.representation = π.ker := by
  have hcount := (source_ratio_factor_count hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp).1
  have hc : Nat.card d.Index = 2 := by omega
  obtain ⟨i,j,_,_,hjoin,_,hcom,_,_⟩ := f.two_factor_moved_decomposition d hc
  have hPK := source_solvable_minimal_residual_le_Jhat
    hG T hempty hM hu hmany hcard e hab J hJ hs a
  have hcent : centralizer (ChapterD.Jhat a.representation : Set (J ⧸ pCore 2 J)) ≤
      ChapterD.Jhat a.representation :=
    (centralizer_le hPK).trans
      ((centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)).trans hPK)
  apply le_antisymm hker
  intro g hg
  have hn (k : d.Index) : g ∈ normalizer ((f.ambientFactor d k).actor : Set _) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (f.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom = _
    simpa only [show π g = 1 from hg,Equiv.Perm.one_apply] using hp g k
  rw [← hjoin] at hcent ⊢
  exact normalizer_intersection_le_join_dihedral_three _ _
    (hcubic i).some (hcubic j).some hcom hcent ⟨hn i,hn j⟩

/-- The source pair is already the index-two kernel in the cubic case.
Any failure in the quintic case has an explicit order-four action on a
marked rotation in one of the actual embedded factors. -/
theorem source_ratio_nonsingleton_kernel_reduction
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index) :
    ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
      ChapterD.Jhat a.representation ≤ π.ker ∧
      (π.ker.comap (QuotientGroup.mk' (pCore 2 J))).index = 2 ∧
      (∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (f.ambientFactor d (π g i)).actor) ∧
      (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) ∧
      ((ChapterD.Jhat a.representation = π.ker ∧
          (ChapterD.Jhat a.representation).index = 2) ∨
        Nonempty (SourcePairCompatibility.QuinticOuterAction a f d π)) := by
  classical
  obtain ⟨π,hker,hindex,hp,ht⟩ := source_ratio_nonsingleton_index_two_preimage
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
  refine ⟨π,hker,hindex,hp,ht,?_⟩
  by_cases he : ChapterD.Jhat a.representation = π.ker
  · refine Or.inl ⟨he,?_⟩
    rw [he]
    exact (π.ker.index_comap_of_surjective (QuotientGroup.mk'_surjective (pCore 2 J))).symm.trans hindex
  obtain ⟨hc,p,m,hpm,_hmark,hmarked,i,j,_hij,_hall,hjoin,_hdis,hcom,_⟩ :=
    source_ratio_nonsingleton_dihedral hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hmore
  rcases (ChapterD.CyclicSource.primeDimensionOptions_iff p m).mp hpm with ⟨rfl,_⟩ | ⟨rfl,rfl⟩
  · exact (he (source_ratio_pair_cubic_kernel hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hmore π hker hp (fun k => (hmarked k).1))).elim
  have hnle : ¬ π.ker ≤ ChapterD.Jhat a.representation := fun h => he (le_antisymm hker h)
  obtain ⟨g,hg,hgout⟩ := Set.not_subset.mp hnle
  have hn (k : d.Index) : g ∈ normalizer ((f.ambientFactor d k).actor : Set _) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (f.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom = _
    simpa only [show π g = 1 from hg,Equiv.Perm.one_apply] using hp g k
  have hPK := source_solvable_minimal_residual_le_Jhat
    hG T hempty hM hu hmany hcard e hab J hJ hs a
  have hcent : centralizer (ChapterD.Jhat a.representation : Set (J ⧸ pCore 2 J)) ≤
      ChapterD.Jhat a.representation :=
    (centralizer_le hPK).trans
      ((centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)).trans hPK)
  have houter : ∃ k : d.Index, ¬ ∃ b : (f.ambientFactor d k).actor,
      ∀ x : (f.ambientFactor d k).actor,
        g * x * g⁻¹ = (b : J ⧸ pCore 2 J) * x * (b : J ⧸ pCore 2 J)⁻¹ := by
    by_contra hall
    push Not at hall
    apply hgout
    rw [←hjoin] at hcent ⊢
    exact mem_join_of_inner_on_commuting_factors _ _ hcom hcent g (hall i) (hall j)
  obtain ⟨k,hk⟩ := houter
  let ek := (hmarked k).1.some
  exact Or.inr ⟨{
    two_factors := hc
    dihedral := fun k => (hmarked k).1
    dimension := fun k => (hmarked k).2
    factor := k
    marking := ek
    element := g
    fixes_factors := hg
    outside_join := hgout
    rotation_action := outer_on_dihedral_five_rotation _ ek g (hn k) hk }⟩


/-- In the cubic branch the actor join and its literal preimage have
index two, and the actor join equals the actual transitive kernel. -/
theorem source_ratio_nonsingleton_cubic_index_two
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index)
    (hcubic : ∀ k, Nonempty ((f.ambientFactor d k).actor ≃* DihedralGroup 3)) :
    (ChapterD.Jhat a.representation).index = 2 ∧
      ((ChapterD.Jhat a.representation).comap (QuotientGroup.mk' (pCore 2 J))).index = 2 ∧
      ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
        ChapterD.Jhat a.representation = π.ker ∧
        (∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (f.ambientFactor d (π g i)).actor) ∧
        (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) := by
  obtain ⟨π,hker,hindex,hp,ht⟩ := source_ratio_nonsingleton_index_two_preimage
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
  have he := source_ratio_pair_cubic_kernel hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd hmore π hker hp hcubic
  have hqindex := (π.ker.index_comap_of_surjective
    (QuotientGroup.mk'_surjective (pCore 2 J))).symm.trans hindex
  exact ⟨he.symm ▸ hqindex, he.symm ▸ hindex, π,he,hp,ht⟩

end CFSG.Quasithin.Chapter14.Section06
