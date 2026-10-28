module
public import CFSG.Quasithin.Chapter14.Section06.SourceTransitiveFactors
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.TransitiveDihedral
/-!
# The literal dihedral factors in the nonsingleton source branch

The original solvable outside-minimal subgroup supplies its SQTK cover,
faithful quotient action and Fitting-full ratio factors. If there is more
than one factor, the genuine source classification gives two dihedral
actors of the same prime and dimension. Their supports split the full
moved space, retaining the globally fixed complement. A member of the
original Sylow subgroup exchanges them, and original 14.6.2 puts the
central point in each lifted residual commutator.

Source: Aschbacher--Smith 14.6.12(2)--(3), printed p.1031.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
private theorem pair_preimage_conj {A B : Type*} [Group A] [Group B] (q : A →* B) (P : Subgroup B) (t : A) :
    (P.comap q).map (MulAut.conj t).toMonoidHom =
      (P.map (MulAut.conj (q t)).toMonoidHom).comap q := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨q y,hy,by change q t * q y * (q t)⁻¹ = q (t*y*t⁻¹); rw [map_mul,map_mul,map_inv]⟩
  · rintro ⟨y,hy,hxy⟩
    refine ⟨t⁻¹*x*t,?_,by simp [MulAut.conj_apply,mul_assoc]⟩
    change q (t⁻¹*x*t) ∈ P
    have he : q (t⁻¹*x*t) = y := by
      simp only [map_mul,map_inv]
      rw [←hxy]
      simp [MulAut.conj_apply,mul_assoc]
    exact he.symm ▸ hy

private theorem pair_kernel_index {D I : Type*} [Group D] [Finite I]
    (π : D →* Equiv.Perm I) (hc : Nat.card I = 2)
    (ht : ∀ i j, ∃ g : D, π g i = j) : π.ker.index = 2 := by
  have hd : π.ker.index ∣ 2 := by
    rw [index_ker]
    apply π.range.card_subgroup_dvd_card.trans
    rw [Nat.card_perm,hc]
    exact dvd_rfl
  have hn : π.ker.index ≠ 1 := by
    intro he
    have heq := index_eq_one.mp he
    obtain ⟨i,j,hij,_⟩ := Nat.card_eq_two_iff.mp hc
    obtain ⟨g,hg⟩ := ht i j
    have hgker : π g = 1 := show g ∈ π.ker from heq ▸ mem_top g
    exact hij (by simpa only [hgker,Equiv.Perm.one_apply] using hg)
  exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hn

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab

theorem source_ratio_nonsingleton_dihedral
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index) :
    Nat.card d.Index = 2 ∧
      ∃ p m, ChapterD.CyclicSource.PrimeDimensionOptions p m ∧
      (∀ i, ∃ l : ChapterD.CyclicSource.LocalGeneration (d.factor i).action,
        ChapterD.CyclicSource.DihedralMarking l p m) ∧
      (∀ k, Nonempty ((f.ambientFactor d k).actor ≃* DihedralGroup p) ∧
        Module.finrank (ZMod 2) (f.ambientFactor d k).space = 2*m) ∧
      ∃ i j : d.Index, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
        (f.ambientFactor d i).actor ⊔ (f.ambientFactor d j).actor = ChapterD.Jhat a.representation ∧
        Disjoint (f.ambientFactor d i).actor (f.ambientFactor d j).actor ∧
        (∀ x ∈ (f.ambientFactor d i).actor,
          ∀ y ∈ (f.ambientFactor d j).actor, Commute x y) ∧
        (f.ambientFactor d i).space ⊔ (f.ambientFactor d j).space =
          subspaceCommutator a.representation ⊤ ⊤ ∧
        Disjoint (f.ambientFactor d i).space (f.ambientFactor d j).space ∧
        ((f.ambientFactor d i).space ⊔ (f.ambientFactor d j).space) ⊔
          fixedSpace a.representation ⊤ = ⊤ ∧
        (∀ k, (f.ambientFactor d k).space =
          subspaceCommutator a.representation ⊤ (f.ambientFactor d k).actor) ∧
        (∀ k, let A := (f.ambientFactor d k).actor.comap (QuotientGroup.mk' (pCore 2 J))
          centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) J,
            ((pResidual 2 A).map A.subtype).map J.subtype⁆) ∧
        ∃ t : J, (t : G) ∈ (T : Subgroup G) ∧
          (f.ambientFactor d i).actor.map
            (MulAut.conj (QuotientGroup.mk' (pCore 2 J) t)).toMonoidHom =
              (f.ambientFactor d j).actor ∧
          (f.ambientFactor d j).actor.map
            (MulAut.conj (QuotientGroup.mk' (pCore 2 J) t)).toMonoidHom =
              (f.ambientFactor d i).actor ∧
          (f.ambientFactor d i).space.map (a.representation (QuotientGroup.mk' (pCore 2 J) t)) =
              (f.ambientFactor d j).space ∧
          QuotientGroup.mk' (pCore 2 J) t ∉ normalizer ((f.ambientFactor d i).actor : Set _) ∧
          ((f.ambientFactor d i).actor.comap (QuotientGroup.mk' (pCore 2 J))).map
            (MulAut.conj t).toMonoidHom =
              (f.ambientFactor d j).actor.comap (QuotientGroup.mk' (pCore 2 J)) ∧
          t ∉ normalizer (((f.ambientFactor d i).actor.comap
            (QuotientGroup.mk' (pCore 2 J))) : Set J) := by
  let := hs
  let : (ChapterD.Jhat a.representation).Normal := ChapterD.Jhat_normal a.representation
  obtain ⟨_,_,_,hcover,_,_⟩ := Section02.source_lemma_14_2_2_8_minimal
    hG T hempty hM hu hmany hcard e J hJ
  have hq : cubicRatio a.representation ≤ 2 := (cubicRatio_le_quadraticRatio _).trans
    (source_rankTwo_quadratic_bound_of_action hG T hempty hM hu hmany hcard e hab J hJ.1 a)
  obtain ⟨π,_hblocks,_hker,hperm⟩ := source_ratio_factor_permutation
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd
  have hp := fun g i => (hperm g i).2.1
  have hsp := fun g i => (hperm g i).2.2
  have ht := source_ratio_factor_transitive hG T hempty hM hu hmany hcard e hab J hJ hs a f d π hp
  obtain ⟨hc,p,m,hpm,hmark⟩ := f.transitive_uniform_dihedral d
    (pCore_quotient_pCore_eq_bot 2) hq hd hcover
    (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _) π hp ht hmore hsp
  have hmarked (k : d.Index) :
      Nonempty ((f.ambientFactor d k).actor ≃* DihedralGroup p) ∧
        Module.finrank (ZMod 2) (f.ambientFactor d k).space = 2*m := by
    obtain ⟨l,hl⟩ := hmark k
    let F := f.ambientFactor d k
    let eg : (d.factor k).Carrier ≃* F.actor := MonoidHom.ofInjective F.embedding.group_injective
    let ev : (d.factor k).Space ≃ₗ[ZMod 2] F.space :=
      LinearEquiv.ofInjective F.embedding.spaceMap F.embedding.space_injective
    exact ⟨⟨eg.symm.trans hl.dihedral.some⟩,ev.finrank_eq.symm.trans hl.dimension⟩
  obtain ⟨i,j,hij,hall,ha,hdis,hcom,hspace,hspaceDis⟩ := f.two_factor_moved_decomposition d hc
  let Q := (T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  obtain ⟨t,htmem,htij⟩ := f.transitive_pair_sylow d π hsp ht hc Q i j
  have htji : π t j = i := by
    rcases hall (π t j) with h | h
    · exact h
    · exact False.elim (hij ((π t).injective (htij.trans h.symm)))
  obtain ⟨b,hbT,hbt⟩ := htmem
  have hnotN : t ∉ normalizer ((f.ambientFactor d i).actor : Set _) := by
    intro hn
    have he := (mem_normalizer_iff_map_conj_eq.mp hn).symm.trans (hp t i)
    rw [htij] at he
    have hz : (f.ambientFactor d i).actor = ⊥ := disjoint_self.mp (he ▸ hdis)
    obtain ⟨x,hx⟩ := exists_ne (1 : (d.factor i).Carrier)
    have hh : (f.ambientFactor d i).embedding.groupMap x ∈ (f.ambientFactor d i).actor := ⟨x,rfl⟩
    rw [hz] at hh
    exact hx ((f.ambientFactor d i).embedding.group_injective
      (hh.trans (f.ambientFactor d i).embedding.groupMap.map_one.symm))

  refine ⟨hc,p,m,hpm,hmark,hmarked,i,j,hij,hall,ha,hdis,hcom,?_,hspaceDis,?_,?_,?_,b,hbT,?_,?_,?_,?_,?_,?_⟩
  · exact hspace.trans (source_rankTwo_whole_moved_eq_residual
      hG T hempty hM hu hmany hcard e hab J hJ.1 a).symm
  · rw [hspace]
    exact source_rankTwo_span_decomposition hG T hempty hM hu hmany hcard e hab J hJ.1 a
  · exact fun k => (f.ambientFactor d k).space_eq_support
  · intro k
    have he : (f.ambientFactor d k).actor =
        (d.factor k).actor.map (ChapterD.Jhat a.representation).subtype :=
      ChapterD.RatioDecomposition.Factor.map_actor (d.factor k) (f.embedding a.representation)
    dsimp only
    rw [he]
    exact source_ratio_factor_point hG T hempty hM hu hmany hcard e hab J hJ hs a f d k
  · rw [hbt,hp,htij]
  · rw [hbt,hp,htji]
  · rw [hbt,hsp,htij]
  · exact hbt ▸ hnotN
  · rw [pair_preimage_conj,hbt,hp,htij]
  · intro hn
    apply hnotN
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : (f.ambientFactor d i).actor.map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 J) b)).toMonoidHom =
          (f.ambientFactor d i).actor := by
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective (pCore 2 J))
      exact (pair_preimage_conj (QuotientGroup.mk' (pCore 2 J))
        (f.ambientFactor d i).actor b).symm.trans (mem_normalizer_iff_map_conj_eq.mp hn)
    exact hbt ▸ he

/-- The index-two subgroup here is the preimage of the factor-permutation
kernel. Identifying it with the actor-join preimage is a separate source step. -/
theorem source_ratio_nonsingleton_index_two_preimage
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
      (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) := by
  obtain ⟨π,_hblocks,hker,hperm⟩ := f.source_Jhat_partition_action rfl d
    (source_ratio_factor_starred_sylow hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd)
  have hp := fun g i => (hperm g i).2.1
  have ht := source_ratio_factor_transitive hG T hempty hM hu hmany hcard e hab J hJ hs a f d π hp
  have hb := (source_ratio_factor_count hG T hempty hM hu hmany hcard e hab J hJ hs a f d π hp).1
  have hc : Nat.card d.Index = 2 := by omega
  refine ⟨π,hker,?_,hp,ht⟩
  exact (π.ker.index_comap_of_surjective (QuotientGroup.mk'_surjective (pCore 2 J))).trans
    (pair_kernel_index π hc ht)

end CFSG.Quasithin.Chapter14.Section06
