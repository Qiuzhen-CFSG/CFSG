module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.ComponentActorNormalizer
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.OuterOrders

/-!
# The two literal pairs in the original quintic plane

The original dihedral rotations and the actual component intersections
both give pairs of order-five subgroups permuted by the same original
quotient. The component pair is obtained from the strict closure; the
rotation pair retains the original factor indices and conjugation action.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
open OddNormalizer.Quintic.ModuleGeometry (ExchangedFactorData)
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem actorImage_intersection {J : Subgroup G} (K : Subgroup G) :
    actorImage J (K ⊓ J) = actorImage J K := by
  unfold actorImage
  congr 1
  ext x
  exact and_iff_left x.property

omit [Finite G] in
private theorem actorImage_conjugate_any {J : Subgroup G} (K : Subgroup G) (h : J) :
    actorImage J (K.map (MulAut.conj (h : G)).toMonoidHom) =
      (actorImage J K).map (MulAut.conj (QuotientGroup.mk' (pCore 2 J) h)).toMonoidHom := by
  have hh := actorImage_conjugate (K ⊓ J) inf_le_right h
  have hH : J.map (MulAut.conj (h : G)).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (J.le_normalizer h.property)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (h : G)).injective,hH,
    actorImage_intersection,actorImage_intersection] at hh
  exact hh

omit [Finite G] in
private theorem component_pair_preserved (T : Sylow 2 G) {J Mc : Subgroup G}
    (hTJ : (T : Subgroup G) ≤ J) (hJM : J ≤ Mc)
    (b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T))
    (x : J ⧸ pCore 2 J) :
    (actorImage J b.K1).map (MulAut.conj x).toMonoidHom = actorImage J b.K1 ∨
      (actorImage J b.K1).map (MulAut.conj x).toMonoidHom = actorImage J b.K2 := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 J) x
  rw [←actorImage_conjugate_any b.K1 x]
  by_cases hn : (x : G) ∈ normalizer (b.K1 : Set G)
  · exact Or.inl (congrArg (actorImage J) (mem_normalizer_iff_map_conj_eq.mp hn))
  · right
    obtain ⟨t,ht,htn,he⟩ := b.exchanged
    have hx : (x : G)⁻¹ ∉ J ⊓ normalizer (b.K1 : Set G) := by
      intro hx
      exact hn (inv_mem_iff.mp hx.2)
    have hex := map_conj_eq_of_outside_normalizer J Mc
      (Mc ⊓ normalizer (b.K1 : Set G)) b.K1 b.K2 hJM
      b.first_le b.first_index inf_le_right t (hTJ ht) htn he
      x⁻¹ x⁻¹.property hx
    have he' : b.K1.map (MulAut.conj (x : G)).toMonoidHom = b.K2 := by
      simpa only [inv_inv] using hex
    exact congrArg (actorImage J) he'

private theorem dihedral_residual_card {K : Type*} [Group K] [Finite K]
    (A : Subgroup K) (e : A ≃* DihedralGroup 5) : Nat.card (residual A) = 5 := by
  change Nat.card ((pResidual 2 A).map A.subtype) = 5
  rw [card_map_of_injective A.subtype_injective]
  apply card_twoResidual_of_card_twice_odd_prime (by decide : Odd 5)
  rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]

omit [Finite G] in
private theorem pair_perm_eq_one {I : Type*} (σ : Equiv.Perm I) {i j : I}
    (hij : i ≠ j) (hall : ∀ k, k = i ∨ k = j) (hi : σ i = i) : σ = 1 := by
  apply Equiv.ext
  intro k
  rcases hall k with rfl | rfl
  · exact hi
  · rcases hall (σ j) with hj | hj
    · exact (hij ((σ.injective (hj.trans hi.symm)).symm)).elim
    · exact hj

private theorem rotation_normalizer_kernel {K I : Type*} [Group K] [Finite K]
    (π : K →* Equiv.Perm I) (A : I → Subgroup K) {i j : I}
    (hij : i ≠ j) (hall : ∀ k, k = i ∨ k = j)
    (hR : residual (A i) ≠ residual (A j))
    (hp : ∀ x k, (A k).map (MulAut.conj x).toMonoidHom = A (π x k)) (x : K) :
    x ∈ normalizer (residual (A i) : Set K) ↔ x ∈ π.ker := by
  have he : (residual (A i)).map (MulAut.conj x).toMonoidHom = residual (A (π x i)) := by
    change ((pResidual 2 (A i)).map (A i).subtype).map (MulAut.conj x).toMonoidHom = _
    rw [map_embedded_pResidual,hp]
    rfl
  constructor
  · intro hx
    have hr := (mem_normalizer_iff_map_conj_eq.mp hx).symm.trans he
    change π x = 1
    apply pair_perm_eq_one (π x) hij hall
    rcases hall (π x i) with hi | hj
    · exact hi
    · rw [hj] at hr
      exact (hR hr).elim
  · intro hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    simpa only [show π x = 1 from hx,Equiv.Perm.one_apply] using he

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs w

/-- Both actual pairs are preserved by conjugation in the original quotient.
The rotation pair retains the two original dihedral factor indices. -/
theorem source_quintic_strict_invariant_pairs
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T),
      ∃ i j : d.Index, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
        Nat.card (residual (f.ambientFactor d i).actor) = 5 ∧
        Nat.card (residual (f.ambientFactor d j).actor) = 5 ∧
        Disjoint (residual (f.ambientFactor d i).actor) (residual (f.ambientFactor d j).actor) ∧
        Nat.card (actorImage J b.K1) = 5 ∧ Nat.card (actorImage J b.K2) = 5 ∧
        Disjoint (actorImage J b.K1) (actorImage J b.K2) ∧
        actorImage J b.K1 ⊔ actorImage J b.K2 = pResidual 2 (J ⧸ pCore 2 J) ∧
        (∀ x : J ⧸ pCore 2 J,
          (residual (f.ambientFactor d i).actor).map (MulAut.conj x).toMonoidHom =
              residual (f.ambientFactor d i).actor ∨
          (residual (f.ambientFactor d i).actor).map (MulAut.conj x).toMonoidHom =
              residual (f.ambientFactor d j).actor) ∧
        (∀ x : J ⧸ pCore 2 J,
          (actorImage J b.K1).map (MulAut.conj x).toMonoidHom = actorImage J b.K1 ∨
          (actorImage J b.K1).map (MulAut.conj x).toMonoidHom = actorImage J b.K2) ∧
        (∀ x : J, (x : G) ∈ normalizer (b.K1 : Set G) ↔
          QuotientGroup.mk' (pCore 2 J) x ∈
            normalizer (actorImage J b.K1 : Set (J ⧸ pCore 2 J))) := by
  obtain ⟨b,hC,hD,hdis,hjoin,hN,_hN1,_hN2⟩ := source_quintic_strict_component_normalizers
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hne
  obtain ⟨i,j,hij,hall,_hjoin,hd,_hc,_⟩ := f.two_factor_moved_decomposition d w.two_factors
  have hJM : J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  refine ⟨b,i,j,hij,hall,dihedral_residual_card _ (w.dihedral i).some,
    dihedral_residual_card _ (w.dihedral j).some,
    hd.mono (residual_le _) (residual_le _),hC,hD,hdis,hjoin,?_,
    component_pair_preserved T hJ.1.1.2 hJM b,hN⟩
  intro x
  have he : (residual (f.ambientFactor d i).actor).map (MulAut.conj x).toMonoidHom =
      residual (f.ambientFactor d (π x i)).actor := by
    change ((pResidual 2 (f.ambientFactor d i).actor).map
      (f.ambientFactor d i).actor.subtype).map (MulAut.conj x).toMonoidHom = _
    rw [map_embedded_pResidual,hp]
    rfl
  rcases hall (π x i) with hi | hj
  · rw [hi] at he
    exact Or.inl he
  · rw [hj] at he
    exact Or.inr he

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
