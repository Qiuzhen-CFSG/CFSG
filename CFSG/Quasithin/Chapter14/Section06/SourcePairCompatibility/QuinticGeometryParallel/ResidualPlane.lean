module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.Support
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Primitive
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Fitting

/-!
# The actual primitive quintic residual plane

The two literal residual actor images commute, intersect trivially and each
have order five. Their join is the entire residual of J/O₂(J), so that
residual has order twenty-five without using an index of the actor join.
The original minimal-normal residual theorem identifies its prime as five.
Transport through the actual quotient then supplies the original Ξ input,
with the same Sylow action and intrinsic core/Frattini conventions.

Source: Aschbacher--Smith 14.6.12 and the application of 1.3.4 in 14.6.14,
printed pp.1031,1033.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
namespace SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]

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
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs w

/-- The actual starred residual has order twenty-five, independently of
the index of Jhat in the full quotient. -/
theorem source_quintic_residual_plane_card :
    Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 25 := by
  obtain ⟨i,j,hij,_hall,_hjoin,hdis,hcom,_⟩ :=
    f.two_factor_moved_decomposition d w.two_factors
  let H1 := actorPreimage J (f.ambientFactor d i).actor
  let H2 := actorPreimage J (f.ambientFactor d j).actor
  let A := actorImage J (residual H1)
  let B := actorImage J (residual H2)
  have h1 : residual H1 ≤ J := (residual_le _).trans (actorPreimage_le J _)
  have h2 : residual H2 ≤ J := (residual_le _).trans (actorPreimage_le J _)
  have hA : A ≤ (f.ambientFactor d i).actor := by
    rw [←actorImage_actorPreimage J (f.ambientFactor d i).actor]
    exact map_mono (subgroupOf_mono J (residual_le H1))
  have hB : B ≤ (f.ambientFactor d j).actor := by
    rw [←actorImage_actorPreimage J (f.ambientFactor d j).actor]
    exact map_mono (subgroupOf_mono J (residual_le H2))
  have hn : B ≤ normalizer (A : Set _) := by
    apply le_normalizer_iff.mpr
    intro y hy x hx
    rw [(hcom x (hA hx) y (hB hy)).symm.eq,mul_inv_cancel_right]
    exact hx
  have hj : A ⊔ B = pResidual 2 (J ⧸ pCore 2 J) := by
    have hjoin : residual H1 ⊔ residual H2 = residual J :=
      source_quintic_residual_join_of_ne hG T hempty hM hu hmany hcard e hab
        J hJ hs a f d π w i j hij
    have hmap : A ⊔ B = actorImage J (residual J) := by
      rw [←hjoin]
      unfold actorImage
      rw [subgroupOf_sup h1 h2,Subgroup.map_sup]
      rfl
    rw [hmap]
    unfold actorImage GenerationOne.residual subgroupOf
    rw [comap_map_eq_self_of_injective J.subtype_injective,
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  rw [←hj,card_sup_eq_mul_of_normalizes_of_disjoint A B hn (hdis.mono hA hB)]
  rw [show Nat.card A = 5 from source_quintic_residual_actor_card T J a f d π w i,
    show Nat.card B = 5 from source_quintic_residual_actor_card T J a f d π w j]

/-- The original minimal residual is elementary abelian at the actual
prime five; this is derived from the factor action, not an added premise. -/
theorem source_quintic_primitive_residual : OddNormalizer.PrimitiveResidual J 5 := by
  obtain ⟨p,hp,hE,_hr,_hne,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  rcases hp with rfl | rfl
  · let := hE
    have hc := source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := pResidual 2 (J ⧸ pCore 2 J))
      5 (by rw [hc]; decide)
    have hcop := (IsElementaryAbelian.isPGroup 3 (pResidual 2 (J ⧸ pCore 2 J))).orderOf_coprime
      (by decide : Nat.Coprime 3 5) x
    rw [hx] at hcop
    norm_num at hcop
  · exact ⟨hE,hmin⟩

/-- The original residual belongs to Ξ with the literal Sylow action.
This discharges the primitive-plane input to the source 1.3.4 application. -/
theorem source_quintic_residual_mem_Xi :
    residual J ∈ Chapter1.Xi G (T : Subgroup G) := by
  apply residual_mem_Xi T J hJ.1.1.2 hJ.1.1.1 (by decide : Odd 5)
    (source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w)
  exact source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w

/-- Apply the source Ξ embedding to the same Mc. The full residual closure
lies in its generalized-Fitting preimage without an actor-join index. -/
theorem source_quintic_residualClosure_le_fittingPreimage :
    residualClosure J Mc ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc := by
  have hXi := source_quintic_residual_mem_Xi hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  have hF := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  have hJMc : J ≤ Mc := hF.H_centralizes.trans (InitialSource.centralizer_le_partner T hu)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu.symm ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := hJ.1.1.2.trans hJMc
  have hSylow : Chapter1.IsSylowIn 2 (T : Subgroup G) Mc := by
    refine ⟨T.subtype hTMc,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]
  obtain ⟨q,hq,hoq,hQ⟩ := hXi.odd_quotient
  let : Fact q.Prime := ⟨hq⟩
  let P : Sylow q (residual J) := default
  have hi := Chapter1.XiEmbedding.localInput_of_mem_Xi hXi hSylow
    (sup_le ((residual_le J).trans hJMc) hTMc) hoq hQ P
  exact localInput_closure_le_fittingPreimage hi (hG.twoLocal_sqtk hMc.1.1) hSylow

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
