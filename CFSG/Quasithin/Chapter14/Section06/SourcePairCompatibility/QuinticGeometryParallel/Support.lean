module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.CoreGeometry
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.PrimeOrderCentralizerEscape

/-!
# Opposite residuals at a noncentral point of a quintic support

The literal disjoint factor supports centralize the opposite residual after
two-layer centralization removes the error in Z. The cyclic-five first actor
has no nonzero fixed vector on its support. Hence a quintic element of O²(J)
fixing a noncentral point of that support lies in the other factor residual.
No equality of Jhat with the factor-permutation kernel or index of Jhat is used.

Source: Aschbacher--Smith 14.6.15, printed p.1034.
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
include hG hempty hM hu hmany hcard e hab hJ hs hp w

omit [Finite G] hG hempty hM hu hmany hcard e hab hJ hs hp w in
private theorem ambient_actors_commute (i j : d.Index) (hij : i ≠ j) :
    ∀ x ∈ (f.ambientFactor d i).actor, ∀ y ∈ (f.ambientFactor d j).actor, Commute x y := by
  intro x hx y hy
  simp only [ChapterD.RatioDecomposition.FactorData.ambientFactor,
    ChapterD.RatioDecomposition.Factor.map_actor,
    ChapterD.RatioDecomposition.FactorData.embedding] at hx hy
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  exact congrArg (ChapterD.Jhat a.representation).subtype (d.actors_commute f.faithful hij hx hy).eq

omit hs hp w in
/-- Distinct literal support preimages ordinarily centralize the opposite
residual; the central-line error is removed using its two-perfectness. -/
theorem source_quintic_support_centralizes_residual (i j : d.Index) (hij : i ≠ j) :
    firstSupport a (actorPreimage J (f.ambientFactor d i).actor) ≤ centralizer
      (residual (actorPreimage J (f.ambientFactor d j).actor) : Set G) := by
  let A := (f.ambientFactor d i).actor
  let B := (f.ambientFactor d j).actor
  let H2 := actorPreimage J B
  let W1 := subspaceCommutator a.representation ⊤ A
  let W2 := subspaceCommutator a.representation ⊤ B
  have hcom := ambient_actors_commute T J a f d i j hij
  have hnA : B ≤ normalizer (A : Set _) := by
    apply le_normalizer_iff.mpr
    intro y hy x hx
    rw [(hcom x hx y hy).symm.eq,mul_inv_cancel_right]
    exact hx
  have hn : B ≤ subspaceStabilizer a.representation W1 :=
    subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial)) hnA
  have hdis : Disjoint W1 W2 := by
    dsimp only [W1,W2,A,B]
    rw [←(f.ambientFactor d i).space_eq_support,←(f.ambientFactor d j).space_eq_support]
    exact (f.ambient_spaces_independent d).pairwiseDisjoint hij
  have hf : W1 ≤ fixedSpace a.representation B := by
    intro v hv b
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hdis
    · exact W1.sub_mem ((hn b.property v).mpr hv) hv
    · exact Submodule.subset_span ⟨b,b.property,v,Submodule.mem_top,rfl⟩
  have herr : ⁅H2,firstSupport a (actorPreimage J A)⁆ ≤ centralInvolutions T := by
    rw [commutator_le]
    intro b hb u hu
    have huU := supportPreimage_le a W1 (by
      simpa only [firstSupport,actorImage_actorPreimage] using hu)
    let bJ : J := ⟨b,actorPreimage_le J B hb⟩
    have hbq : QuotientGroup.mk' (pCore 2 J) bJ ∈ B := by
      have hh : QuotientGroup.mk' (pCore 2 J) bJ ∈ actorImage J H2 := mem_map_of_mem _ hb
      simpa only [H2,actorImage_actorPreimage] using hh
    have huW : u ∈ supportPreimage a W1 := by
      simpa only [firstSupport,actorImage_actorPreimage] using hu
    have hh := hf ((mem_supportPreimage a W1 ⟨u,huU⟩).mp huW)
      ⟨QuotientGroup.mk' (pCore 2 J) bJ,hbq⟩
    change a.representation (QuotientGroup.mk' (pCore 2 J) bJ)
      (Additive.ofMul (QuotientGroup.mk' ((centralInvolutions T).subgroupOf
        (conjugateSpanBy (localModule T M) J)) ⟨u,huU⟩)) = _ at hh
    rw [a.conjugation] at hh
    have hc := QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul hh)
    change b*u*b⁻¹/u ∈ centralInvolutions T at hc
    simpa only [div_eq_mul_inv,commutatorElement_def] using hc
  have hHZ : H2 ≤ centralizer (centralInvolutions T : Set G) :=
    (actorPreimage_le J B).trans
      (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes
  exact le_centralizer_iff.mp (residual_centralizes_of_two_layer H2 _ _
    ((IsElementaryAbelian.isPGroup 2 (conjugateSpanBy (localModule T M) J)).to_le a.kernel_le)
    hHZ herr)

omit hp in
/-- The original residual join in any ordering of the two actual labels. -/
theorem source_quintic_residual_join_of_ne (i j : d.Index) (hij : i ≠ j) :
    residual (actorPreimage J (f.ambientFactor d i).actor) ⊔
      residual (actorPreimage J (f.ambientFactor d j).actor) = residual J := by
  obtain ⟨k,l,_,hall,hjoin⟩ := source_quintic_residual_join hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  rcases hall i with rfl | rfl <;> rcases hall j with rfl | rfl
  · exact (hij rfl).elim
  · exact hjoin
  · exact (sup_comm _ _).trans hjoin
  · exact (hij rfl).elim

omit hG hempty hM hu hmany hcard e hab hJ hs hp in
/-- Each actual factor residual is generated by ambient elements of order five. -/
theorem source_quintic_residual_generated (k : d.Index) :
    closure {x : G | x ∈ residual (actorPreimage J (f.ambientFactor d k).actor) ∧ orderOf x = 5} =
      residual (actorPreimage J (f.ambientFactor d k).actor) := by
  let Hk := actorPreimage J (f.ambientFactor d k).actor
  let R := residual Hk
  have hc : Nat.card (R ⧸ pCore 2 R) = 5 :=
    (Nat.card_congr (source_quintic_factor_residual_model T J a f d π w k).some.toEquiv).trans (by simp)
  have h := closure_prime_order_eq_top_of_isPPerfect
    (isPPerfect_embedded_pResidual 2 Hk) (by decide : Nat.Coprime 2 5) hc
  apply le_antisymm ((closure_le _).mpr (fun _ hx => hx.1))
  intro x hx
  have hle : closure {y : R | orderOf y = 5} ≤
      (closure {y : G | y ∈ R ∧ orderOf y = 5}).comap R.subtype := by
    apply (closure_le _).mpr
    intro y hy
    exact subset_closure ⟨y.property,(Subgroup.orderOf_coe y).trans hy⟩
  exact hle (h.ge (mem_top (⟨x,hx⟩ : R)))

omit hG hempty hM hu hmany hcard e hab hJ hs hp in
/-- The residual of a literal actor preimage acts through a cyclic five-group. -/
theorem source_quintic_residual_actor_card (k : d.Index) :
    Nat.card (actorImage J (residual (actorPreimage J (f.ambientFactor d k).actor))) = 5 := by
  let B := actorPreimage J (f.ambientFactor d k).actor
  have hB : B ≤ J := actorPreimage_le J _
  have he : (residual B).subgroupOf J =
      (pResidual 2 (B.subgroupOf J)).map (B.subgroupOf J).subtype := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le ((residual_le B).trans hB),map_embedded_pResidual,
      map_subgroupOf_eq_of_le hB]
    rfl
  change Nat.card (actorImage J (residual B)) = 5
  unfold actorImage
  rw [he,map_embedded_pResidual,card_map_of_injective]
  · apply card_twoResidual_of_card_twice_odd_prime (by decide : Odd 5)
    change Nat.card (actorImage J B) = 2*5
    rw [show actorImage J B = (f.ambientFactor d k).actor from actorImage_actorPreimage J _,
      Nat.card_congr (w.dihedral k).some.toEquiv,DihedralGroup.nat_card]
  · exact Subgroup.subtype_injective _

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
