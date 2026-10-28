module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductMarkedThompson
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
public import Theory.SpecificGroups.Alternating.BorelCommutatorOrders

/-!
# The literal terminal product and its full Thompson image

A transposition on the four-letter support of the selected point lies in
the original Sylow Thompson image and fixes the complementary three letters.
Its action on the prescribed A₅ component is odd. Indeed, an even actor
normalizes the A₄ Borel and has commutators of two-power order there; the
support transposition produces a nonidentity cubic commutator through the
same first local factor, which is impossible.

This independent actor completes the marked S₅ × S₃ Thompson image.
`productAnalysis` now constructs every field of the published interface,
using the previously proved cubic Sylow, central-cover, local-factor and
seed calculations. `false_of_component_analysis` applies the actual B.5.6
module decomposition and terminal contradiction.

Only ComponentAnalysis and the permitted earlier source inputs remain
explicit. Its producer and the final source-theorem assembly belong to
qt-d-1231-terminal; there is no remaining product or local actor premise.
Source: Aschbacher--Smith, 12.3.13 and completion of 12.3.1, pp.811--812.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

private theorem weightFour_support_swap (w : EvenWord) (hw : weight w.val = 4)
    (Q : Sylow 2 (Equiv.Perm (Fin 7)))
    (hQC : (Q : Subgroup (Equiv.Perm (Fin 7))) ≤ WeightTwoGeometry.symmetricStabilizer w) :
    ∃ i j : WeightFourLocal.Support w, i ≠ j ∧ Equiv.swap i.val j.val ∈ Q := by
  have hn : Nontrivial (WeightFourLocal.Support w) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_eq_fintype_card,WeightFourLocal.support_card w hw]; decide)
  obtain ⟨i,j,hij⟩ := exists_pair_ne (WeightFourLocal.Support w)
  have ht : Equiv.swap i.val j.val ∈ WeightTwoGeometry.symmetricStabilizer w := by
    rw [WeightTwoGeometry.mem_symmetricStabilizer]
    apply Subtype.ext
    funext k
    change w.val ((Equiv.swap i.val j.val).symm k) = w.val k
    have hi : w.val i.val = 1 := by
      have h := i.property
      simp only [WeightTwoGeometry.support,Finset.mem_filter,
        Finset.mem_univ,true_and] at h
      exact (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ h
    have hj : w.val j.val = 1 := by
      have h := j.property
      simp only [WeightTwoGeometry.support,Finset.mem_filter,
        Finset.mem_univ,true_and] at h
      exact (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ h
    simp only [Equiv.symm_swap,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  let t : WeightTwoGeometry.symmetricStabilizer w := ⟨Equiv.swap i.val j.val,ht⟩
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by change (Equiv.swap i.val j.val)^2 = 1; simp [pow_two]))
  obtain ⟨R,hR⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (WeightTwoGeometry.symmetricStabilizer w) R (Q.subtype hQC)
  have htR : g * t * g⁻¹ ∈ Q.subtype hQC := by
    rw [←hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hR (mem_zpowers t))
  let a := WeightFourLocal.supportPermutation w g i
  let b := WeightFourLocal.supportPermutation w g j
  refine ⟨a,b,(WeightFourLocal.supportPermutation w g).injective.ne hij,?_⟩
  have he : Equiv.swap a.val b.val = g.val * t.val * g.val⁻¹ :=
    Equiv.swap_apply_apply g.val i.val j.val
  rw [he]
  exact htR

/-- A support transposition in the original Thompson image, with trivial
complementary action. -/
theorem exists_thompson_first_swap
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    ∃ j : P.pointNormalizer, (j : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) ∧
      (P.pointBlockAction j).1.IsSwap ∧ (P.pointBlockAction j).2 = 1 := by
  let N := normalizer (V : Set G)
  let hTV := ((structural G T L S.hypothesis).2.2 V S.chosen).1
  let R := T.subtype hTV
  let Q := R.mapSurjective (MonoidHom.range_eq_top.mp (D.permutation_range_eq_top structural escape))
  have hQC : (Q : Subgroup (Equiv.Perm (Fin 7))) ≤
      WeightTwoGeometry.symmetricStabilizer (D.model.coordinates P.point).toAdd := by
    rintro g ⟨t,ht,rfl⟩
    exact (D.model.pointPermutation P.point ⟨t,P.sylow_le_pointNormalizer structural ht⟩).property
  obtain ⟨i,k,hik,hikQ⟩ := weightFour_support_swap (D.model.coordinates P.point).toAdd
    P.weight_four Q hQC
  have hik' : i.val ≠ k.val := fun h => hik (Subtype.ext h)
  obtain ⟨j,hj,hjπ⟩ := D.swap_mem_thompson_image structural escape
    (show (Equiv.swap i.val k.val).IsSwap from ⟨i.val,k.val,hik',rfl⟩) hikQ
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) := sSup_le fun _ h => h.1
  let jP : P.pointNormalizer := ⟨j,P.sylow_le_pointNormalizer structural (hJT hj)⟩
  let e := WeightFourLocal.fourLetters _ P.weight_four
  have hsupport : WeightFourLocal.supportPermutation (D.model.coordinates P.point).toAdd
      (D.model.pointPermutation P.point jP) = Equiv.swap i k := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    change D.model.permutation j b.val = (Equiv.swap i k b).val
    rw [hjπ]
    by_cases hi : b = i
    · subst b; simp
    by_cases hk : b = k
    · subst b; simp
    rw [Equiv.swap_apply_of_ne_of_ne (fun h => hi (Subtype.ext h))
      (fun h => hk (Subtype.ext h)),Equiv.swap_apply_of_ne_of_ne hi hk]
  have hfirst : (P.pointBlockAction jP).1 = Equiv.swap (e i) (e k) := by
    apply Equiv.ext
    intro a
    obtain ⟨b,rfl⟩ := e.surjective a
    rw [P.pointBlockAction_first,hsupport]
    exact e.injective.map_swap i k b
  refine ⟨jP,hj,?_,?_⟩
  · exact ⟨e i,e k,e.injective.ne hik,hfirst⟩
  · apply Equiv.ext
    intro a
    obtain ⟨b,rfl⟩ := (WeightFourLocal.threeLetters _ P.weight_four).surjective a
    rw [P.pointBlockAction_second]
    change WeightFourLocal.threeLetters _ P.weight_four _ =
      WeightFourLocal.threeLetters _ P.weight_four b
    congr 1
    apply Subtype.ext
    change D.model.permutation j b.val = b.val
    rw [hjπ,Equiv.swap_apply_of_ne_of_ne]
    · intro h
      exact (Finset.mem_compl.mp b.property) (h ▸ i.property)
    · intro h
      exact (Finset.mem_compl.mp b.property) (h ▸ k.property)

/-- Odd support action is odd on the original A₅ component. An even component
actor normalizes its A₄ Borel and has only two-power commutators there,
contradicting the cubic commutator of an odd support permutation. -/
theorem componentPermutation_odd_of_first_odd
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (j : P.pointNormalizer) (hj : (P.pointBlockAction j).1 ∉ alternatingGroup (Fin 4)) :
    P.componentPermutation C ⟨j,C.normalizes j.property.2⟩ ∉ alternatingGroup (Fin 5) := by
  let NK := normalizer (P.K : Set G)
  let X := P.K ⊓ normalizer (L : Set G)
  let XN := X.subgroupOf NK
  let f := P.componentPermutation C
  let jN : NK := ⟨j,C.normalizes j.property.2⟩
  obtain ⟨R,hR⟩ := P.exists_component_sylow
  let R' := R.mapSurjective (P.componentProjection_surjective C)
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R'
  have hB : ((normalizer (L : Set G)).subgroupOf P.K).map (P.componentProjection C) =
      MulAction.stabilizer (alternatingGroup (Fin 5)) i :=
    (P.component_intersection_image_eq_borel structural C R hR).trans hi
  have himage : XN.map f = (alternatingGroup (Fin 5)) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 5)) i := by
    apply le_antisymm
    · rintro a ⟨n,hn,rfl⟩
      have he : f n = (P.componentProjection C ⟨n,hn.1⟩).val :=
        P.componentPermutation_on_component C ⟨n,hn.1⟩
      rw [he]
      exact ⟨(P.componentProjection C ⟨n,hn.1⟩).property,
        hB.le (mem_map_of_mem (P.componentProjection C) hn.2)⟩
    · intro a ha
      have ham : (⟨a,ha.1⟩ : alternatingGroup (Fin 5)) ∈
          ((normalizer (L : Set G)).subgroupOf P.K).map (P.componentProjection C) :=
        hB.symm ▸ ha.2
      obtain ⟨k,hk,he⟩ := ham
      exact ⟨⟨k,P.K.le_normalizer k.property⟩,⟨k.property,hk⟩,
        (P.componentPermutation_on_component C k).trans (congrArg Subtype.val he)⟩
  have hjN : jN ∈ normalizer (XN : Set NK) := by
    rw [mem_normalizer_iff]
    intro k
    exact (mem_normalizer_iff.mp (P.component_intersection_normalized structural C j.property)) k.val
  have hfix : f jN i = i := by
    have hh := XN.le_normalizer_map f (mem_map_of_mem f hjN)
    rw [himage,Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.even_stabilizer_normalizer] at hh
    exact hh
  intro heven
  obtain ⟨a,hacube,hane⟩ := Theory.SpecificGroups.Alternating.four_odd_cubic_witness _ hj
  obtain ⟨r,hr⟩ := P.firstResidualProjection_surjective structural escape a
  have hrK : (r : G) ∈ P.K := by
    apply P.L1_le_component structural escape C
    rw [←P.firstPointResidual_eq_L1 structural escape C]
    exact r.property
  let rK : P.K := ⟨r,hrK⟩
  let rP := inclusion P.firstPointResidual_le_pointNormalizer r
  let rN : NK := ⟨r,P.K.le_normalizer hrK⟩
  let cP : P.pointNormalizer := ⁅rP,j⁆
  have hcK : (cP : G) ∈ P.K := by
    have hc := (le_normalizer_iff_commutator_le_left.mp
      (show P.pointNormalizer ≤ normalizer (P.K : Set G) from inf_le_right.trans C.normalizes))
      (commutator_mem_commutator hrK j.property)
    exact hc
  let cK : P.K := ⟨cP,hcK⟩
  have hrM : (rK : G) ∈ normalizer (L : Set G) :=
    P.pointNormalizer_le_original structural rP.property
  have hrfix : (P.componentProjection C rK).val i = i :=
    hB.le (mem_map_of_mem (P.componentProjection C) hrM)
  have hcsq : (P.componentProjection C cK)^2 = 1 := by
    apply Subtype.ext
    have he : (P.componentProjection C cK).val = ⁅(P.componentProjection C rK).val,f jN⁆ := by
      rw [←P.componentPermutation_on_component C cK]
      change f ⁅rN,jN⁆ = _
      rw [map_commutatorElement,P.componentPermutation_on_component C rK]
    change ((P.componentProjection C cK).val)^2 = 1
    rw [he]
    exact congrArg Subtype.val (Theory.SpecificGroups.Alternating.five_borel_commutator_sq
      i (P.componentProjection C rK) ⟨f jN,heven⟩ hrfix hfix)
  have hcore : cK^2 ∈ pCore 2 P.K := by
    rw [←P.componentProjection_ker C]
    change P.componentProjection C (cK^2) = 1
    rw [map_pow,hcsq]
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := P.K)) ⟨cK^2,hcore⟩
  have hcpow : cP ^ (2^(n+1)) = 1 := by
    apply Subtype.ext
    change (cP : G) ^ (2^(n+1)) = 1
    have hh := congrArg (fun x : pCore 2 P.K => ((x : P.K) : G)) hn
    change (((cP : G)^2)^(2^n)) = 1 at hh
    simpa only [←pow_mul,←pow_succ'] using hh
  let q := (MonoidHom.fst _ _).comp P.pointBlockAction
  have hq : q cP = ⁅a.val,(P.pointBlockAction j).1⁆ := by
    change q ⁅rP,j⁆ = _
    rw [map_commutatorElement]
    exact congrArg (fun b => ⁅b,(P.pointBlockAction j).1⁆) (congrArg Subtype.val hr)
  have hp : (⁅a.val,(P.pointBlockAction j).1⁆)^(2^(n+1)) = 1 := by
    rw [←hq,←map_pow,hcpow,map_one]
  apply hane
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 3 2).pow_right (n+1))
    (orderOf_dvd_of_pow_eq_one hacube) (orderOf_dvd_of_pow_eq_one hp))

/-- The independent odd component actor required by the marked product comes
from a support transposition in the actual Sylow Thompson image. -/
theorem exists_independent_thompson_actor
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ∃ t : P.Y, (t : G) ∈ elementaryAbelianMaxJ P.Y ∧
      P.firstYAction C t ∉ alternatingGroup (Fin 5) ∧
      P.secondYAction structural escape C t = 1 := by
  obtain ⟨j,hj,hs,hsecond⟩ := P.exists_thompson_first_swap structural escape
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) := sSup_le fun _ h => h.1
  let t : P.Y := ⟨j,P.sylow_le_Y (hJT hj)⟩
  refine ⟨t,P.sylow_thompson_le_Y_thompson hj,?_,?_⟩
  · apply P.componentPermutation_odd_of_first_odd structural escape C j
    intro he
    have h := Equiv.Perm.mem_alternatingGroup.mp he
    rw [hs.sign_eq] at h
    exact (by decide : (-1 : ℤˣ) ≠ 1) h
  · exact (P.secondYAction_agrees structural escape C t j.property).trans hsecond

/-- The full marked Thompson image, with no remaining local actor premise. -/
theorem markedThompson_surjective
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    Function.Surjective ((P.markedProductAction structural escape C).comp
      ((elementaryAbelianMaxJ P.Y).subgroupOf P.Y).subtype) := by
  obtain ⟨t,ht,hfirst,hsecond⟩ := P.exists_independent_thompson_actor structural escape C
  exact P.markedThompson_surjective_of_independent_actor structural escape C t ht hfirst hsecond

/-- Construct every literal terminal product and module-seed requirement from
the normal A₅ component. Its source producer remains with qt-d-1231-terminal. -/
theorem productAnalysis
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : Nonempty P.ProductAnalysis :=
  P.productAnalysis_of_markedThompson_surjective structural escape C
    (P.markedThompson_surjective structural escape C)

/-- Actual B.5.6 application and terminal contradiction, conditional only on
the earlier normal A₅ component and the permitted source inputs. -/
theorem false_of_component_analysis
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : False := by
  obtain ⟨A⟩ := P.productAnalysis structural escape C
  exact P.false_of_module_analysis structural A

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
