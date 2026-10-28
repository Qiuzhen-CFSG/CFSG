module
public import Theory.Representation.PSL3Two.PairedNaturalDual.Permutation
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.ActorEstimates
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Centralization

/-!
# Paired component actors on the original terminal quotient

The two natural--dual support markings exclude FF offenders on the actual
U/Z and supply the no-transvection hypothesis for critical-endpoint selection.
The selected actor normalizes both components. Its literal component images
satisfy the rank and displacement estimates used in 14.6.24(c)--(i).

After placing the critical point in the first support, relative component
centralization kills the second automorphism action. Joint faithfulness then
identifies the full actor rank with the first image, bounds it by two, and
the original quadratic budget forces this image to consist of inner actors.
The embedding of the second component is the actual star image, with its
conjugation covariance retained.

The support markings are the earlier-source inputs of
qt-e-suitable-component-supports. The mixed-support point placement, component
alignment and Sylow contradiction remain with qt-e-suitable-component-marking;
none is asserted by this conditional actor family. Final suitable-choice
assembly remains with qt-e-suitable-existence.
Source: Aschbacher--Smith 14.6.22--24, printed pp.1038--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Every selected quadratic endpoint preserves the two marked supports.
The group is the literal common stabilizer in the original star quotient. -/
theorem QuadraticEndpoint.le_pair_stabilizer
    {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (p : QuadraticEndpoint h ρ) (_hb : 3 ≤ h.b)
    (s : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (N : Subgroup (Source.Hstar D.H)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : Source.Hstar D.H,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range)) :
    Source.starImage D.H (p.endpoint.conjugate D.UH) ≤ N := by
  let A := Source.starImage D.H (p.endpoint.conjugate D.UH)
  let : IsElementaryAbelian 2 A := p.member.1.2
  have hf := f9_section_faithful _ h (criticalSection h s)
  have hdim : 2 < Module.finrank (ZMod 2) m.leftEmbedding.range := by
    rw [←(LinearEquiv.ofInjective m.leftEmbedding m.left_injective).finrank_eq]
    change 2 < Module.finrank (ZMod 2) (BinaryLinearThree.Vector ×
      Module.Dual (ZMod 2) BinaryLinearThree.Vector)
    rw [Module.finrank_prod,Subspace.dual_finrank_eq]
    norm_num [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  have hp := quadratic_preserves_large_pair ρ hf m.leftEmbedding.range m.rightEmbedding.range
    m.disjoint hspan hdim A p.member.2.1 p.member.2.2 (fun a _ => hperm a)
  rw [hN]
  apply le_inf
  · apply le_subspaceStabilizer
    intro b hb v hv
    exact (hp b hb).1 ▸ Submodule.mem_map_of_mem hv
  · apply le_subspaceStabilizer
    intro b hb v hv
    exact (hp b hb).2 ▸ Submodule.mem_map_of_mem hv

/-- The original actor satisfies the rank and displacement inequalities
(c)--(d); rank-two component images are inner with displacement three,
as required in (g)--(i). All images use the same literal quotient actor. -/
theorem QuadraticEndpoint.paired_actor_estimates
    {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (p : QuadraticEndpoint h ρ) (hb : 3 ≤ h.b)
    (s : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (N : Subgroup (Source.Hstar D.H)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : Source.Hstar D.H,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range)) :
    let A := Source.starImage D.H (p.endpoint.conjugate D.UH)
    let B := A.subgroupOf N
    A ≤ N ∧
    rank A ≤ rank (B.map m.left) + rank (B.map m.right) ∧
    fixedCodim autAction (B.map m.left) + fixedCodim autAction (B.map m.right) ≤ fixedCodim ρ A ∧
    rank (B.map m.left) ≤ 2 ∧ rank (B.map m.right) ≤ 2 ∧
    (B.map m.left ≠ ⊥ → rank (B.map m.left) < fixedCodim autAction (B.map m.left)) ∧
    (B.map m.right ≠ ⊥ → rank (B.map m.right) < fixedCodim autAction (B.map m.right)) ∧
    (rank (B.map m.left) = 2 → B.map m.left ≤ MulAut.innerSubgroup BinaryLinearThree.Group ∧
      fixedCodim autAction (B.map m.left) = 3) ∧
    (rank (B.map m.right) = 2 → B.map m.right ≤ MulAut.innerSubgroup BinaryLinearThree.Group ∧
      fixedCodim autAction (B.map m.right) = 3) := by
  let A := Source.starImage D.H (p.endpoint.conjugate D.UH)
  let B := A.subgroupOf N
  have hAN := p.le_pair_stabilizer hb s N m hN hspan hperm
  let : IsElementaryAbelian 2 A := p.member.1.2
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAN
  let : IsElementaryAbelian 2 (B.map m.left) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (B.map m.right) := IsElementaryAbelian.map _
  have hf := f9_section_faithful _ h (criticalSection h s)
  have hm : B.map N.subtype = A := map_subgroupOf_eq_of_le hAN
  have hr := rank_map_injective N.subtype N.subtype_injective B
  rw [hm] at hr
  have hc := fixedCodim_map_equivariant (ρ.comp N.subtype) ρ N.subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) B
  rw [hm] at hc
  have hq : IsQuadratic (ρ.comp N.subtype) B := by
    intro a ha b hb v
    exact p.member.2.1 a ha b hb v
  have hqi := m.quadratic_images B hq
  have hrl := m.rank_le_sum (hf.comp N.subtype_injective) B
  have hdc := m.sum_fixedCodim_le B
  rw [←hr] at hrl
  rw [hc] at hdc
  exact ⟨hAN,hrl,hdc,(m.image_ranks_le_two B).1,(m.image_ranks_le_two B).2,
    (m.image_rank_lt_codim B).1,(m.image_rank_lt_codim B).2,
    fun hr => Paired.rank_two_profile _ hqi.1 hr,
    fun hr => Paired.rank_two_profile _ hqi.2 hr⟩

/-- The full paired marking discharges the no-FF and no-transvection steps
before selection; the resulting actor normalizes both original components. -/
theorem source_quadraticEndpoint_of_paired_supports
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (s : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (N : Subgroup (Source.Hstar Mc)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : Source.Hstar Mc,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (K Kplus : Subgroup G)
    (hK : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.leftEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.rightEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc))) :
    ¬ IsFFModule ρ ∧
      ∃ p : QuadraticEndpoint
        (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) ρ,
        p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ normalizer (K : Set G) ∧
        p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ normalizer (Kplus : Set G) := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  have hf := f9_section_faithful _ h (criticalSection h s)
  refine ⟨Paired.not_ff_of_permuted_pair ρ N m hf hN hspan hperm,?_⟩
  obtain ⟨p⟩ := source_quadraticEndpoint_of_no_transvections hG T hempty hM hunique hmany hcard e hab s
    (Paired.no_involution_transvections ρ N m hf hN hspan hperm)
  refine ⟨p,?_⟩
  apply source_quadratic_actor_normalizes_components hG T hempty hM hunique hmany hcard e hab p s
    m.leftEmbedding.range m.rightEmbedding.range m.disjoint hspan _ hperm K Kplus hK hKplus
  rw [←(LinearEquiv.ofInjective m.leftEmbedding m.left_injective).finrank_eq]
  change Module.finrank (ZMod 2) (BinaryLinearThree.Vector ×
    Module.Dual (ZMod 2) BinaryLinearThree.Vector) = 6
  rw [Module.finrank_prod,Subspace.dual_finrank_eq]
  norm_num [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]

omit [Finite G] in
private theorem starImage_centralizes_of_commutator_le
    (H A B : Subgroup G) (hc : ⁅A,B⁆ ≤ H.pCoreIn 2) :
    Source.starImage H A ≤ centralizer (Source.starImage H B : Set (Source.Hstar H)) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  change ⁅(A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)),
    (B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))⁆ = ⊥
  rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have hQ : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [←hQ]
  apply commutator_le.mpr
  intro a ha b hb
  exact hc (commutator_mem_commutator ha hb)

/-- Once the point lies in the first support, the existing component
centralization lemma kills the second action. The literal first image then
has the full actor rank, bounded by two. The marked component embedding and
its covariance identify which automorphism action is being killed. -/
theorem source_actor_rank_and_inner_of_point_support
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (s : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (p : QuadraticEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) ρ)
    (N : Subgroup (Source.Hstar Mc)) (m : Paired.Marking (ρ.comp N.subtype))
    (hAN : Source.starImage Mc (p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc)) ≤ N)
    (K Kplus : Subgroup G)
    (hiKplus : p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ normalizer (Kplus : Set G))
    (hpoint : p.endpoint.conjugate (centralInvolutions T) ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hKplusM : Kplus ≤ Mc) (hKplus : (Kplus.subgroupOf Mc).IsCComponent)
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    (κ : BinaryLinearThree.Group →* Source.Hstar Mc) (hκ : Function.Injective κ)
    (hκrange : κ.range = Source.starImage Mc Kplus)
    (hκact : ∀ (n : N) (k : BinaryLinearThree.Group),
      κ (m.right n k) = (n : Source.Hstar Mc) * κ k * (n : Source.Hstar Mc)⁻¹) :
    let A := Source.starImage Mc (p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc))
    rank A = rank ((A.subgroupOf N).map m.left) ∧ rank A ≤ 2 ∧
      (A.subgroupOf N).map m.left ≤ MulAut.innerSubgroup BinaryLinearThree.Group := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let A := Source.starImage Mc (p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc))
  have hf := f9_section_faithful _ h (criticalSection h s)
  have hc := source_actor_commutator_le_core_of_point_support hG T hempty hM hunique hmany hcard e hab
    K Kplus p.endpoint hiKplus hpoint hKplusM hKplus hcross
  have hcent := starImage_centralizes_of_commutator_le Mc _ Kplus hc
  have hk : A.subgroupOf N ≤ m.right.ker := by
    intro n hn
    apply MulEquiv.ext
    intro k
    apply hκ
    change κ (m.right n k) = κ k
    rw [hκact]
    have he := hcent hn (κ k) (hκrange ▸ (show κ k ∈ κ.range from ⟨k,rfl⟩))
    change κ k * (n : Source.Hstar Mc) = (n : Source.Hstar Mc) * κ k at he
    rw [←he,mul_inv_cancel_right]
  let : IsElementaryAbelian 2 A := p.member.1.2
  let : IsElementaryAbelian 2 (A.subgroupOf N) := IsElementaryAbelian.subgroupOf hAN
  have hr := m.rank_eq_left_of_right_trivial (hf.comp N.subtype_injective) (A.subgroupOf N) hk
  have he := rank_map_injective N.subtype N.subtype_injective (A.subgroupOf N)
  rw [map_subgroupOf_eq_of_le hAN] at he
  let B := A.subgroupOf N
  have hq : IsQuadratic (ρ.comp N.subtype) B := by
    intro a ha b hb v
    exact p.member.2.1 a ha b hb v
  have hcodim := fixedCodim_map_equivariant (ρ.comp N.subtype) ρ N.subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) B
  rw [map_subgroupOf_eq_of_le hAN] at hcodim
  have hsum := m.sum_fixedCodim_le B
  rw [hcodim] at hsum
  have hleftRank : rank A = rank (B.map m.left) := he.trans hr.1
  have hnon : B.map m.left ≠ ⊥ := by
    intro hz
    have hp := p.member.1.rank_pos
    change 0 < rank A at hp
    rw [hleftRank,hz,Representation.BinaryOffender.rank_bot] at hp
    omega
  let : IsElementaryAbelian 2 (B.map m.left) := IsElementaryAbelian.map _
  have hbudget := p.member.2.2
  change fixedCodim ρ A ≤ 2 * rank A at hbudget
  have hlocalBudget : fixedCodim autAction (B.map m.left) ≤ 2 * rank (B.map m.left) := by
    calc
      fixedCodim autAction (B.map m.left) ≤ fixedCodim ρ A := (Nat.le_add_right _ _).trans hsum
      _ ≤ 2 * rank A := hbudget
      _ = 2 * rank (B.map m.left) := congrArg (2 * ·) hleftRank
  have hi := LowRankProfiles.inner_of_quadratic_budget autAction autAction_inner
    (B.map m.left) ⟨hnon,inferInstance⟩ (m.quadratic_images B hq).1 hlocalBudget
  exact ⟨hleftRank,he.le.trans hr.2,hi⟩
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
