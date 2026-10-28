module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialOddNonfusion
public import Theory.GroupTheory.CyclicQuotientInvolutionTransfer
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms

/-!
# Involution transfer into the original intersection core

Let K = O²(H) and S = O₂(N_G(L) intersect H). When S lies in both
factors and K/O₂(K) is binary PSL₂, the actual quotient action gives a
homomorphism T → Aut(F) with kernel S. Finite-field automorphisms form a
cyclic group. Generalized Thompson transfer and the original ambient
nonabelian simplicity therefore fuse every involution of G into S.
The full cyclic quotient is retained; no index-two replacement is used.

The G₂ and triality applications discharge factor containment and the
quotient marking from their compatible comparisons. In triality this uses
the actual cubic-field arms quotient. Neither application assumes S=T
or odd original degree. They supply the fusion side of the F.4.38
contradiction; the outer-involution centralizer geometry is still needed
to deduce S=T. Original uniqueness and exhaustive comparison remain
inputs owned by the generic-global assembly.

Source: Aschbacher–Smith A.1.37(2), F.4.29(2) and F.4.38, printed
pp.31,289,294, and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- Generalized Thompson transfer through the actual right-quotient field action.
The kernel is the original intersection core S. -/
theorem Preparation.residual_involution_fused_into_sourceS
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n r : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i)
    (he : ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^r))
    (x : G) (hx : orderOf x=2) :
    ∃ y ∈ sourceS L H, IsConj x y := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : CommGroup (F ≃+* F) := IsCyclic.commGroup
  let : IsSimpleGroup G := h.qtke.simple
  obtain ⟨a,hxa⟩ := T.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have ha : orderOf a=2 := by
    rw [←Subgroup.orderOf_coe]
    obtain ⟨g,hg⟩ := isConj_iff.mp hxa
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  obtain ⟨b,hab,hb⟩ := T.exists_isConj_ker_of_cyclic_of_simple h.qtke.nonabelian
    (residualSylowFieldAction hTH e) a ha
  have hbS : b.val ∈ sourceS L H := by
    change b ∈ (sourceS L H).subgroupOf (T : Subgroup G)
    rw [←d.residual_sylow_field_kernel h hTH hS e]
    exact hb
  exact ⟨b.val,hbS,hxa.trans hab⟩

/-- Every ambient involution is fused into the original G₂ S, at all degrees. -/
theorem Preparation.g2_involution_fused_into_sourceS
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (x : G) (hx : orderOf x=2) :
    ∃ y ∈ sourceS L H, IsConj x y := by
  have hs := d.g2_local_structure h hTH hp F he
  exact d.residual_involution_fused_into_sourceS h hTH hs.2.2.2.2 hs.2.2.2.1 x hx

/-- Transfer into the original triality S retains the cubic-field quotient. -/
theorem Preparation.triality_involution_fused_into_sourceS
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)).reverse))
    (x : G) (hx : orderOf x=2) :
    ∃ y ∈ sourceS L H, IsConj x y := by
  have hs := d.triality_sourceS_le_factors h hTH hp m hm he
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hTH hp _ rfl he).elim
  obtain ⟨e⟩ := he
  exact d.residual_involution_fused_into_sourceS h hTH hs
    (d.triality_local_structure h hTH hp m hm e).2.2.2.2.1 x hx

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
