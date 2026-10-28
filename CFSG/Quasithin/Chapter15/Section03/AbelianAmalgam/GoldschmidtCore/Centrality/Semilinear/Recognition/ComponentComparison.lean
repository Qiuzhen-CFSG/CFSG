module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FFComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.LinearThreeBound

/-!
# Identifying the component inside the surviving offender actors

The actual generalized Fitting subgroup lies in the offender actor by the
best-offender commutator argument. When that actor is simple, its normal
nontrivial component fills it. In S₅ the nontrivial normal perfect subgroup
is exactly the actual A₅: normality contains A₅, and perfectness puts the
subgroup inside the derived group A₅. Both conclusions retain the original
embedding into the quotient group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and
F.6.18 in the repaired 15.3.68 comparison, pp.1154–1155.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite D] in
private theorem fitting_nontrivial (h : IsQuasisimple (generalizedFitting D)) :
    Nontrivial (generalizedFitting D) := by
  let : IsSimpleGroup ((generalizedFitting D) ⧸ center (generalizedFitting D)) := h.simple
  exact (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial

/-- The component fills a simple actual offender actor. -/
theorem fitting_eq_simple_offender (ρ : Representation (ZMod 2) D W)
    (hne : offenderSubgroup ρ ≠ ⊥) (hcore : pCore 2 D = ⊥)
    (hL : IsQuasisimple (generalizedFitting D)) [IsSimpleGroup (offenderSubgroup ρ)] :
    generalizedFitting D = offenderSubgroup ρ := by
  have hl := fitting_le_offender ρ hne hcore hL
  let : (generalizedFitting D).Normal := generalizedFitting_normal
  let N := (generalizedFitting D).subgroupOf (offenderSubgroup ρ)
  let : N.Normal := inferInstance
  let : Nontrivial (generalizedFitting D) := fitting_nontrivial hL
  have hn : N ≠ ⊥ := by
    intro hn
    have hh := congrArg (Subgroup.map (offenderSubgroup ρ).subtype) hn
    rw [map_subgroupOf_eq_of_le hl, Subgroup.map_bot] at hh
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hh
  have ht : N = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal N inferInstance).resolve_left hn
  have hh := congrArg (Subgroup.map (offenderSubgroup ρ).subtype) ht
  simpa only [N, map_subgroupOf_eq_of_le hl, ← MonoidHom.range_eq_map, range_subtype] using hh

private theorem normal_perfect_symmetricFive (N : Subgroup (Equiv.Perm (Fin 5)))
    [N.Normal] [Group.IsPerfect N] [Nontrivial N] : N = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rw [← alternatingGroup.commutator_perm_eq (by norm_num)]
    change N ≤ ⁅(⊤ : Subgroup (Equiv.Perm (Fin 5))), ⊤⁆
    rw [← N.commutator_eq_self]
    exact commutator_mono le_top le_top
  · exact Equiv.Perm.alternatingGroup_le_of_normal (by norm_num) inferInstance

/-- In the S₅ case the source marking identifies the actual component with
A₅, including its image under the original actor equivalence. -/
theorem fitting_in_symmetricFive (ρ : Representation (ZMod 2) D W)
    (hne : offenderSubgroup ρ ≠ ⊥) (hcore : pCore 2 D = ⊥)
    (hL : IsQuasisimple (generalizedFitting D))
    (e : offenderSubgroup ρ ≃* Equiv.Perm (Fin 5)) :
    ((generalizedFitting D).subgroupOf (offenderSubgroup ρ)).map e.toMonoidHom =
      alternatingGroup (Fin 5) ∧
    Nonempty (generalizedFitting D ≃* alternatingGroup (Fin 5)) := by
  have hl := fitting_le_offender ρ hne hcore hL
  let N := (generalizedFitting D).subgroupOf (offenderSubgroup ρ)
  let : (generalizedFitting D).Normal := generalizedFitting_normal
  let : N.Normal := inferInstance
  let : IsQuasisimple (generalizedFitting D) := hL
  let : Nontrivial (generalizedFitting D) := fitting_nontrivial hL
  let a : generalizedFitting D ≃* N := (subgroupOfEquivOfLe hl).symm
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let : Nontrivial N := a.injective.nontrivial
  let : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  let : Group.IsPerfect (N.map e.toMonoidHom) := Group.IsPerfect.map _
  let : Nontrivial (N.map e.toMonoidHom) := (e.subgroupMap N).injective.nontrivial
  have hm := normal_perfect_symmetricFive (N.map e.toMonoidHom)
  exact ⟨hm, ⟨a.trans ((e.subgroupMap N).trans (MulEquiv.subgroupCongr hm))⟩⟩

/-- The binary degree-two actor is simple in precisely the degrees surviving
B.5.1, so its actual inclusion identifies it with the ambient component. -/
theorem fitting_eq_linearTwo_offender (ρ : Representation (ZMod 2) D W)
    (hne : offenderSubgroup ρ ≠ ⊥) (hcore : pCore 2 D = ⊥)
    (hL : IsQuasisimple (generalizedFitting D))
    (F : BinaryField) (hn : 2 ≤ F.degree)
    (e : offenderSubgroup ρ ≃* SL(2,F.Carrier)) :
    generalizedFitting D = offenderSubgroup ρ := by
  let : IsSimpleGroup PSL(2,F.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [F.card_eq]
      exact (by decide : 4 = 2 ^ 2) ▸ Nat.pow_le_pow_right (by decide : 0 < 2) hn)
  let : IsSimpleGroup (offenderSubgroup ρ) := (e.trans (linearTwoProjectiveEquiv F)).isSimpleGroup
  exact fitting_eq_simple_offender ρ hne hcore hL

/-- Odd field degree removes the scalar center in degree three. The resulting
projective simplicity applies to the actual offender actor. -/
theorem fitting_eq_linearThree_offender (ρ : Representation (ZMod 2) D W)
    (hne : offenderSubgroup ρ ≠ ⊥) (hcore : pCore 2 D = ⊥)
    (hL : IsQuasisimple (generalizedFitting D))
    (F : BinaryField) (ho : Odd F.degree)
    (e : offenderSubgroup ρ ≃* SL(3,F.Carrier)) :
    generalizedFitting D = offenderSubgroup ρ := by
  let : IsSimpleGroup PSL(3,F.Carrier) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (offenderSubgroup ρ) :=
    (e.trans (oddLinearThreeProjectiveEquiv F ho)).isSimpleGroup
  exact fitting_eq_simple_offender ρ hne hcore hL

/-- The complete B-side comparison, including the original component embedding.
The quasisimplicity and small Sylow bound must still be proved from F.6.18;
they are explicit conditional hypotheses here, not classification premises. -/
theorem fitting_source_rank_one (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥) (hL : IsQuasisimple (generalizedFitting D))
    (S : Sylow 2 D) (hS : Nat.card S ≤ 128)
    (h : SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)) :
    (generalizedFitting D = offenderSubgroup ρ ∧
      ∃ F : BinaryField, 2 ≤ F.degree ∧ Nonempty (generalizedFitting D ≃* SL(2,F.Carrier))) ∨
    (generalizedFitting D = offenderSubgroup ρ ∧
      Nonempty (generalizedFitting D ≃* SL(3,ZMod 2))) ∨
    (Nonempty (offenderSubgroup ρ ≃* Equiv.Perm (Fin 5)) ∧
      Nonempty (generalizedFitting D ≃* alternatingGroup (Fin 5))) := by
  rcases offender_source_rank_one ρ hr hne hcore hL h with h | h | h
  · obtain ⟨F, hn, ⟨e⟩⟩ := h
    have he := fitting_eq_linearTwo_offender ρ hne hcore hL F hn e
    exact Or.inl ⟨he, F, hn, ⟨(MulEquiv.subgroupCongr he).trans e⟩⟩
  · obtain ⟨F, ho, ⟨e⟩⟩ := h
    have he := fitting_eq_linearThree_offender ρ hne hcore hL F ho e
    obtain ⟨a⟩ := linearThree_binary_equiv (offenderSubgroup ρ) F ho e S hS
    exact Or.inr (Or.inl ⟨he, ⟨(MulEquiv.subgroupCongr he).trans a⟩⟩)
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr ⟨⟨e⟩, (fitting_in_symmetricFive ρ hne hcore hL e).2⟩)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
