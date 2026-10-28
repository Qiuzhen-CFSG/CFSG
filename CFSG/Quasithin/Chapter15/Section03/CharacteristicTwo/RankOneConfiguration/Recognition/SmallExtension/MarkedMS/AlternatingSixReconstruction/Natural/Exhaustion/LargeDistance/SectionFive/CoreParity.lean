module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreMovement
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# Even actors detected by movement on the entire augmentation cover

A subactor retaining all movement of a quadratic elementary actor of order
at least four contains an even involution. If the subactor had no even
involution, sign would embed it in a group of order two. No involution moves
a core vector onto the constant vector: an involution doing so would consist
of three swaps and its preimage would have odd coordinate sum. Thus the
central-line alternative for the full actor is impossible. In the remaining
two-transposition case, an odd cyclic subactor cannot move both duad lines.

The conclusion concerns the literal symmetric marking and the full
five-dimensional cover. `RestrictedActor` uses it with equality of actual
commutators at opposite endpoints, strengthening the purely numerical
restriction argument without assuming a full-seed parity statement.
Source: MS93 (3.3)(ii), pp.866--867, and (5.0)--(5.2)(i), pp.912--914.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CoreCrossing
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
local notation "ρ" => coreRepresentation (Fin 6)

set_option maxRecDepth 4096 in
private theorem no_constant : ∀ a : S, a ^ 2 = 1 → ∀ v : Full (Fin 6),
    (∑ i, v i) = 0 → representation (Fin 6) a v - v ≠ allOne (Fin 6) := by
  decide +kernel
private theorem odd_pair : ∀ i : Fin 4, Equiv.Perm.sign (initialWords 2 i) ≠ 1 →
    ∀ v w : Full (Fin 6),
      representation (Fin 6) (initialWords 2 i) v-v ≠ (pairWord 0 1).val ∨
      representation (Fin 6) (initialWords 2 i) w-w ≠ (pairWord 2 3).val := by
  decide +kernel


private theorem action_surjective (g : S) : Function.Surjective (ρ g) :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv ((coreRepresentation (Fin 6)).asGroupHom g)).surjective

private theorem one_in_kernel : oneWord ∈ (coreToNatural (Fin 6)).ker := by
  apply Subtype.ext
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span (by simp [oneWord]))

private theorem even_of_preserved_core_movement (B : Subgroup S) [IsElementaryAbelian 2 B]
    (hB : 4 ≤ Nat.card B) (hq : CoreActor.Quadratic B)
    (c : S) (hc : c ∈ B)
    (hm : subspaceCommutator ρ ⊤ B = LinearMap.range (ρ c - LinearMap.id)) :
    c ∈ alternatingGroup (Fin 6) := by
  by_contra hodd
  have hsq := elemPow_eq_one_of_isElementaryAbelian (p := 2) c hc
  rcases CoreActor.kernel_or_two_transpositions B hB hq with hk | ⟨g,hg⟩
  · have hh := hk one_in_kernel
    rw [hm] at hh
    obtain ⟨v,hv⟩ := hh
    exact no_constant c hsq v.val v.property (congrArg Subtype.val hv)
  · rw [hg] at hc
    obtain ⟨c₀,hc₀,rfl⟩ := hc
    obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (2 : Fin 4) c₀).mp hc₀
    have hsign : Equiv.Perm.sign (initialWords 2 i) ≠ 1 := by
      intro he
      apply hodd
      change Equiv.Perm.sign (g * initialWords 2 i * g⁻¹) = 1
      simp only [map_mul,map_inv,he,mul_one,mul_inv_cancel]
    have topmap : (⊤ : Submodule (ZMod 2) C).map (ρ g) = ⊤ := by
      rw [Submodule.map_top,LinearMap.range_eq_top.mpr (action_surjective g)]
    have hmoved : subspaceCommutator ρ ⊤ B = CoreMovement.movedPlane.map (ρ g) := by
      rw [hg,←topmap,CoreMovement.conjugate_moved,CoreMovement.exceptional_moved_eq]
    have pair_in (v : C) (hv : v ∈ CoreMovement.movedPlane) :
        ∃ w : C, ρ (initialWords 2 i) w-w = v := by
      have hh : ρ g v ∈ subspaceCommutator ρ ⊤ B := by
        rw [hmoved]
        exact ⟨v,hv,rfl⟩
      rw [hm] at hh
      obtain ⟨w,hw⟩ := hh
      obtain ⟨z,rfl⟩ := action_surjective g w
      refine ⟨z,?_⟩
      apply (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((coreRepresentation (Fin 6)).asGroupHom g)).injective
      change ρ g (ρ (initialWords 2 i) z-z) = ρ g v
      change ρ ((MulAut.conj g) (initialWords 2 i)) (ρ g z)-ρ g z = ρ g v at hw
      simp only [map_sub,←Module.End.mul_apply,←map_mul] at hw ⊢
      simpa only [MulAut.conj_apply,inv_mul_cancel_right] using hw
    obtain ⟨v,hv⟩ := pair_in (pairWord 0 1) (Submodule.subset_span (by simp))
    obtain ⟨w,hw⟩ := pair_in (pairWord 2 3) (Submodule.subset_span (by simp))
    rcases odd_pair i hsign v.val w.val with hh | hh
    · exact hh (congrArg Subtype.val hv)
    · exact hh (congrArg Subtype.val hw)

/-- A subactor retaining all movement of a large quadratic actor on the full
augmentation cover contains an even involution in the same coordinates. -/
theorem core_preserving_actor_even (B C₀ : Subgroup S) [IsElementaryAbelian 2 B]
    (hCB : C₀ ≤ B) (hB : 4 ≤ Nat.card B) (hq : CoreActor.Quadratic B)
    (hm : subspaceCommutator ρ ⊤ C₀ = subspaceCommutator ρ ⊤ B) :
    ∃ c ∈ C₀, orderOf c = 2 ∧ c ∈ alternatingGroup (Fin 6) := by
  let : IsElementaryAbelian 2 C₀ := IsElementaryAbelian.of_le hCB
  by_contra hn
  have hnone : ∀ c ∈ C₀, c ≠ 1 → c ∉ alternatingGroup (Fin 6) := by
    intro c hc hne he
    exact hn ⟨c,hc,orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian c hc) hne,he⟩
  let f := (Equiv.Perm.sign (α := Fin 6)).comp C₀.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro c hc
    by_contra hne
    exact hnone c c.property (fun he => hne (Subtype.ext he)) hc
  have hsmall : Nat.card C₀ ≤ 2 := by
    have hh := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_eq_fintype_card,Fintype.card_units_int] using hh
  have hne : C₀ ≠ ⊥ := by
    intro he
    have hbot : subspaceCommutator ρ ⊤ (⊥ : Subgroup S) = ⊥ := by
      apply le_antisymm _ bot_le
      apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,v,_,rfl⟩
      rw [show a = 1 from ha,map_one,Module.End.one_apply,sub_self]
      exact Submodule.zero_mem _
    have hfix : B = ⊥ := by
      apply le_bot_iff.mp
      intro b hb
      apply naturalRepresentation_injective (Fin 6) (by decide)
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := coreToNatural_surjective v
      have hv : ρ b w-w ∈ subspaceCommutator ρ ⊤ C₀ := by
        rw [hm]
        exact Submodule.subset_span ⟨b,hb,w,Submodule.mem_top,rfl⟩
      rw [he,hbot] at hv
      have hh : ρ b w = w := sub_eq_zero.mp hv
      rw [map_one,Module.End.one_apply,←coreToNatural_equivariant,hh]
    rw [hfix,card_bot] at hB
    omega
  obtain ⟨c,hc,hc1⟩ := C₀.bot_or_exists_ne_one |>.resolve_left hne
  have ho : orderOf c = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian c hc) hc1
  have heq : zpowers c = C₀ := eq_of_le_of_card_ge (zpowers_le.mpr hc) (by
    rw [Nat.card_zpowers,ho]
    exact hsmall)
  have hrange : subspaceCommutator ρ ⊤ B = LinearMap.range (ρ c-LinearMap.id) := by
    rw [←hm,←heq,Representation.CyclicFixedRank.commutator_eq_range]
  exact hnone c hc hc1 (even_of_preserved_core_movement B hB hq c (hCB hc) hrange)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
