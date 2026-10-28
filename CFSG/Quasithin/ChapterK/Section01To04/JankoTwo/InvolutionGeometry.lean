module
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.InvolutionGeometry.Local
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Fusion

/-!
# The two Hall--Janko involution-actor bounds for K.4.5

Conjugate an elementary actor into the certified Sylow subgroup. Every
conjugate of the 2-central involution `FirstFusion.t` fixes a permutation point,
so the four-color calculation bounds a pure actor by rank two. Exhaustive
involution fusion then selects a conjugate of the noncentral `GeneratorPair.a`
in every actor of rank at least three.

In the actual permutation extension, conjugation preserves the literal image
of `intoExtension`. An outer involution therefore selects the eight-color
calculation after Sylow placement, giving rank at most three. No rank bound,
centralizer recognition, or replacement group is assumed.

Source: Aschbacher--Smith K.4.5, printed p.460 / PDF p.471; the original
ATLAS J2G1-p100B0 attribution is retained in the imported carrier and tables.
-/

public section
namespace CFSG.Quasithin.ChapterK.JankoTwo
open Sporadic.LeechRelated.J2
open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.SecondParabolic
open Representation.BinaryOffender
open scoped Pointwise

private theorem elementary_conjugate_into {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [IsElementaryAbelian 2 A] (S : Sylow 2 G) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S := by
  obtain ⟨T, hT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  refine ⟨g, ?_⟩
  have hm := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hT
  have he : (T : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) := by
    change (↑(g • T) : Subgroup G) = S
    rw [hg]
  exact he ▸ hm

private theorem fixed_point_of_isConj {x : Carrier} (hx : IsConj GeneratorPair.FirstFusion.t x) :
    ∃ p, inclusion x p = p := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hx
  have ht : inclusion GeneratorPair.FirstFusion.t 0 = 0 := by
    rw [GeneratorPair.FirstFusion.inclusion_t]
    decide +kernel
  refine ⟨inclusion g 0, ?_⟩
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, ht]

/-- A pure 2-central elementary abelian subgroup of the actual degree-100
carrier has at most four elements (K.4.5, printed p.460). -/
theorem pure_twoCentral_card_le (A : Subgroup Carrier) (hA : IsElementaryAbelian 2 A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj GeneratorPair.FirstFusion.t x) :
    Nat.card A ≤ 4 := by
  let := hA
  obtain ⟨g, hg⟩ := elementary_conjugate_into A (sylow FirstParabolic.card_l₁)
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hb : Nat.card B ≤ 4 := InvolutionGeometry.inner_sylow_card_le B hg (by
    rintro x ⟨y, hy, rfl⟩
    by_cases he : y = 1
    · subst y
      exact ⟨0, by simp⟩
    · apply fixed_point_of_isConj
      exact (hpure y hy he).trans (isConj_iff.mpr ⟨g, rfl⟩))
  simpa only [B, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective] using hb

/-- The pure-class actor bound needed in K.4.5. The nontriviality hypothesis
matches the source actor convention. -/
theorem pure_twoCentral_rank_le (A : Subgroup Carrier) (hA : IsElementaryTwo A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj GeneratorPair.FirstFusion.t x) : rank A ≤ 2 := by
  have h := Nat.log_mono_right (b := 2) (pure_twoCentral_card_le A hA.2 hpure)
  exact h.trans_eq (by decide)

/-- Exhaustive fusion and the pure bound select the source's noncentral
involution in every elementary actor of rank at least three. -/
theorem exists_noncentral_involution (A : Subgroup Carrier) (hA : IsElementaryTwo A)
    (hr : 3 ≤ rank A) : ∃ x ∈ A, IsConj GeneratorPair.a x := by
  classical
  let := hA.2
  by_contra hn
  have hpure : ∀ x ∈ A, x ≠ 1 → IsConj GeneratorPair.FirstFusion.t x := by
    intro x hx hne
    have ho : orderOf x = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian x hx) hne
    exact (InnerInvolutionCores.involution_fusion x ho).resolve_left (fun h => hn ⟨x, hx, h⟩)
  have := pure_twoCentral_rank_le A hA hpure
  omega

private theorem inner_range_conj {x : Extension} (g : Extension)
    (hx : x ∈ intoExtension.range) : g * x * g⁻¹ ∈ intoExtension.range := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨extensionAction g y, ?_⟩
  apply extensionAction_injective
  simp only [extensionAction_inner, map_mul, map_inv]
  ext z
  simp

/-- An elementary abelian subgroup containing an actual outer element of
the given permutation extension has at most eight elements. -/
theorem outer_elementary_card_le (A : Subgroup Extension) (hA : IsElementaryAbelian 2 A)
    (i : Extension) (hi : i ∈ A) (hout : i ∉ intoExtension.range) : Nat.card A ≤ 8 := by
  let := hA
  obtain ⟨g, hg⟩ := elementary_conjugate_into A (outerSylow FirstParabolic.card_l₁)
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hiB : (MulAut.conj g) i ∈ B := Subgroup.mem_map_of_mem _ hi
  have ho : (MulAut.conj g) i ∉ intoExtension.range := by
    intro h
    have hh := inner_range_conj g⁻¹ h
    apply hout
    simpa [MulAut.conj_apply, mul_assoc] using hh
  have hb := InvolutionGeometry.outer_sylow_card_le B hg ((MulAut.conj g) i) hiB ho
  simpa only [B, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective] using hb

/-- The source's outer actor rank-three bound on the actual extension and
its literal inner inclusion. -/
theorem outer_elementary_rank_le (A : Subgroup Extension) (hA : IsElementaryAbelian 2 A)
    (i : Extension) (hi : i ∈ A) (_hi2 : orderOf i = 2)
    (hout : i ∉ intoExtension.range) : rank A ≤ 3 := by
  have h := Nat.log_mono_right (b := 2) (outer_elementary_card_le A hA i hi hout)
  exact h.trans_eq (by decide)

end CFSG.Quasithin.ChapterK.JankoTwo
