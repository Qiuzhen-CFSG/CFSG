module
public import Theory.Representation.BinaryPermutation.AlternatingEightNaturalFixedLine
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Sylow
public import Theory.Representation.SL5ExteriorSquare.SylowFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation

/-!
# Fixed-line block exclusions for the binary doubled orbit

A Sylow two-subgroup fixes at most two vectors on the natural A₈ six-space,
on every single natural binary linear module, and on either ten-dimensional
irreducible for SL₅(2). The first two bounds use the actual permutation and
matrix actions. The last uses irreducibility of the intrinsic block module
and recognition with the original actor marking, allowing its graph twist.

Projection of a subgroup of U(K) disjoint from Z(K) into the block module
is injective. Transport through the actual two-core quotient and module
marking therefore bounds any such Sylow-fixed subgroup by two.

NonFFSourceDoubledBinaryFixedLineBlocks applies these bounds to the original
residual four-space. Its index-two Sylow action has at least four fixed
vectors, excluding these blocks on the same selected component. The
ordinary alternating blocks of degrees five through eight are thereby all
excluded; single natural modules remain distinct from repeated or
natural--dual modules.

Source: Aschbacher--Smith, proof of Proposition 7.7.3 after Lemma 7.7.10,
printed p.709, refs/quasithin.pdf; B.3.1--2 and I.1.6(7) for the model bounds.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFixedLineBlocks
open scoped MatrixGroups IsMulCommutative

/-- Transfer a fixed-point bound through the literal central quotient of a block. -/
theorem linear_block_sylow_fixed_card
    {L A V : Type*} [Group L] [Finite L] [Group A] [Finite A]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (hb : ChapterC.IsLinearBlockModel L ρ)
    (b : ℕ) (hfixed : ∀ P : Sylow 2 A, Nat.card (fixedSpace ρ (P : Subgroup A)) ≤ b)
    (S : Sylow 2 L) (D : Subgroup L)
    (hDU : D ≤ ChapterC.blockU L) (hDZ : Disjoint D (center L))
    (hDS : D ≤ centralizer (S : Set L)) : Nat.card D ≤ b := by
  obtain ⟨r,⟨m⟩,hm⟩ := hb
  let q : L →* A := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hq
  let : Finite V := Finite.of_injective
    (fun v => m.moduleIso.symm (Multiplicative.ofAdd v))
    (m.moduleIso.symm.injective.comp Multiplicative.ofAdd.injective)
  let f : D →* Multiplicative V := m.moduleIso.toMonoidHom.comp
    ((QuotientGroup.mk' (ChapterC.blockFixed L)).comp (inclusion hDU))
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro d hd
    change f d = 1 at hd
    have hz : QuotientGroup.mk' (ChapterC.blockFixed L) (inclusion hDU d) = 1 :=
      m.moduleIso.injective (by change f d = m.moduleIso 1; simpa only [map_one] using hd)
    have hc : (d : L) ∈ center L := (QuotientGroup.eq_one_iff (inclusion hDU d)).mp hz
    have hh : (d : L) ∈ D ⊓ center L := ⟨d.property,hc⟩
    rw [hDZ.eq_bot] at hh
    exact Subtype.ext (mem_bot.mp hh)
  let j : D → fixedSpace ρ (P : Subgroup _) := fun d =>
    ⟨(f d).toAdd,by
      intro a
      obtain ⟨l,hl,he⟩ := a.property
      have hd : ChapterC.blockConjugate L l (inclusion hDU d) = inclusion hDU d := by
        apply Subtype.ext
        change l*(d : L)*l⁻¹ = (d : L)
        rw [hDS d.property l hl,mul_inv_cancel_right]
      have hh := congrArg Multiplicative.toAdd (m.intertwining l (inclusion hDU d))
      rw [hd,hm] at hh
      change (f d).toAdd = ρ (q l) (f d).toAdd at hh
      rw [he] at hh
      exact hh.symm⟩
  have hj : Function.Injective j := by
    intro x y he
    apply hf
    exact Multiplicative.toAdd.injective (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective j hj).trans (hfixed P)

/-- A Sylow of A₈ fixes at most two vectors in its actual natural six-space. -/
theorem eight_sylow_fixed_card (P : Sylow 2 (alternatingGroup (Fin 8))) :
    Nat.card (fixedSpace (alternatingNaturalRepresentation (Fin 8)) (P : Subgroup _)) ≤ 2 := by
  classical
  let F := fixedSpace (alternatingNaturalRepresentation (Fin 8)) (P : Subgroup _)
  by_cases hF : F = ⊥
  · change Nat.card F ≤ 2
    rw [hF,Nat.card_unique]
    decide
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
  let j : F → Bool := fun w => decide (w.val ≠ 0)
  have hj : Function.Injective j := by
    intro a b he
    have ha := alternatingEight_sylow_fixed_unique P v a hv0 hv a.property
    have hb := alternatingEight_sylow_fixed_unique P v b hv0 hv b.property
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Subtype.ext (ha.trans hb.symm)
    · change decide (a.val ≠ 0) = decide (b.val ≠ 0) at he
      rw [ha,hb] at he
      simp [hv0] at he
    · change decide (a.val ≠ 0) = decide (b.val ≠ 0) at he
      rw [ha,hb] at he
      simp [hv0] at he
    · exact Subtype.ext (ha.trans hb.symm)
  simpa using Nat.card_le_card_of_injective j hj

/-- An embedded Sylow-fixed subgroup of an ordinary A₈ block has order at most two. -/
theorem eight_block_sylow_fixed_card {L : Type*} [Group L] [Finite L]
    (hb : ChapterC.IsAlternatingBlock L 8) (S : Sylow 2 L) (D : Subgroup L)
    (hDU : D ≤ ChapterC.blockU L) (hDZ : Disjoint D (center L))
    (hDS : D ≤ centralizer (S : Set L)) : Nat.card D ≤ 2 := by
  exact linear_block_sylow_fixed_card (alternatingNaturalRepresentation (Fin 8))
    hb.2.2 2 eight_sylow_fixed_card S D hDU hDZ hDS

/-- The fixed space of a binary special-linear Sylow is a single binary line. -/
theorem binary_linear_sylow_fixed_card (n : ℕ) (hn : 0 < n)
    (P : Sylow 2 SL(n,ZMod 2)) :
    Nat.card (fixedSpace (specialLinearNatural (k := ZMod 2) n) (P : Subgroup _)) ≤ 2 := by
  let e := BinaryLinear.OuterCyclic.slEquivLinear n
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨v,hv,hline⟩ := BinaryNaturalDual.VectorStabilizers.Pure.linear_sylow_fixed_line
    (V := Fin n → ZMod 2) (by simpa using hn) S
  have heq : fixedSpace (specialLinearNatural (k := ZMod 2) n) (P : Subgroup _) =
      BinaryLinear.fixedSpace (S : Subgroup _) := by
    ext w
    constructor
    · intro hw a ha
      obtain ⟨g,hg,rfl⟩ := ha
      exact hw ⟨g,hg⟩
    · intro hw g
      exact hw (e g) (mem_map_of_mem e.toMonoidHom g.property)
  rw [heq,hline,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    finrank_span_singleton hv]
  decide

/-- A single natural binary linear block has at most two Sylow-fixed vectors. -/
theorem binary_linear_block_sylow_fixed_card {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hb : ChapterC.IsLinearTwoBlock L n) (S : Sylow 2 L) (D : Subgroup L)
    (hDU : D ≤ ChapterC.blockU L) (hDZ : Disjoint D (center L))
    (hDS : D ≤ centralizer (S : Set L)) : Nat.card D ≤ 2 := by
  exact linear_block_sylow_fixed_card (specialLinearNatural (k := ZMod 2) n)
    hb.2.2.2 2 (binary_linear_sylow_fixed_card n (by have := hb.1; omega)) S D hDU hDZ hDS


/-- The ten-dimensional irreducible block for SL₅(2) has at most two
Sylow-fixed vectors, including either graph twist of its exterior module. -/
theorem linear_five_ten_block_sylow_fixed_card {L : Type*} [Group L] [Finite L]
    (hb : ChapterC.IsShort L)
    (m : (L ⧸ pCore 2 L) ≃* SL(5,ZMod 2))
    (hc : Nat.card (ChapterC.BlockModule L) = 2 ^ 10)
    (S : Sylow 2 L) (D : Subgroup L)
    (hDU : D ≤ ChapterC.blockU L) (hDZ : Disjoint D (center L))
    (hDS : D ≤ centralizer (S : Set L)) : Nat.card D ≤ 2 := by
  let := hb.elementary
  let : IsElementaryAbelian 2 (ChapterC.BlockModule L) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.mk' (ChapterC.blockFixed L))
      (QuotientGroup.mk'_surjective _)
  let ρ := ChapterC.ExceptionalRestrictions.moduleRepresentation hb
  let := ChapterC.ExceptionalRestrictions.moduleRepresentation_irreducible hb
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hd : Module.finrank (ZMod 2) (Additive (ChapterC.BlockModule L)) = 10 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive (ChapterC.BlockModule L)) =
          Nat.card (Additive (ChapterC.BlockModule L)) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      _ = 2 ^ 10 := (Nat.card_congr Additive.toMul).trans hc
  have hbound : Nat.card (fixedSpace ρ (P : Subgroup _)) ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (SL5ExteriorSquare.marked_sylow_fixed_finrank_le_one ρ m hd P)).trans_eq (by decide)
  let f : D →* ChapterC.BlockModule L :=
    (QuotientGroup.mk' (ChapterC.blockFixed L)).comp (inclusion hDU)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro d hd
    have hz : (d : L) ∈ center L := (QuotientGroup.eq_one_iff (inclusion hDU d)).mp hd
    have hh : (d : L) ∈ D ⊓ center L := ⟨d.property,hz⟩
    rw [hDZ.eq_bot] at hh
    exact Subtype.ext (mem_bot.mp hh)
  let j : D → fixedSpace ρ (P : Subgroup _) := fun d =>
    ⟨Additive.ofMul (f d),by
      intro a
      obtain ⟨l,hl,he⟩ := a.property
      have hd : ChapterC.blockConjugate L l (inclusion hDU d) = inclusion hDU d := by
        apply Subtype.ext
        change l*(d : L)*l⁻¹ = (d : L)
        rw [hDS d.property l hl,mul_inv_cancel_right]
      change ρ a.val (Additive.ofMul (f d)) = Additive.ofMul (f d)
      rw [←he]
      apply Additive.toMul.injective
      exact (hb.exists_quotient_moduleAction.choose_spec l (inclusion hDU d)).trans
        (congrArg (QuotientGroup.mk' (ChapterC.blockFixed L)) hd)⟩
  have hj : Function.Injective j := by
    intro x y he
    exact hf (congrArg (fun z => z.val.toMul) he)
  exact (Nat.card_le_card_of_injective j hj).trans hbound

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFixedLineBlocks
