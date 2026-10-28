module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Covers
public import Theory.GroupTheory.CentralPPerfectCoprime
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Perfect actors on a normalized A₃-block

For a short group whose two-core quotient has order three, the image of
O₂ modulo U is central. Two-perfection kills this central two-extension of
the cyclic three-group, proving O₂ = U. The actual A₃ natural module has
order four, and the checked coprime covering argument makes C_U(B) trivial.
Thus U itself has order four.

A perfect subgroup normalizing B acts trivially on U and on B/O₂(B), since
both permutation groups are solvable. Its first commutator with B lies in
U, and the three-subgroups lemma kills that commutator. No identification
of B with A₄ is assumed, and no C-component classification is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–10
and C.1.12–13, printed pp.123–125; the solvable block case in the proof of
E.6.23, printed p.254. The fixed-layer argument is reused from
`InvariantSubspaces/LocalIndex/Conjugates/Factorizations/NaturalIndices/Covers`.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
open ChapterC

private theorem core_eq_blockU {L : Type*} [Group L] (h : IsShort L)
    (hcard : Nat.card (L ⧸ pCore 2 L) = 3) : pCore 2 L = blockU L := by
  let := h.finite
  let q := QuotientGroup.mk' (blockU L)
  let f := QuotientGroup.lift (blockU L) (QuotientGroup.mk' (pCore 2 L))
    (by rw [QuotientGroup.ker_mk']; exact blockU_le_core)
  have hk : f.ker = (pCore 2 L).map q := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (blockU L) y
      exact mem_map_of_mem q ((QuotientGroup.eq_one_iff x).mp hy)
    · rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff x).mpr hx
  let : IsCyclic (L ⧸ pCore 2 L) := isCyclic_of_prime_card hcard
  let : CommGroup (L ⧸ pCore 2 L) := IsMulCommutative.instCommGroup
  have hf : Function.Injective f :=
    f.injective_of_isPPerfect_of_coprime_abelian_image (h.quotient_twoPerfect (blockU L))
      (hk ▸ blockU_core_image_le_center) (hk ▸ pCore_isPGroup.map q)
      (fun _ _ => Commute.all _ _) (by decide : Nat.Coprime 2 3)
      (fun x => by rw [← hcard]; exact pow_card_eq_one')
  apply le_antisymm _ blockU_le_core
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hf
  exact ((QuotientGroup.eq_one_iff x).mpr hx).trans (map_one f).symm

private theorem perfect_small_action {A W : Type*} [Group A] [Group W]
    [Group.IsPerfect A] [Finite W] (hc : Nat.card W ≤ 4)
    (f : A →* MulAut W) : f = 1 := by
  classical
  let : Fintype W := Fintype.ofFinite W
  have hc' : Fintype.card W ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hc
  let e : W ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le hc')
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm W) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let r := (MulAction.toPermHom (MulAut W) W).comp f
  let := Group.IsPerfect.range r
  have hs : Subsingleton r.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable r.range inferInstance
  apply MonoidHom.ext
  intro a
  apply MulEquiv.ext
  intro w
  have hr : r a = 1 := congrArg Subtype.val (Subsingleton.elim (r.rangeRestrict a) 1)
  exact DFunLike.congr_fun hr w

private theorem blockU_card_four {G : Type*} [Group G] {B : Subgroup G}
    (h : IsAlternatingBlock B 3) : Nat.card (blockU B) = 4 := by
  have hf := InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.alternatingThreeCoverInput B h
  have hm := h.module_card_odd (by decide)
  change Nat.card (blockU B ⧸ blockFixed B) = 4 at hm
  rw [hf] at hm
  exact (Nat.card_congr (QuotientGroup.quotientBot (G := blockU B)).toEquiv).symm.trans hm

/-- A perfect subgroup normalizing an actual A₃-block centralizes it. -/
theorem perfect_centralizes_normalized_three_block {G : Type*} [Group G]
    {B X : Subgroup G} [Group.IsPerfect X]
    (hB : IsAlternatingBlock B 3) (hn : X ≤ normalizer (B : Set G)) :
    X ≤ centralizer (B : Set G) := by
  let := hB.2.1.finite
  have hcard : Nat.card (B ⧸ pCore 2 B) = 3 := by
    obtain ⟨e⟩ := hB.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hcore := core_eq_blockU hB.2.1 hcard
  let f : X →* MulAut B := B.normalizerMonoidHom.comp (inclusion hn)
  have hu := perfect_small_action (le_of_eq (blockU_card_four hB))
    ((MulAut.characteristic (blockU B)).comp f)
  have hq := perfect_small_action (hcard.le.trans (by decide : 3 ≤ 4))
    ((quotientAut (pCore 2 B)).comp f)
  let U := (blockU B).map B.subtype
  have hXU : X ≤ centralizer (U : Set G) := by
    intro x hx
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b, hb, rfl⟩
    have he := congrArg (fun a : X →* MulAut (blockU B) =>
      ((a ⟨x, hx⟩ ⟨b, hb⟩ : B) : G)) hu
    change x * (b : G) * x⁻¹ = (b : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hc : ⁅B, X⁆ ≤ U := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro x hx b hb
    have he := congrArg (fun a : X →* MulAut (B ⧸ pCore 2 B) =>
      a ⟨x, hx⟩ (QuotientGroup.mk' (pCore 2 B) ⟨b, hb⟩)) hq
    simp only [MonoidHom.comp_apply, quotientAut_apply_mk] at he
    change QuotientGroup.mk' (pCore 2 B) (f ⟨x, hx⟩ ⟨b, hb⟩) =
      QuotientGroup.mk' (pCore 2 B) ⟨b, hb⟩ at he
    have hmem := QuotientGroup.eq_iff_div_mem.mp he
    rw [hcore] at hmem
    refine ⟨_, hmem, ?_⟩
    simp only [div_eq_mul_inv]
    rfl
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  exact le_bot_iff.mp ((commutator_mono hc le_rfl).trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hXU)).le)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
