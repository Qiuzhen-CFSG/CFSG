module

public import Theory.GroupTheory.Amalgam.SymmetricThreePair
public import Mathlib.GroupTheory.Index

/-!
# The dihedral-twelve amalgam over a four-group

The two vertices are `C₂ × S₃`. The middle four-group embeds by the two
opposite coordinate orders, so the central lines of the vertices are distinct.
Normal odd complements extend each middle coordinate to the opposite vertex.
This yields an isomorphism of amalgams, retaining both commuting squares.

Source: Aschbacher–Smith F.6.5(2)(ii), printed p.305.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.RankTwoAmalgam

abbrev DihedralTwelveVertex := swapMiddle × SymmetricThree

def dihedralTwelvePair : RankTwoAmalgam DihedralTwelveVertex
    (swapMiddle × swapMiddle) DihedralTwelveVertex where
  left := (MonoidHom.fst _ _).prod (swapMiddle.subtype.comp (MonoidHom.snd _ _))
  right := (MonoidHom.snd _ _).prod (swapMiddle.subtype.comp (MonoidHom.fst _ _))

private theorem normalize_middle {B : Type*} [Group B]
    (f : B →* SymmetricThree) (hc : Nat.card f.range = 2) :
    ∃ e : SymmetricThree ≃* SymmetricThree, ∃ b : B →* swapMiddle,
      ∀ x, e (f x) = b x := by
  classical
  obtain ⟨t, ht, hunique⟩ := (Nat.card_eq_two_iff' (1 : f.range)).mp hc
  have ht2 : (t : SymmetricThree) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := t)
    rw [hc] at hh
    exact congrArg Subtype.val hh
  have htn : (t : SymmetricThree) ≠ 1 := fun he => ht (Subtype.ext he)
  have conjugate : ∀ x : SymmetricThree, x ≠ 1 → x ^ 2 = 1 →
      ∃ g : SymmetricThree, g * x * g⁻¹ = Equiv.swap 0 1 := by decide +kernel
  obtain ⟨g, hg⟩ := conjugate t htn ht2
  let e := MulAut.conj g
  have he (x : B) : e (f x) ∈ swapMiddle := by
    by_cases hx : f x = 1
    · rw [hx, map_one]; exact swapMiddle.one_mem
    · have hh : (⟨f x, ⟨x, rfl⟩⟩ : f.range) = t :=
        hunique _ (fun h => hx (congrArg Subtype.val h))
      have hfx : f x = t := congrArg Subtype.val hh
      rw [hfx]
      change g * (t : SymmetricThree) * g⁻¹ ∈ swapMiddle
      rw [hg]
      exact mem_zpowers _
  exact ⟨e, (e.toMonoidHom.comp f).codRestrict swapMiddle he, fun _ => rfl⟩

/-- A normal subgroup of coprime order gives a retraction onto any subgroup
whose order is its complementary factor. -/
theorem retraction_of_normal_complement_card {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (i : B →* A) (hi : Function.Injective i)
    (N : Subgroup A) [N.Normal]
    (hcop : Nat.Coprime (Nat.card N) (Nat.card B))
    (hc : Nat.card A = Nat.card N * Nat.card B) :
    ∃ r : A →* B, ∀ b, r (i b) = b := by
  let q := QuotientGroup.mk' N
  let f := q.comp i
  have hir : Nat.card i.range = Nat.card B :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm
  have hd : Disjoint N i.range := disjoint_of_coprime_natCard (by rwa [hir])
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro b hb
    have hbN : i b ∈ N := (QuotientGroup.eq_one_iff (i b)).mp hb
    have hb1 : i b = 1 := disjoint_iff_inf_le.mp hd ⟨hbN, ⟨b, rfl⟩⟩
    exact hi (hb1.trans i.map_one.symm)
  have hquot : Nat.card (A ⧸ N) = Nat.card B := by
    have hh := N.card_mul_index
    rw [hc] at hh
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := N)) hh
  let e := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, hquot.symm⟩)
  refine ⟨e.symm.toMonoidHom.comp q, ?_⟩
  intro b
  exact e.symm_apply_apply b

/-- Recognition with both marked middle embeddings. The two kernels on the
middle group must have trivial intersection. -/
theorem iso_dihedralTwelvePair {A B C : Type*} [Group A] [Group B] [Group C]
    [Finite A] [Finite B] [Finite C] (α : RankTwoAmalgam A B C)
    (fA : A →* SymmetricThree) (fC : C →* SymmetricThree)
    (hA : Nat.card A = 12) (hB : Nat.card B = 4) (hC : Nat.card C = 12)
    (himageA : Nat.card (fA.comp α.left).range = 2)
    (himageC : Nat.card (fC.comp α.right).range = 2)
    (hkerA : fA.ker ≤ α.left.range) (hkerC : fC.ker ≤ α.right.range)
    (hdis : (fA.comp α.left).ker ⊓ (fC.comp α.right).ker = ⊥)
    (rA : A →* B) (hrA : ∀ b, rA (α.left b) = b)
    (rC : C →* B) (hrC : ∀ b, rC (α.right b) = b) :
    Nonempty (Iso α dihedralTwelvePair) := by
  obtain ⟨a, s, hs⟩ := normalize_middle (fA.comp α.left) himageA
  obtain ⟨c, t, ht⟩ := normalize_middle (fC.comp α.right) himageC
  let m := t.prod s
  have hm : Function.Injective m := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro b hb
    have ht1 : t b = 1 := congrArg Prod.fst hb
    have hs1 : s b = 1 := congrArg Prod.snd hb
    have ha1 : fA (α.left b) = 1 := by
      apply a.injective
      rw [a.map_one]
      exact (hs b).trans (congrArg Subtype.val hs1)
    have hc1 : fC (α.right b) = 1 := by
      apply c.injective
      rw [c.map_one]
      exact (ht b).trans (congrArg Subtype.val ht1)
    have : b ∈ (fA.comp α.left).ker ⊓ (fC.comp α.right).ker := ⟨ha1, hc1⟩
    simpa only [hdis, mem_bot] using this
  let em := MulEquiv.ofBijective m ((Nat.bijective_iff_injective_and_card m).mpr
    ⟨hm, by rw [Nat.card_prod, swapMiddle_card, hB]⟩)
  let l := (t.comp rA).prod (a.toMonoidHom.comp fA)
  let r := (s.comp rC).prod (c.toMonoidHom.comp fC)
  have hl : Function.Injective l := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hxA : fA x = 1 := by
      apply a.injective
      exact (congrArg Prod.snd hx).trans a.map_one.symm
    obtain ⟨b, rfl⟩ := hkerA hxA
    change α.left b = 1
    rw [← α.left.map_one]
    apply congrArg α.left
    apply hm
    apply Prod.ext
    · exact (by simpa only [l, MonoidHom.prod_apply, MonoidHom.comp_apply, hrA,
        m, map_one, Prod.fst_one, Prod.snd_one] using congrArg Prod.fst hx)
    · apply Subtype.ext
      exact (hs b).symm.trans (by simp only [MonoidHom.comp_apply, hxA, map_one, Prod.snd_one, Subgroup.coe_one])
  have hr : Function.Injective r := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hxC : fC x = 1 := by
      apply c.injective
      exact (congrArg Prod.snd hx).trans c.map_one.symm
    obtain ⟨b, rfl⟩ := hkerC hxC
    change α.right b = 1
    rw [← α.right.map_one]
    apply congrArg α.right
    apply hm
    apply Prod.ext
    · apply Subtype.ext
      exact (ht b).symm.trans (by simp only [MonoidHom.comp_apply, hxC, map_one, Prod.fst_one, Subgroup.coe_one])
    · exact (by simpa only [r, MonoidHom.prod_apply, MonoidHom.comp_apply, hrC,
        m, map_one, Prod.fst_one, Prod.snd_one] using congrArg Prod.fst hx)
  have hv : Nat.card DihedralTwelveVertex = 12 := by
    rw [Nat.card_prod, swapMiddle_card]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  let el := MulEquiv.ofBijective l ((Nat.bijective_iff_injective_and_card l).mpr
    ⟨hl, hA.trans hv.symm⟩)
  let er := MulEquiv.ofBijective r ((Nat.bijective_iff_injective_and_card r).mpr
    ⟨hr, hC.trans hv.symm⟩)
  refine ⟨⟨⟨el, em, er⟩, ?_, ?_⟩⟩
  · intro b
    apply Prod.ext
    · exact congrArg t (hrA b)
    · exact hs b
  · intro b
    apply Prod.ext
    · exact congrArg s (hrC b)
    · exact ht b
end Theory.GroupTheory.RankTwoAmalgam
