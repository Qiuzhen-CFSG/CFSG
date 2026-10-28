module

public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Basic
public import Mathlib.GroupTheory.Complement

/-!
# Removing a split central kernel from a perfect subgroup

If a central extension splits over its kernel, every perfect subgroup lies
in the complement. The complement is normal because the kernel is central;
the quotient by the complement is abelian, so it kills the derived subgroup.
Restricting to the preimage of a specified quotient subgroup proves that the
original projection is injective on every perfect subgroup in that preimage.

This is the group-theoretic use of I.2.2(7a) in 16.1.7(3)(i): the preimage
of E(C_{K/Z(K)}(r)) splits over Z(K). To identify L itself with Sz(8), the
source assembly must still supply that splitting, containment in the preimage,
and the identification of the image of L. A quotient centralizer isomorphism
alone supplies none of the splitting hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(7a), p.410, and 16.1.7, p.1173.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic

open Subgroup Theory.GroupTheory

variable {G H : Type*} [Group G] [Group H]

/-- Every perfect subgroup of a split central extension lies in the complement. -/
theorem perfect_le_central_complement (Z D : Subgroup G)
    (hZ : Z ≤ center G) (hsplit : Z.IsComplement' D)
    (L : Subgroup G) [Group.IsPerfect L] : L ≤ D := by
  have hn : (⊤ : Subgroup G) ≤ normalizer D := by
    rw [← hsplit.sup_eq_top]
    exact sup_le (hZ.trans ((center_le_centralizer (D : Set G)).trans
      (centralizer_le_normalizer (D : Set G))))
      D.le_normalizer
  let : D.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hcomm : IsMulCommutative Z := by
    exact ⟨⟨fun x y => Subtype.ext (mem_center_iff.mp (hZ x.property) y).symm⟩⟩
  have hc : _root_.commutator G ≤ D :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      (by rw [sup_comm]; exact hsplit.sup_eq_top) hcomm
  calc
    L = ⁅L, L⁆ := commutator_eq_self.symm
    _ ≤ _root_.commutator G := commutator_mono le_top le_top
    _ ≤ D := hc

/-- Splitting over the central kernel makes projection injective on a perfect subgroup. -/
theorem injective_on_perfect_of_split_preimage (f : G →* H)
    (hker : f.ker ≤ center G) (J : Subgroup H)
    (D : Subgroup (J.comap f))
    (hsplit : (f.ker.subgroupOf (J.comap f)).IsComplement' D)
    (L : Subgroup G) [Group.IsPerfect L] (hL : L ≤ J.comap f) :
    Function.Injective (f.comp L.subtype) := by
  let I := J.comap f
  let Z := f.ker.subgroupOf I
  have hz : Z ≤ center I := by
    intro z hz
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (mem_center_iff.mp (hker hz) x)
  let := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hL).symm.toMonoidHom) (subgroupOfEquivOfLe hL).symm.surjective
  have hd : L.subgroupOf I ≤ D := perfect_le_central_complement Z D hz hsplit _
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hxi : (⟨x, hL x.property⟩ : I) ∈ Z ⊓ D := ⟨hx, hd x.property⟩
  have he := hsplit.disjoint.eq_bot ▸ hxi
  have hi : (⟨x, hL x.property⟩ : I) = 1 := mem_bot.mp he
  exact Subtype.ext (congrArg (fun z : I => (z : G)) hi)

/-- The quotient projection identifies the perfect subgroup with its actual image. -/
noncomputable def equiv_image_of_split_preimage (f : G →* H)
    (hker : f.ker ≤ center G) (J : Subgroup H)
    (D : Subgroup (J.comap f))
    (hsplit : (f.ker.subgroupOf (J.comap f)).IsComplement' D)
    (L : Subgroup G) [Group.IsPerfect L] (hL : L ≤ J.comap f) : L ≃* L.map f :=
  MulEquiv.ofBijective (f.subgroupMap L) ⟨by
    intro x y he
    exact injective_on_perfect_of_split_preimage f hker J D hsplit L hL
      (congrArg Subtype.val he), f.subgroupMap_surjective L⟩

end CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic

