module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryResidualMovement
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryNaturalFour
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import Theory.GroupTheory.PerfectSylowTwo
public import FeitThompson.FinalTheorem

/-!
# Excluding small block modules on the original doubled orbit

The paired-plane symmetric-three quotient makes the original core Q have
index two in the original Sylow. The residual acts through its cubic image,
so coprime-image splitting makes its order-sixteen commutator disjoint from
the center of a containing block. The literal projection into U(C)/C_U(C)
is therefore injective.

If this block module has order at most sixteen, that projection is onto,
and Q fixes the whole module. Its component Sylow then has image of order
at most two. The action image is nontrivial and perfect because it factors
through the quasisimple intrinsic two-core quotient. The odd-order theorem
and Burnside transfer exclude this small Sylow image.

The Chapter12 SmallBlocks consumer supplies every hypothesis on the same
chosen orbit and lifted component, excluding the exceptional A7 four-space,
natural A6, and single natural binary three- and four-dimensional blocks.
The ordinary six-dimensional A7 module is kept distinct.
Source: Aschbacher--Smith, proof of Proposition 7.7.3 after Lemma 7.7.10,
printed p.709, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySmallBlocks
open ChapterC
variable {G : Type*} [Group G] [Finite G]

private theorem block_action_nontrivial {K : Type*} [Group K]
    (h : IsShort K) (r : K →* MulAut (BlockModule K))
    (hr : ∀ k u, r k (QuotientGroup.mk' (blockFixed K) u) =
      QuotientGroup.mk' (blockFixed K) (blockConjugate K k u)) :
    r ≠ 1 := by
  intro he
  have hc : ⁅blockU K,(⊤ : Subgroup K)⁆ ≤ center K := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro k _ u hu
    have hh := hr k ⟨u,hu⟩
    rw [he] at hh
    have hz := QuotientGroup.eq_iff_div_mem.mp hh.symm
    change k*u*k⁻¹/u ∈ center K at hz
    simpa only [commutatorElement_def,div_eq_mul_inv] using hz
  rw [ExceptionalRestrictions.short_commutator h] at hc
  exact h.irreducible.1.ne (inf_eq_left.mpr hc)

/-- A full order-sixteen subgroup of a short component's module cannot be
fixed by a subgroup of index at most two in its Sylow. -/
theorem small_block_fixed_contradiction
    (C Q : Subgroup G) (P : Sylow 2 G) (hC : C.IsSubnormal)
    (hb : IsShort C) [IsQuasisimple (C ⧸ pCore 2 C)]
    (hindex : Q.relIndex (P : Subgroup G) ≤ 2)
    (D : Subgroup C) (hDU : D ≤ blockU C)
    (hDZ : Disjoint D (center C)) (hD : Nat.card D = 16)
    (hcard : Nat.card (BlockModule C) ≤ 16)
    (hDQ : D ≤ centralizer (Q.subgroupOf C : Set C)) : False := by
  let f : D →* BlockModule C := (QuotientGroup.mk' (blockFixed C)).comp (inclusion hDU)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    have hz : (x : C) ∈ center C := (QuotientGroup.eq_one_iff (inclusion hDU x)).mp hx
    have hx0 : (x : C) ∈ D ⊓ center C := ⟨x.property,hz⟩
    rw [hDZ.eq_bot] at hx0
    exact Subtype.ext (mem_bot.mp hx0)
  have hfs : Function.Surjective f := (hf.bijective_of_nat_card_le (by rw [hD]; exact hcard)).surjective
  obtain ⟨r,hr⟩ := exists_blockModuleAction (L := C)
  have hQker : Q.subgroupOf C ≤ r.ker := by
    intro c hc
    apply MonoidHom.mem_ker.mpr
    ext v
    obtain ⟨d,rfl⟩ := hfs v
    change r c (QuotientGroup.mk' (blockFixed C) (inclusion hDU d)) = _
    rw [hr]
    change QuotientGroup.mk' (blockFixed C) (blockConjugate C c (inclusion hDU d)) =
      QuotientGroup.mk' (blockFixed C) (inclusion hDU d)
    congr 1
    apply Subtype.ext
    change c*(d : C)*c⁻¹ = (d : C)
    rw [hDQ d.property c hc,mul_inv_cancel_right]
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_subnormal C hC
  have hbound : r.ker.relIndex (S : Subgroup C) ≤ 2 := by
    apply le_trans (relIndex_le_of_le_left hQker index_ne_zero_of_finite)
    rw [hS,←inf_subgroupOf_right (P : Subgroup G) C,
      relIndex_subgroupOf (show (P : Subgroup G) ⊓ C ≤ C from inf_le_right)]
    exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hindex
  let s := r.rangeRestrict
  have hs : Function.Surjective s := r.rangeRestrict_surjective
  let R := S.mapSurjective hs
  have hRs : Nat.card R ≤ 2 := by
    change Nat.card ((S : Subgroup C).map s) ≤ 2
    rw [←relIndex_ker]
    simpa only [s,MonoidHom.ker_rangeRestrict] using hbound
  let a : (C ⧸ pCore 2 C) →* r.range := QuotientGroup.lift _ s
    (by simpa only [s,MonoidHom.ker_rangeRestrict] using hb.core_le_moduleAction_ker r hr)
  have has : Function.Surjective a := by
    intro x
    obtain ⟨c,rfl⟩ := hs x
    exact ⟨QuotientGroup.mk' (pCore 2 C) c,rfl⟩
  let : Group.IsPerfect r.range := Group.IsPerfect.ofSurjective has
  have hn : r.range ≠ ⊥ := by
    intro he
    exact block_action_nontrivial hb r hr (MonoidHom.range_eq_bot_iff.mp he)
  let : Nontrivial r.range := (nontrivial_iff_ne_bot r.range).mpr hn
  have heven : Even (Nat.card r.range) := by
    by_contra he
    have ho : Odd (Nat.card r.range) := Nat.not_even_iff_odd.mp he
    exact Group.IsPerfect.not_isSolvable r.range (odd_order_theorem _ ho)
  exact (not_lt_of_ge hRs) (perfect_sylow_two_card_gt_two R heven)

/-- The original residual commutator embeds in the block module, retaining
its full subgroup and the central quotient kernel. -/
theorem residual_block_embedding
    (W A C : Subgroup G) (hC : C.IsSubnormal) (hb : IsShort C)
    (hWcore : W ≤ pCore 2 G) (hAC : A ≤ C)
    (hAW : A ≤ normalizer (W : Set G))
    (hsplit : ⁅W,A⁆ ⊓ (W ⊓ centralizer (A : Set G)) = ⊥) :
    (⁅W,A⁆).subgroupOf C ≤ blockU C ∧
      Disjoint ((⁅W,A⁆).subgroupOf C) (center C) ∧
      ⁅W,A⁆ ≤ C := by
  have hDW : ⁅W,A⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hAW
  have hDU : ⁅W,A⁆ ≤ (blockU C).map C.subtype :=
    (commutator_mono hWcore hAC).trans
      (commutator_le_core_commutator_of_isSubnormal C (pCore 2 G)
        hC hb.twoPerfect pCore_isPGroup le_normalizer_of_normal)
  refine ⟨?_,?_,hDU.trans (map_subtype_le _)⟩
  · intro x hx
    obtain ⟨u,hu,he⟩ := hDU hx
    exact (Subtype.ext he : u=x) ▸ hu
  · apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    have hz : (x : G) ∈ centralizer (A : Set G) := by
      intro a ha
      exact congrArg Subtype.val (mem_center_iff.mp hx.2 ⟨a,hAC ha⟩)
    have hh : (x : G) ∈ ⁅W,A⁆ ⊓ (W ⊓ centralizer (A : Set G)) :=
      ⟨hx.1,hDW hx.1,hz⟩
    rw [hsplit] at hh
    exact Subtype.ext (mem_bot.mp hh)


/-- The original local core has index two in the Sylow, as detected by
its literal symmetric-three quotient. -/
theorem local_sylow_core_index (P : Sylow 2 G) (B Q : Subgroup G)
    (hPB : (P : Subgroup G) ≤ B) (hcore : B.pCoreIn 2 = Q)
    (π : B →* Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hker : ∀ p (hp : p ∈ (P : Subgroup G)), π ⟨p,hPB hp⟩ = 1 → p ∈ Q) :
    Q.relIndex (P : Subgroup G) = 2 := by
  have hQker : Q.subgroupOf B ≤ π.ker := by
    have hQ : Q.subgroupOf B = pCore 2 B := by
      rw [←hcore,pCoreIn]
      exact comap_map_eq_self_of_injective B.subtype_injective _
    rw [hQ]
    apply (Subgroup.map_eq_bot_iff _).mp
    apply le_bot_iff.mp
    rw [←DoubledBinaryPlaneQuotient.twoCore_eq_bot_of_symmetricThree ⟨MulEquiv.refl _⟩]
    exact le_sSup ⟨(inferInstance : (pCore 2 B).Normal).map π hπ,pCore_isPGroup.map π⟩
  have hi : π.ker ⊓ (P : Subgroup G).subgroupOf B =
      Q.subgroupOf B ⊓ (P : Subgroup G).subgroupOf B := by
    ext x
    constructor
    · rintro ⟨hk,hp⟩
      exact ⟨hker x hp hk,hp⟩
    · rintro ⟨hq,hp⟩
      exact ⟨hQker hq,hp⟩
  let S := (P.subtype hPB).mapSurjective hπ
  have hc : Nat.card S = 2 := by
    rw [S.card_eq_multiplicity]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial,Nat.factorization]
    rw [show 6 = 2*3 from rfl,padicValNat.mul (by decide) (by decide),
      padicValNat_self,padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
    rfl
  calc
    Q.relIndex (P : Subgroup G) =
        (Q.subgroupOf B).relIndex ((P : Subgroup G).subgroupOf B) :=
      (relIndex_subgroupOf hPB).symm
    _ = π.ker.relIndex ((P : Subgroup G).subgroupOf B) := by
      rw [←inf_relIndex_right,←hi,inf_relIndex_right]
    _ = Nat.card S := relIndex_ker _ π
    _ = 2 := hc

/-- A two-perfect actor detected inside S₃ has coprime image on a binary
orbit, even when the actor itself has even order. -/
theorem residual_coprime_split (W N A : Subgroup G) [IsElementaryAbelian 2 W]
    (hNW : N ≤ normalizer (W : Set G)) (hAN : A ≤ N)
    (π : N →* Equiv.Perm (Fin 3))
    (hk : π.ker = (centralizer (W : Set G)).subgroupOf N)
    (hA : IsPPerfect 2 A) :
    ⁅W,A⁆ ⊓ (W ⊓ centralizer (A : Set G)) = ⊥ := by
  let a := W.normalizerMonoidHom.comp (inclusion (hAN.trans hNW))
  let b := π.comp (inclusion hAN)
  have he : a.ker = b.ker := by
    ext x
    change inclusion (hAN.trans hNW) x ∈ W.normalizerMonoidHom.ker ↔ inclusion hAN x ∈ π.ker
    rw [normalizerMonoidHom_ker,hk]
    rfl
  have hc : Nat.card a.range = Nat.card b.range :=
    Nat.card_congr (((QuotientGroup.quotientKerEquivRange a).symm.trans
      (QuotientGroup.quotientMulEquivOfEq he)).trans
        (QuotientGroup.quotientKerEquivRange b)).toEquiv
  have hb : b.range ≤ alternatingGroup (Fin 3) := by
    rw [←Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_eq]
    exact le_pResidual_of_isPPerfect _ (hA.of_surjective b.rangeRestrict b.rangeRestrict_surjective)
  have hp3 : IsPGroup 3 (alternatingGroup (Fin 3)) := IsPGroup.of_card (n := 1) (by
    rw [nat_card_alternatingGroup,Nat.card_fin]; rfl)
  have hcop : Nat.Coprime (Nat.card a.range) (Nat.card W) := by
    rw [hc]
    exact IsPGroup.coprime_card_of_ne 3 2 (by decide) b.range W
      (hp3.to_le hb) (IsElementaryAbelian.isPGroup 2 W)
  exact (commutator_centralizer_decomposition_of_coprime_image W A (hAN.trans hNW) hcop).2

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySmallBlocks
