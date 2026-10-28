module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import Theory.GroupTheory.CComponent.OddRadicalNormalizer

/-!
# Centralizers of natural-block Borels

The Borel's nontrivial odd subgroup prevents a centralizing two-group
from moving the C-component. Its induced automorphisms then fix the Borel
pointwise, hence fix the component by the full-cover fixer theorem. The
relative version transports through the literal subgroup of the ambient
component group; no normality in the full ambient group is asserted.

Source: Aschbacher--Smith15.1.21(i), printed pp.1097--1098, the comparison
C_S(B)≤C_S(L) for the S-orbit Borel.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC
open BenderSuzuki.Converse Matrix.ProjectiveSpecialLinearGroup

private theorem natural_core_quotient_simple {L : Type*} [Group L]
    {n : ℕ} (hb : IsL2EvenBlock L n) : IsSimpleGroup (L ⧸ pCore 2 L) := by
  obtain ⟨hn,_,F,_,_,hF,_,r,⟨m⟩,_⟩ := hb
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq4 : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = 2^2 by decide) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let e := m.quotientIso.trans
    (MulEquiv.ofBijective (pi F) ⟨pi_injective,pi_surjective⟩)
  exact e.isSimpleGroup

/-- A two-subgroup centralizing the Borel centralizes the component. The
two-subgroup is not assumed to normalize the component. -/
theorem IsL2EvenBlock.borel_centralizer {G : Type*} [Group G] [Finite G]
    (L Q : Subgroup G) {n : ℕ} (hb : IsL2EvenBlock L n)
    (hL : L.IsCComponent) (hQ : IsPGroup 2 Q) (P : Sylow 2 L) :
    Q ⊓ centralizer ((normalizer (P : Set L)).map L.subtype : Set G) ≤
      centralizer (L : Set G) := by
  let B := (normalizer (P : Set L)).map L.subtype
  let C := Q ⊓ centralizer (B : Set G)
  obtain ⟨D,hDB,ho,hd⟩ := hb.exists_odd_borel_subgroup P
  let E := D.map L.subtype
  have hEB : E ≤ B := map_mono hDB
  have hEodd : Odd (Nat.card E) := by
    rwa [card_map_of_injective L.subtype_injective]
  have hEne : E ≠ ⊥ := fun he => hd ((map_eq_bot_iff_of_injective D L.subtype_injective).mp he)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := natural_core_quotient_simple hb
  have hCN : C ≤ normalizer (L : Set G) :=
    normalizes_cComponent_of_odd_subgroup L C E hL (hQ.to_le inf_le_left) hEodd hEne
      (map_subtype_le _) ((le_centralizer_iff.mp
        (show C ≤ centralizer (E : Set G) from inf_le_right.trans (centralizer_le hEB))).trans
          (Subgroup.centralizer_le_normalizer _))
  intro x hx
  let a := L.normalizerMonoidHom ⟨x,hCN hx⟩
  have ha : a=1 := hb.borel_fixer P a (by
    intro l hl
    apply Subtype.ext
    change x*(l : G)*x⁻¹=(l : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 l (mem_map_of_mem L.subtype hl)).symm)
  intro l hl
  have he := congrArg Subtype.val (DFunLike.congr_fun ha (⟨l,hl⟩ : L))
  change x*l*x⁻¹=l at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The same centralizer comparison for a component relative to H. -/
theorem IsL2EvenBlock.relative_borel_centralizer {G : Type*} [Group G] [Finite G]
    (H L Q : Subgroup G) {n : ℕ} (hb : IsL2EvenBlock L n)
    (hLH : L ≤ H) (hQH : Q ≤ H) (hL : (L.subgroupOf H).IsCComponent)
    (hQ : IsPGroup 2 Q) (P : Sylow 2 L) :
    Q ⊓ centralizer ((normalizer (P : Set L)).map L.subtype : Set G) ≤
      centralizer (L : Set G) := by
  let X := L.subgroupOf H
  let e : X ≃* L := subgroupOfEquivOfLe hLH
  let P' := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hP : (P' : Subgroup X).map e.toMonoidHom = (P : Subgroup L) := by
    change ((P : Subgroup L).map e.symm.toMonoidHom).map e.toMonoidHom = _
    rw [map_map]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id L := by
      apply MonoidHom.ext
      intro l
      exact e.apply_symm_apply l
    rw [he,map_id]
  have hB : ((normalizer (P' : Set X)).map X.subtype).map H.subtype =
      (normalizer (P : Set L)).map L.subtype := by
    have hn := map_equiv_normalizer_eq (P' : Subgroup X) e
    rw [hP] at hn
    change (normalizer (P' : Set X)).map e.toMonoidHom = normalizer (P : Set L) at hn
    rw [←hn,map_map,map_map]
    rfl
  have hc := IsL2EvenBlock.borel_centralizer X (Q.subgroupOf H) (hb.of_mulEquiv e.symm)
    hL hQ.comap_subtype P'
  rintro x ⟨hxQ,hxB⟩ l hl
  have hx : (⟨x,hQH hxQ⟩ : H) ∈ centralizer (X : Set H) := hc ⟨hxQ,by
    intro z hz
    apply Subtype.ext
    exact hxB z (hB ▸ mem_map_of_mem H.subtype hz)⟩
  exact congrArg H.subtype (hx ⟨l,hLH hl⟩ hl)

end CFSG.Quasithin.ChapterC
