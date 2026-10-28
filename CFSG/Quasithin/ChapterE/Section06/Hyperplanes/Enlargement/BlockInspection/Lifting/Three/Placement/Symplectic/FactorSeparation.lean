module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic.FixedProducts
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.DisjointCommutingProduct


/-!
# Separation of subnormal blocks in commuting normal factors

Let B be a block of a finite group D of characteristic two, contained in
commuting disjoint normal factors P and R. For either factor's two-core Q,
subnormality and two-perfection give [Q,B] ≤ U(B), and this commutator is
stable under B. Irreducibility of U(B)/C_U(B) makes every such stable normal
subgroup either trivial or all of U(B): a central stable subgroup is trivial,
and a subgroup covering the quotient contains [U(B),B] = U(B).

Disjointness therefore forces one factor's two-core to centralize B.
The multiplication isomorphism P × R ≃ P R constructs the corresponding
coordinate homomorphism from B. Its image centralizes that factor's two-core,
hence is a two-group by inheritance of characteristic two. Two-perfection
kills this image and places B in the other factor.

The argument uses the actual short-group axioms and relative subnormality;
it works for every block, so in particular supplies ThreeFactorSeparation
without an assumed identification of an A₃-block with A₄.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13,
printed pp.123–125, and the block-placement argument in E.6.23, printed p.254.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic
open ChapterC
universe u

private theorem blockU_stable {L : Type*} [Group L] (h : IsShort L) :
    ⁅blockU L, (⊤ : Subgroup L)⁆ = blockU L := by
  let := h.finite
  exact commutator_isPPerfect_idempotent (⊤ : Subgroup L) (pCore 2 L)
    (h.twoPerfect.of_surjective (topEquiv (G := L)).symm.toMonoidHom
      (topEquiv (G := L)).symm.surjective)
    pCore_isPGroup le_normalizer_of_normal

private theorem stable_layer_dichotomy {L : Type*} [Group L] (h : IsShort L)
    (N : Subgroup L) [N.Normal] (hNU : N ≤ blockU L)
    (hstable : ⁅N, (⊤ : Subgroup L)⁆ = N) : N = ⊥ ∨ N = blockU L := by
  let Z := blockU L ⊓ center L
  rcases h.irreducible.2 (N ⊔ Z) inferInstance le_sup_right
      (sup_le hNU inf_le_left) with hlo | hhi
  · left
    have hNZ : N ≤ center L := (le_sup_left.trans hlo.le).trans inf_le_right
    exact hstable.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr hNZ)
  · right
    apply le_antisymm hNU
    rw [← blockU_stable h, ← hhi]
    apply commutator_le.mpr
    intro x hx y _
    obtain ⟨n, hn, z, hz, rfl⟩ := mem_sup_of_normal_left.mp hx
    have hzcomm : ⁅z, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz.2 y).symm
    rw [commutatorElement_mul_left_eq_conj_mul, hzcomm, mul_one, mul_inv_cancel, one_mul]
    exact commutator_le_left N ⊤ (commutator_mem_commutator hn (mem_top y))

/-- The subnormal radical commutator is zero or the whole block layer. -/
private theorem core_action_dichotomy {D : Type*} [Group D] [Finite D]
    (B Q : Subgroup D) (hB : IsBlock B) (hQ : IsPGroup 2 Q)
    (hn : B ≤ normalizer Q) :
    ⁅Q, B⁆ = ⊥ ∨ ⁅Q, B⁆ = (blockU B).map B.subtype := by
  let M := ⁅Q, B⁆
  have hMU : M ≤ (blockU B).map B.subtype :=
    commutator_le_core_commutator_of_isSubnormal B Q hB.subnormal hB.short.twoPerfect hQ hn
  have hMB : M ≤ B := hMU.trans (map_subtype_le _)
  let N := M.subgroupOf B
  let : N.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right Q B)
  have hNmap : N.map B.subtype = M := map_subgroupOf_eq_of_le hMB
  have hNU : N ≤ blockU B := by
    intro b hb
    obtain ⟨c, hc, he⟩ := hMU hb
    exact (Subtype.ext he : c = b) ▸ hc
  have hstable : ⁅N, (⊤ : Subgroup B)⁆ = N := by
    apply map_injective B.subtype_injective
    rw [map_commutator, hNmap, ← MonoidHom.range_eq_map, range_subtype]
    exact commutator_isPPerfect_idempotent B Q hB.short.twoPerfect hQ hn
  rcases stable_layer_dichotomy hB.short N hNU hstable with h | h
  · left
    change M = ⊥
    rw [← hNmap, h, Subgroup.map_bot]
  · right
    change M = _
    rw [← hNmap, h]

/-- Multiplication coordinates kill the component centralizing a self-centralizing core. -/
private theorem placement_of_centralizing_factor_core
    {D : Type*} [Group D] (P R B : Subgroup D)
    (hd : Disjoint P R) (hc : P ≤ centralizer (R : Set D))
    (hBR : B ≤ P ⊔ R) (hB : IsPPerfect 2 B)
    (hR : centralizer (pCore 2 R : Set R) ≤ pCore 2 R)
    (hcomm : ⁅(pCore 2 R).map R.subtype, B⁆ = ⊥) : B ≤ P := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting P R hd hc
  let f : B →* P × R := e.symm.toMonoidHom.comp (inclusion hBR)
  let r : B →* R := (MonoidHom.snd P R).comp f
  have hcoords (b : B) : (f b).1.val * (f b).2.val = (b : D) := by
    have hh := congrArg Subtype.val (e.apply_symm_apply (inclusion hBR b))
    exact (he (f b).1 (f b).2).symm.trans hh
  have hr (b : B) : r b ∈ pCore 2 R := by
    apply hR
    apply mem_centralizer_iff.mpr
    intro q hq
    apply Subtype.ext
    symm
    change ((f b).2 : D) * (q : D) = (q : D) * ((f b).2 : D)
    have hbq : (b : D) * (q : D) = (q : D) * (b : D) :=
      (commutator_eq_bot_iff_le_centralizer.mp hcomm
        (mem_map_of_mem R.subtype hq)) b b.property
    have hpq : ((f b).1 : D) * (q : D) = (q : D) * ((f b).1 : D) :=
      (hc (f b).1.property q q.property).symm
    apply mul_left_cancel (a := ((f b).1 : D))
    calc
      _ = (b : D) * (q : D) := by rw [← mul_assoc, hcoords]
      _ = (q : D) * (b : D) := hbq
      _ = ((f b).1 : D) * ((q : D) * ((f b).2 : D)) := by
        rw [← hcoords, ← mul_assoc, ← hpq, mul_assoc]
  let r' : B →* pCore 2 R := r.codRestrict _ hr
  have hr' := hB.hom_eq_one_of_isPGroup pCore_isPGroup r'
  intro b hb
  have hrb : ((f ⟨b, hb⟩).2 : D) = 1 :=
    congrArg (fun k : B →* pCore 2 R => ((k ⟨b, hb⟩ : R) : D)) hr'
  have hp := (f ⟨b, hb⟩).1.property
  have hcb := hcoords ⟨b, hb⟩
  rw [hrb, mul_one] at hcb
  exact Eq.mp (congrArg (fun d : D => d ∈ P) hcb) hp

/-- A subnormal short group contained in two commuting disjoint normal factors
of a characteristic-two group lies in one factor. -/
theorem block_factor_separation {D : Type u} [Group D] [Finite D]
    (hD : generalizedFitting D = pCore 2 D) (P R B : Subgroup D)
    [P.Normal] [R.Normal] (hd : Disjoint P R) (hc : ⁅P, R⁆ = ⊥)
    (hB : IsBlock B) (hle : B ≤ P ⊔ R) : B ≤ P ∨ B ≤ R := by
  have hself : centralizer (pCore 2 D : Set D) ≤ pCore 2 D := by
    simpa only [hD] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := D))
  let QP := (pCore 2 P).map P.subtype
  let QR := (pCore 2 R).map R.subtype
  let : QP.Normal := ConjAct.normal_of_characteristic_of_normal
  let : QR.Normal := ConjAct.normal_of_characteristic_of_normal
  have hQP : IsPGroup 2 QP := pCore_isPGroup.map _
  have hQR : IsPGroup 2 QR := pCore_isPGroup.map _
  rcases core_action_dichotomy B QP hB hQP le_normalizer_of_normal with hzero | hfull
  · right
    exact placement_of_centralizing_factor_core R P B hd.symm
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
      (hle.trans_eq (sup_comm P R)) hB.short.twoPerfect
      (normal_core_selfCentralizing hself P) hzero
  · left
    have hUP : (blockU B).map B.subtype ≤ P :=
      hfull ▸ (commutator_le_left QP B).trans (map_subtype_le _)
    have hRQ : ⁅QR, B⁆ = ⊥ := by
      apply le_bot_iff.mp
      apply (le_inf
        ((commutator_le_core_commutator_of_isSubnormal B QR hB.subnormal
          hB.short.twoPerfect hQR le_normalizer_of_normal).trans hUP)
        ((commutator_le_left QR B).trans (map_subtype_le _))).trans
      exact disjoint_iff_inf_le.mp hd
    exact placement_of_centralizing_factor_core P R B hd
      (commutator_eq_bot_iff_le_centralizer.mp hc) hle hB.short.twoPerfect
      (normal_core_selfCentralizing hself R) hRQ

/-- The unconditional separation predicate consumed by the symplectic assembly. -/
theorem threeFactorSeparation : ThreeFactorSeparation.{u} := by
  intro D _ _ hD P R B hP hR hd hc hB _hthree hle
  let := hP
  let := hR
  exact block_factor_separation hD P R B hd hc hB hle

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic
