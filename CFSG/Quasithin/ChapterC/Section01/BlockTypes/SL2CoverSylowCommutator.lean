module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverCoordinates
public import Theory.Representation.SL2OrthogonalCover.Sylow
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2OddFixed
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# The central layer of a natural block lies in a Sylow commutator

The natural-cover theorem I.2.3(3) places the globally fixed vectors in
all Sylow commutator spaces. Transporting the literal core quotient and
conjugation action gives U(L)∩Z(L)≤[U(L),P], including nonsplit covers.
If P normalizes A and lies in O₂(L)O₂(A), this puts the central layer in
O₂(A). A nontrivial cubic actor then gives U(L)≤O₂(A) by coprime splitting.

Source: Aschbacher–Smith I.2.3(3), applied in original15.3.18, pp.1126–1127.
-/
public section
noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {L : Type*} [Group L] [Finite L]

/-- The actual central layer is contained in the commutator with every
Sylow two-subgroup, even for a nonsplit natural cover. -/
theorem IsL2EvenBlock.central_layer_le_sylow_commutator
    {n : ℕ} (hL : IsL2EvenBlock L n) (P : Sylow 2 L) :
    blockU L ⊓ center L ≤ ⁅blockU L, (P : Subgroup L)⁆ := by
  obtain ⟨hn,hs,F,_,_,hF,_,r,⟨m⟩,hm⟩ := hL
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 (blockU L) := hs.elementary
  let : IsElementaryAbelian 2 (BlockModule L) := hs.module_elementary
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q :=
    m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := P.mapSurjective hq
  let σ := modelCoverAction hs m
  let C := ⁅blockU L, (P : Subgroup L)⁆
  let D : Submodule (ZMod 2) (Additive (blockU L)) :=
    AddSubgroup.toZModSubmodule 2 (C.subgroupOf (blockU L)).toAddSubgroup
  have hker : Coinvariants.ker (σ.comp S.toSubgroup.subtype) ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨s,v⟩,rfl⟩
    obtain ⟨p,hp,he⟩ := s.property
    change q p = s.val at he
    change σ s.val v - v ∈ D
    rw [←he]
    change modelCoverAction hs m (m.quotientIso (QuotientGroup.mk' (pCore 2 L) p)) v - v ∈ D
    rw [modelCoverAction_apply]
    change (p * (v.toMul : L) * p⁻¹) / (v.toMul : L) ∈ C
    rw [div_eq_mul_inv]
    rw [show C = ⁅(P : Subgroup L),blockU L⁆ from commutator_comm _ _]
    exact commutator_mem_commutator hp v.toMul.property
  have hgeom := SL2OrthogonalCover.cover_sylow_geometry n hn hF
    (modelCoverProjection hs m hm) (modelCoverProjection_isCover hs m hm) S
  rintro x ⟨hx,hz⟩
  let v : Additive (blockU L) := Additive.ofMul ⟨x,hx⟩
  have hv : v ∈ fixed σ := by
    intro g
    exact (uRepresentation_fixed hs v).mpr hz (m.quotientIso.symm g)
  exact hker (hgeom.2.1 ▸ hgeom.1 hv)

/-- The Sylow placement and a nontrivial cubic actor force the entire
natural block module into the normalized subgroup's two-core. -/
theorem IsL2EvenBlock.blockU_le_normalized_core
    {n : ℕ} (hL : IsL2EvenBlock L n) (P : Sylow 2 L) (A : Subgroup L)
    (hPA : (P : Subgroup L) ≤ normalizer (A : Set L))
    (hP : (P : Subgroup L) ≤ pCore 2 L ⊔ A.pCoreIn 2)
    (hA : 3^(Nat.card A).factorization 3 = 3) : blockU L ≤ A.pCoreIn 2 := by
  let : IsElementaryAbelian 2 (blockU L) := hL.2.1.elementary
  have hcoreA : pCore 2 L ≤ normalizer (A : Set L) :=
    (pCore_isPGroup.le_sylow_of_normal P).trans hPA
  have hcoreC : pCore 2 L ≤ normalizer (A.pCoreIn 2 : Set L) :=
    hcoreA.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hUC : blockU L ≤ normalizer (A.pCoreIn 2 : Set L) :=
    blockU_le_core.trans hcoreC
  have hcomm : ⁅pCore 2 L ⊔ A.pCoreIn 2, blockU L⁆ ≤ A.pCoreIn 2 := by
    have hpre : pCore 2 L ⊔ A.pCoreIn 2 ≤
        commutatorPreimage (pCore 2 L ⊔ A.pCoreIn 2) (blockU L) (A.pCoreIn 2) := by
      apply sup_le
      · apply le_commutatorPreimage le_sup_left
        rw [commutator_eq_bot_iff_le_centralizer.mpr hL.2.1.core_centralizes_blockU]
        exact bot_le
      · exact le_commutatorPreimage le_sup_right
          (le_normalizer_iff_commutator_le_left.mp hUC)
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (sup_le hcoreC (A.pCoreIn 2).le_normalizer))
  have hcentral : blockU L ⊓ center L ≤ A.pCoreIn 2 :=
    (hL.central_layer_le_sylow_commutator P).trans (by
      rw [commutator_comm]
      exact (commutator_mono hP le_rfl).trans hcomm)
  let T : Sylow 3 A := Classical.choice inferInstance
  let D : Subgroup L := (T : Subgroup A).map A.subtype
  have hDcard : Nat.card D = 3 := by
    rw [card_map_of_injective A.subtype_injective,T.card_eq_multiplicity,hA]
  have hDne : D ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hDcard
    omega
  have hDodd : Odd (Nat.card D) := hDcard ▸ (by decide : Odd 3)
  have hcop : Nat.Coprime (Nat.card D) (Nat.card (blockU L)) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le (blockU_le_core (L := L))).exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hDodd).pow_right k
  have hdec := eq_commutator_sup_centralizer_of_solvable_coprime (blockU L) D
    (by rw [normalizer_eq_top]; exact le_top) inferInstance hcop
  have hUA : blockU L ≤ A := by
    rw [hdec]
    apply sup_le
    · exact (commutator_mono le_rfl (map_subtype_le _)).trans
        (le_normalizer_iff_commutator_le_right.mp (blockU_le_core.trans hcoreA))
    · exact (le_inf inf_le_left (hL.blockU_odd_fixed_le_center D hDodd hDne)).trans
        (hcentral.trans (pCoreIn_le 2 A))
  exact le_pCoreIn_of_normalizes
    (pCore_isPGroup.to_le blockU_le_core) hUA
    (by rw [normalizer_eq_top]; exact le_top)

end CFSG.Quasithin.ChapterC
