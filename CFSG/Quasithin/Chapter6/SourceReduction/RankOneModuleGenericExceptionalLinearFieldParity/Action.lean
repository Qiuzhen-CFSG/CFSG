module
public import CFSG.Quasithin.ChapterF.Section08
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.Representation.BinaryConjugationSection.QuotientActor
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# The original F.8 quotient action and its two critical-pair kernels

The F.8.2 kernel identity constructs a faithful representation of H/O₂(H)
on the actual U/V₁ with its original quotient coordinates. Counting the
fixed coordinate images then identifies centralizer indices with binary
fixed codimensions. V₁ is normal only in the relevant local groups; no
ambient normality is used.

For a critical pair, both D_γ and D_H are exactly intersections with the
opposite local two-cores. Their indices are therefore bounded by the
binary rank of H/O₂(H), and a subgroup of U_γ intersects O₂(H) in a
subgroup centralizing D_H. These are the literal quotient and kernel
steps used in the two terminal branches of 5.1.17.

Source: Aschbacher–Smith, F.8.2, F.8.6–7, printed pp.315–317, and
5.1.17, printed pp.641–642 (`refs/quasithin.pdf`).
-/

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {E : ChapterF.Section08.Setup G} (h : E.Hypothesis)

include h in
theorem point_le_span : E.V₁ ≤ E.U :=
  h.point_le.trans (le_conjugateSpanBy E.V E.H)

include h in
theorem point_normal_in_span : (E.V₁.subgroupOf E.U).Normal :=
  normal_subgroupOf_of_le_normalizer (h.g2.U_le_H.trans h.H_le)

theorem exists_faithful_action :
    let := point_normal_in_span h
    let := ChapterF.Section08.Setup.lemma_F_8_5_two h
    ∃ (ρ : Representation (ZMod 2) E.HStar
        (Additive (E.U ⧸ E.V₁.subgroupOf E.U)))
      (c : Representation.BinaryConjugationSection E.H E.U E.V₁
        (ρ.comp (QuotientGroup.mk' (pCore 2 E.H)))),
      Function.Injective ρ ∧
      ∀ u : E.U, (c.coordinates u).toAdd =
        Additive.ofMul (QuotientGroup.mk' (E.V₁.subgroupOf E.U) u) := by
  let := point_normal_in_span h
  let := ChapterF.Section08.Setup.lemma_F_8_5_two h
  let : IsElementaryAbelian 2 (E.U ⧸ E.V₁.subgroupOf E.U) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  apply Representation.BinaryConjugationSection.exists_faithful_quotient_actor
    E.H E.U E.V₁ h.g2.U_le_H (point_le_span h)
    (le_normalizer_conjugateSpanBy E.V E.H) h.H_le
    (QuotientGroup.mk' (pCore 2 E.H)) (QuotientGroup.mk'_surjective _)
  intro a
  change (a : E.H ⧸ pCore 2 E.H) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, ← h.quotientCentralizer_U_eq_pCore,
    E.mem_quotientCentralizer_iff h.H_le E.U (h.g2.U_le_H.trans h.H_le)]
  constructor <;> intro ha u hu
  · rw [← commutatorElement_inv]
    exact E.V₁.inv_mem (ha u hu)
  · rw [← commutatorElement_inv]
    exact E.V₁.inv_mem (ha u hu)

omit [Finite G] in
theorem quotient_image_card (A : Subgroup G) (hA : A ≤ E.H) :
    Nat.card ((A.subgroupOf E.H).map (QuotientGroup.mk' (pCore 2 E.H))) =
      E.QH.relIndex A := by
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  have he : E.QH.comap E.H.subtype = pCore 2 E.H := by
    exact comap_map_eq_self_of_injective E.H.subtype_injective _
  rw [← he, relIndex_comap, map_subgroupOf_eq_of_le hA]

theorem quotient_image_index_le (A : Subgroup G) (hA : A ≤ E.H)
    [IsElementaryAbelian 2 A] :
    E.QH.relIndex A ≤ 2 ^ primeRank 2 E.HStar := by
  let : IsElementaryAbelian 2 (A.subgroupOf E.H) :=
    IsElementaryAbelian.subgroupOf hA
  let B := (A.subgroupOf E.H).map (QuotientGroup.mk' (pCore 2 E.H))
  have hb : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  rw [← quotient_image_card A hA]
  exact (primeRank_le_iff_elementary_card_le E.HStar).mp le_rfl B hb

include h in
theorem le_core_iff_commutator_le (A : Subgroup G) (hA : A ≤ E.H) :
    A ≤ E.QH ↔ ⁅E.U, A⁆ ≤ E.V₁ := by
  constructor
  · intro ha
    apply commutator_le.mpr
    intro u hu a hmem
    obtain ⟨aH, haH, rfl⟩ := ha hmem
    rw [← h.quotientCentralizer_U_eq_pCore] at haH
    exact (E.mem_quotientCentralizer_iff h.H_le E.U
      (h.g2.U_le_H.trans h.H_le) aH).mp haH u hu
  · intro hc a ha
    have hk : (⟨a, hA ha⟩ : E.H) ∈ E.quotientCentralizer h.H_le E.U :=
      (E.mem_quotientCentralizer_iff h.H_le E.U
        (h.g2.U_le_H.trans h.H_le) _).mpr
        (fun u hu => hc (commutator_mem_commutator hu ha))
    rw [h.quotientCentralizer_U_eq_pCore] at hk
    exact mem_map_of_mem E.H.subtype hk

include h in
open Representation.BinaryOffender in
theorem fixed_index {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E.HStar W)
    (c : Representation.BinaryConjugationSection E.H E.U E.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 E.H))))
    (A : Subgroup G) (hA : A ≤ E.H) :
    (commutatorPreimage E.U A E.V₁).relIndex E.U =
      2 ^ fixedCodim ρ ((A.subgroupOf E.H).map (QuotientGroup.mk' (pCore 2 E.H))) := by
  let : Finite W := Finite.of_surjective (fun u : E.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let σ := ρ.comp (QuotientGroup.mk' (pCore 2 E.H))
  let B := commutatorPreimage E.U A E.V₁
  let F : Subgroup (Multiplicative W) :=
    AddSubgroup.toSubgroup' (fixedSpace σ (A.subgroupOf E.H)).toAddSubgroup
  have hm : (B.subgroupOf E.U).map c.coordinates = F := by
    ext v
    change v.toAdd ∈ c.imageSpace B ↔ v.toAdd ∈ fixedSpace σ (A.subgroupOf E.H)
    rw [c.fixed_image_eq A hA (h.g2.U_le_H.trans h.H_le)]
  have hz : E.V₁ ≤ B := le_commutatorPreimage c.kernel_le
    (le_normalizer_iff_commutator_le_left.mp (hA.trans h.H_le))
  have hk : c.coordinates.ker ≤ B.subgroupOf E.U := by
    rw [c.kernel_eq]
    exact comap_mono hz
  have hi : F.index = B.relIndex E.U := by
    rw [← hm, index_map_eq _ c.onto hk]
    rfl
  have hc := F.card_mul_index
  have hF : Nat.card F = 2 ^ Module.finrank (ZMod 2) (fixedSpace σ (A.subgroupOf E.H)) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace σ (A.subgroupOf E.H))).trans (by rw [Nat.card_zmod])
  have hW : Nat.card (Multiplicative W) = 2 ^ Module.finrank (ZMod 2) W :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)).trans (by rw [Nat.card_zmod])
  rw [hF, hW, ← fixedCodim_add_finrank σ (A.subgroupOf E.H), add_comm, pow_add] at hc
  have he := hi.symm.trans (Nat.eq_of_mul_eq_mul_left (by positivity) hc)
  change B.relIndex E.U = 2 ^ fixedCodim
    (ρ.comp (QuotientGroup.mk' (pCore 2 E.H))) (A.subgroupOf E.H) at he
  unfold fixedCodim at he ⊢
  rw [fixedSpace_comp_map] at he
  exact he

variable {h} (C : h.CriticalPath)

theorem Dg_eq_core_intersection : C.Dg = E.QH ⊓ C.Ug := by
  rw [C.Dg_eq_quotientCentralizer, h.quotientCentralizer_U_eq_pCore]
  rfl

theorem Dg_index_le : C.Dg.relIndex C.Ug ≤ 2 ^ primeRank 2 E.HStar := by
  let := ChapterF.Section08.Setup.lemma_F_8_5_two h
  let : IsElementaryAbelian 2 C.Ug := IsElementaryAbelian.map _
  rw [Dg_eq_core_intersection C, inf_relIndex_right]
  exact quotient_image_index_le C.Ug C.Ug_le_H

theorem kernel_intersection_centralizes (A : Subgroup G) (hA : A ≤ C.Ug) :
    A ⊓ E.QH ≤ centralizer (C.DH : Set G) := by
  have ha : A ⊓ E.QH ≤ C.Dg := by
    rw [Dg_eq_core_intersection C]
    exact le_inf inf_le_right (inf_le_left.trans hA)
  exact ha.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp C.centralizers_commute))

theorem le_endpoint_core_iff (A : Subgroup G) (hA : A ≤ C.vertexGroup C.endpoint) :
    A ≤ (C.vertexGroup C.endpoint).pCoreIn 2 ↔ ⁅C.Ug, A⁆ ≤ C.A₁ := by
  let e : G ≃* G := MulAut.conj (C.g : G)
  have hAH : A.map e.symm.toMonoidHom ≤ E.H := by
    have hh := map_mono (f := e.symm.toMonoidHom) hA
    rw [C.endpointGroup_eq] at hh
    simpa [e, map_map] using hh
  have hk : A.map e.symm.toMonoidHom ≤ E.QH ↔ A ≤ E.QH.map e.toMonoidHom := by
    rw [← map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective]
    simp [map_map]
  have hc : ⁅E.U, A.map e.symm.toMonoidHom⁆ ≤ E.V₁ ↔
      ⁅C.Ug, A⁆ ≤ C.A₁ := by
    rw [← map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective, map_commutator]
    simp [map_map, ChapterF.Section08.Setup.Hypothesis.CriticalPath.Ug,
      ChapterF.Section08.Setup.Hypothesis.CriticalPath.A₁, e]
  rw [C.endpointGroup_eq, AmalgamLocalCores.pCoreIn_map_of_injective 2 _ e.injective]
  exact hk.symm.trans ((le_core_iff_commutator_le h _ hAH).trans hc)

theorem DH_eq_endpoint_core_intersection :
    C.DH = (C.vertexGroup C.endpoint).pCoreIn 2 ⊓ E.U := by
  apply le_antisymm
  · refine le_inf ((le_endpoint_core_iff C C.DH
      ((commutatorPreimage_le _ _ _).trans C.U_le_endpoint)).mpr
      C.centralizer_commutators.1) (commutatorPreimage_le _ _ _)
  · apply le_commutatorPreimage inf_le_right
    rw [commutator_comm]
    exact (le_endpoint_core_iff C _ (inf_le_right.trans C.U_le_endpoint)).mp inf_le_left

theorem DH_index_le : C.DH.relIndex E.U ≤ 2 ^ primeRank 2 E.HStar := by
  let e : G ≃* G := MulAut.conj (C.g : G)
  have hAH : E.U.map e.symm.toMonoidHom ≤ E.H := by
    have hh := map_mono (f := e.symm.toMonoidHom) C.U_le_endpoint
    rw [C.endpointGroup_eq] at hh
    simpa [e, map_map] using hh
  let := ChapterF.Section08.Setup.lemma_F_8_5_two h
  let : IsElementaryAbelian 2 (E.U.map e.symm.toMonoidHom) := IsElementaryAbelian.map _
  have hh := quotient_image_index_le _ hAH
  rw [DH_eq_endpoint_core_intersection C, inf_relIndex_right, C.endpointGroup_eq,
    AmalgamLocalCores.pCoreIn_map_of_injective 2 _ e.injective]
  have he := relIndex_map_map_of_injective (f := e.toMonoidHom) E.QH (E.U.map e.symm.toMonoidHom) e.injective
  simpa [e, ChapterG.Section02.Setup.QH, map_map] using he.le.trans hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
