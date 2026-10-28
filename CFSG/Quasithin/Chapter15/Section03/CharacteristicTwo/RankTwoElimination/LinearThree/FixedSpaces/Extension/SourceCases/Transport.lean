module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Layers

/-!
# One marking for the intrinsic and original component quotients

The inclusion L ↪ H identifies the intrinsic copy of L and its two-core
quotient with the original ones. Every actual layer is transported through
the same marking, preserving the lower subgroup and conjugation formula.
The images of the fixed subgroup and natural commutator are identified
with C_Q(L) and [Z(Q),L] in the original ambient group.

Source: Aschbacher–Smith, C.1.34, printed pp.136–137, and 15.3.23,
printed p.1128. These are transport results, not a classification input.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases
variable {G : Type*} [Group G] {L H : Subgroup G}

/-- The actual two-core quotients of the intrinsic and original copies of L. -/
noncomputable def quotientComparison (hLH : L ≤ H) :
    ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* (L ⧸ pCore 2 L) :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hLH))

/-- The original component marking induced by the local classification marking. -/
noncomputable def ambientMarking {T : Type*} [Group T] (hLH : L ≤ H)
    (e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* T) :
    (L ⧸ pCore 2 L) ≃* T := (quotientComparison hLH).symm.trans e

/-- Both markings agree on the same component element. -/
theorem ambientMarking_apply {T : Type*} [Group T] (hLH : L ≤ H)
    (e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* T)
    (l : L.subgroupOf H) :
    ambientMarking hLH e (QuotientGroup.mk (subgroupOfEquivOfLe hLH l)) =
      e (QuotientGroup.mk l) := by
  change e ((quotientComparison hLH).symm _) = _
  have hq : quotientComparison hLH (QuotientGroup.mk l) =
      QuotientGroup.mk (subgroupOfEquivOfLe hLH l) :=
    QuotientGroup.congr_mk' _ _ (subgroupOfEquivOfLe hLH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hLH)) l
  rw [← hq]
  exact congrArg e ((quotientComparison hLH).symm_apply_apply _)

/-- Transport the entire layer and its conjugation action with the common marking. -/
noncomputable def ambientLayer {F T V : Type*} [Field F] [Group T]
    [AddCommGroup V] [Module F V] (hLH : L ≤ H)
    {A B : Subgroup H} {e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* T}
    {ρ : Representation F T V} (m : LayerModel (L.subgroupOf H) A B e ρ) :
    LayerModel L (A.map H.subtype) (B.map H.subtype) (ambientMarking hLH e) ρ := by
  let eA := A.equivMapOfInjective H.subtype H.subtype_injective
  let eL := subgroupOfEquivOfLe hLH
  have hB : (B.subgroupOf A).map eA.toMonoidHom =
      (B.map H.subtype).subgroupOf (A.map H.subtype) := by
    apply map_injective (A.map H.subtype).subtype_injective
    calc
      ((B.subgroupOf A).map eA.toMonoidHom).map (A.map H.subtype).subtype =
          ((B.subgroupOf A).map A.subtype).map H.subtype := by
        rw [map_map, map_map]; rfl
      _ = B.map H.subtype := by rw [map_subgroupOf_eq_of_le m.lower_le]
      _ = ((B.map H.subtype).subgroupOf (A.map H.subtype)).map
          (A.map H.subtype).subtype := (map_subgroupOf_eq_of_le (map_mono m.lower_le)).symm
  let _ := m.lower_normal
  let _ : ((B.map H.subtype).subgroupOf (A.map H.subtype)).Normal :=
    hB ▸ m.lower_normal.map eA.toMonoidHom eA.surjective
  let qA := QuotientGroup.congr _ _ eA hB
  have hn : L ≤ normalizer (A.map H.subtype : Set G) := by
    rw [← map_subgroupOf_eq_of_le hLH]
    exact (map_mono m.normalized).trans (A.le_normalizer_map H.subtype)
  refine {
    lower_le := map_mono m.lower_le
    normalized := hn
    lower_normal := inferInstance
    quotientIso := qA.symm.trans m.quotientIso
    intertwining := ?_ }
  intro l' a'
  obtain ⟨l, rfl⟩ := eL.surjective l'
  obtain ⟨a, rfl⟩ := eA.surjective a'
  have hconj : layerConjugate L (A.map H.subtype) hn (eL l) (eA a) =
      eA (layerConjugate (L.subgroupOf H) A m.normalized l a) := by
    apply Subtype.ext
    rfl
  have hqA (a : A) : qA.symm (QuotientGroup.mk' _ (eA a)) = QuotientGroup.mk' _ a := by
    rw [← QuotientGroup.congr_mk' _ _ eA hB]
    exact qA.symm_apply_apply _
  rw [hconj]
  change Multiplicative.toAdd (m.quotientIso (qA.symm (QuotientGroup.mk' _ _))) =
    ρ (ambientMarking hLH e (QuotientGroup.mk (eL l)))
      (Multiplicative.toAdd (m.quotientIso (qA.symm (QuotientGroup.mk' _ _))))
  rw [hqA, hqA, ambientMarking_apply]
  exact m.intertwining l a

/-- C_Q(L) in the original ambient group, for Q = [O₂(L),L]. -/
def coreFixed (L : Subgroup G) : Subgroup G := commutatorCore L ⊓ centralizer (L : Set G)

/-- The actual commutator [Z(Q),L] in the original ambient group. -/
def coreNatural (L : Subgroup G) : Subgroup G := ⁅coreCenter L, L⁆

/-- The local fixed subgroup maps to precisely C_Q(L). -/
theorem sourceFixed_map [Finite G] (hLH : L ≤ H)
    (hL : (L.subgroupOf H).IsCComponent) :
    (sourceFixed (L.subgroupOf H)).map H.subtype = coreFixed L := by
  apply le_antisymm
  · rintro x ⟨q, ⟨hq, hc⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← sourceQ_map_subtype hLH hL]
      exact mem_map_of_mem H.subtype hq
    · intro l hl
      exact congrArg Subtype.val (hc ⟨l, hLH hl⟩ hl)
  · rintro x ⟨hq, hc⟩
    rw [← sourceQ_map_subtype hLH hL] at hq
    obtain ⟨q, hq, rfl⟩ := hq
    refine ⟨q, ⟨hq, ?_⟩, rfl⟩
    intro l hl
    exact Subtype.ext (hc l hl)

/-- The local natural commutator maps to precisely [Z(Q),L]. -/
theorem sourceNatural_map [Finite G] (hLH : L ≤ H)
    (hL : (L.subgroupOf H).IsCComponent) :
    (sourceNatural (L.subgroupOf H)).map H.subtype = coreNatural L := by
  rw [sourceNatural, map_commutator, sourceCenter_map_subtype hLH hL,
    map_subgroupOf_eq_of_le hLH]
  rfl

/-- Component normalization preserves its characteristic natural commutator. -/
theorem coreNatural_normalized (S : Subgroup G) (hSL : S ≤ normalizer (L : Set G)) :
    S ≤ normalizer (coreNatural L : Set G) := by
  have hSQ := hSL.trans (normalizer_le_normalizer_commutatorCore L)
  have hSZ : S ≤ normalizer (coreCenter L : Set G) :=
    hSQ.trans (normalizer_le_normalizer_characteristic_image (commutatorCore L)
      (center (commutatorCore L)))
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅coreCenter L, L⁆).map (MulAut.conj s).toMonoidHom = coreNatural L
  rw [map_commutator]
  have hz : (coreCenter L).map (MulAut.conj s).toMonoidHom = coreCenter L :=
    mem_normalizer_iff_map_conj_eq.mp (hSZ hs)
  have hl : L.map (MulAut.conj s).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (hSL hs)
  rw [hz, hl]
  rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases
end
