module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Residual
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Alternatives
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# Transporting the actual C.1.34 layers into the Section 15.3 ambient group

The source classification forms Q = [O₂(H),L] inside its MS-group H.
For its actual C-component, the intrinsic core-commutator theorem identifies
this group with [O₂(L),L] after inclusion into the original ambient group.
The same inclusion preserves the center layer exactly.

An injective homomorphism transports a `LayerModel` together with its lower
normal subgroup, quotient isomorphism and actual conjugation formula. The
actor identification changes by the induced isomorphism on L/O₂(L). Thus
natural and dual layers transported by the same embedding retain a common
quotient marking; no abstract group-family tag replaces their actions.

Source: Aschbacher–Smith, C.1.34(1)–(3), printed pp.136–137, as used in
15.3.23, printed pp.1128–1129 (combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
variable {G : Type*} [Group G] [Finite G]

/-- The C.1.34 ambient commutator, included into G, is the actual Q. -/
theorem sourceQ_map_subtype {L H : Subgroup G} (hLH : L ≤ H)
    (hL : (L.subgroupOf H).IsCComponent) :
    (sourceQ (L.subgroupOf H)).map H.subtype = commutatorCore L := by
  rw [sourceQ, ← component_core_commutator_eq _ hL]
  change ((⁅pCore 2 (L.subgroupOf H), (⊤ : Subgroup (L.subgroupOf H))⁆).map
    (L.subgroupOf H).subtype).map H.subtype = _
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  change (⁅(L.subgroupOf H).pCoreIn 2, L.subgroupOf H⁆).map H.subtype = _
  rw [map_commutator, map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hLH]

/-- The actual center of Q, in the original ambient group. -/
def coreCenter (L : Subgroup G) : Subgroup G :=
  (center (commutatorCore L)).map (commutatorCore L).subtype

/-- The center layer in C.1.34 maps to Z(Q), with the same Q as in 15.3.23. -/
theorem sourceCenter_map_subtype {L H : Subgroup G} (hLH : L ≤ H)
    (hL : (L.subgroupOf H).IsCComponent) :
    (sourceCenter (L.subgroupOf H)).map H.subtype = coreCenter L := by
  rw [sourceCenter, map_subgroup_center_eq _ H.subtype_injective,
    sourceQ_map_subtype hLH hL]
  rfl

omit [Finite G] in
/-- Reidentify the component quotient after an injective ambient embedding. -/
noncomputable def embeddedQuotient {D T : Type*} [Group D] [Group T]
    (f : D →* G) (hf : Function.Injective f) (L : Subgroup D)
    (e : (L ⧸ pCore 2 L) ≃* T) : ((L.map f) ⧸ pCore 2 (L.map f)) ≃* T :=
  (QuotientGroup.congr _ _ (L.equivMapOfInjective f hf)
    (pCore_map_iso 2 (L.equivMapOfInjective f hf))).symm.trans e

omit [Finite G] in
/-- Transport a whole literal layer, including its quotient and conjugation
action, along a faithful ambient embedding. -/
noncomputable def embedLayer {D F T V : Type*} [Group D] [Field F] [Group T]
    [AddCommGroup V] [Module F V] (f : D →* G) (hf : Function.Injective f)
    {L A B : Subgroup D} {e : (L ⧸ pCore 2 L) ≃* T}
    {ρ : Representation F T V} (m : LayerModel L A B e ρ) :
    LayerModel (L.map f) (A.map f) (B.map f) (embeddedQuotient f hf L e) ρ := by
  let eA := A.equivMapOfInjective f hf
  let eL := L.equivMapOfInjective f hf
  have hB : (B.subgroupOf A).map eA.toMonoidHom = (B.map f).subgroupOf (A.map f) := by
    apply map_injective (A.map f).subtype_injective
    calc
      ((B.subgroupOf A).map eA.toMonoidHom).map (A.map f).subtype =
          ((B.subgroupOf A).map A.subtype).map f := by rw [map_map, map_map]; rfl
      _ = B.map f := by rw [map_subgroupOf_eq_of_le m.lower_le]
      _ = ((B.map f).subgroupOf (A.map f)).map (A.map f).subtype :=
        (map_subgroupOf_eq_of_le (map_mono m.lower_le)).symm
  let _ := m.lower_normal
  let _ : ((B.map f).subgroupOf (A.map f)).Normal :=
    hB ▸ m.lower_normal.map eA.toMonoidHom eA.surjective
  let qA := QuotientGroup.congr (B.subgroupOf A) ((B.map f).subgroupOf (A.map f)) eA hB
  let qL := QuotientGroup.congr (pCore 2 L) (pCore 2 (L.map f)) eL (pCore_map_iso 2 eL)
  have hn : L.map f ≤ normalizer (A.map f : Set G) :=
    (map_mono m.normalized).trans (A.le_normalizer_map f)
  refine {
    lower_le := map_mono m.lower_le
    normalized := hn
    lower_normal := inferInstance
    quotientIso := qA.symm.trans m.quotientIso
    intertwining := ?_ }
  intro l' a'
  obtain ⟨l, rfl⟩ := eL.surjective l'
  obtain ⟨a, rfl⟩ := eA.surjective a'
  have hconj : layerConjugate (L.map f) (A.map f) hn (eL l) (eA a) =
      eA (layerConjugate L A m.normalized l a) := by
    apply Subtype.ext
    change f l * f a * (f l)⁻¹ = f ((l : D) * (a : D) * (l : D)⁻¹)
    simp only [map_mul, map_inv]
  have hqA (a : A) : qA.symm (QuotientGroup.mk' _ (eA a)) = QuotientGroup.mk' _ a := by
    rw [← QuotientGroup.congr_mk' _ _ eA hB]
    exact qA.symm_apply_apply _
  have hqL (l : L) : qL.symm (QuotientGroup.mk' _ (eL l)) = QuotientGroup.mk' _ l := by
    rw [← QuotientGroup.congr_mk' _ _ eL (pCore_map_iso 2 eL)]
    exact qL.symm_apply_apply _
  rw [hconj]
  change Multiplicative.toAdd (m.quotientIso (qA.symm (QuotientGroup.mk' _ _))) =
    ρ (e (qL.symm (QuotientGroup.mk' _ _)))
      (Multiplicative.toAdd (m.quotientIso (qA.symm (QuotientGroup.mk' _ _))))
  rw [hqA, hqA, hqL]
  exact m.intertwining l a

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
end
