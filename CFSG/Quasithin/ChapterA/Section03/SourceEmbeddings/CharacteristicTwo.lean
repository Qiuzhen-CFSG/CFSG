module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.GroupTheory.CComponent.CharacteristicTwo
public import Theory.AtlasPort.LinearGroups.G2.ProperSylowOvergroups

/-!
# Quasisimple smaller components in characteristic-two Sylow overgroups

After restricting the original full Sylow to the containing component,
the join with the smaller local component cannot be proper if all proper
Sylow overgroups have characteristic two. Such an overgroup cannot have a
quasisimple C-component. The actual G₂ carrier discharges this hypothesis
by its proved exhaustive root-parabolic placement and self-centralizing cores.

This is a consumer specialization of A.3.12 for C.5.13, where the smaller
image is PSL₂ in characteristic two. It does not assert the full parabolic
extension list for smaller C-components with nontrivial two-core.

Source: Aschbacher–Smith A.3.12 and C.5.13, printed pp.47–48,163;
GLS III, Theorems 2.3.5 and 2.6.5–2.6.7 for the native G₂ geometry.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A quasisimple smaller local component cannot lie in a proper full-Sylow
overgroup of characteristic two. -/
theorem eq_of_characteristic_two_sylow_overgroups
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B]
    (hproper : ∀ (S : Sylow 2 L) (P : Subgroup L),
      (S : Subgroup L) ≤ P → P ≠ ⊤ →
        centralizer (pCore 2 P : Set P) ≤ pCore 2 P) : B = L := by
  obtain ⟨S, _, hlocal⟩ := exists_local_sylow_restriction T hB hBL hL.subnormal
  let C := B.subgroupOf L
  let J := C ⊔ (S : Subgroup L)
  change (C.subgroupOf J).IsCComponent at hlocal
  have hJ : J = ⊤ := by
    by_contra hne
    let e : C.subgroupOf J ≃* B :=
      (subgroupOfEquivOfLe (show C ≤ J from le_sup_left)).trans
        (subgroupOfEquivOfLe hBL)
    let : Nontrivial (C.subgroupOf J) := (nontrivial_iff_ne_bot _).mpr hlocal.ne_bot
    have hq : IsQuasisimple (C.subgroupOf J) :=
      IsQuasisimple.of_surjective e.symm.toMonoidHom e.symm.surjective
    exact hlocal.not_isQuasisimple_of_characteristic_two
      (hproper S J le_sup_right hne) hq
  rw [hJ] at hlocal
  have hC : C.IsCComponent := by
    have h := hlocal.map_subtype (show (⊤ : Subgroup L).IsSubnormal from .top)
    simpa only [map_subgroupOf_eq_of_le le_top] using h
  exact le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hC))

/-- The native G₂ proper-Sylow-overgroup theorem excludes a proper
quasisimple smaller local component. -/
theorem eq_of_g2_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : L ≃* Atlas.G2.Model F) : B = L := by
  apply eq_of_characteristic_two_sylow_overgroups T hB hL hBL
  intro S P hSP hne
  have him : P.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [he, map_top_of_surjective _ e.surjective]
  have hc := Atlas.G2.ProperSylowOvergroups.centralizer_twoCore_le
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    (P.map e.toMonoidHom) (map_mono hSP) him
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap P)).mpr hc

/-- The model predicate used by the actual earlier Theorem C catalogue. -/
theorem eq_of_binary_g2_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] {n : ℕ}
    (hmodel : ClassificationModels.IsG2At L (2 ^ n)) : B = L := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact eq_of_g2_containing_component T hB hL hBL e

/-- Literal quotient application: the smaller image is quasisimple, as in
C.5.13, while the containing image has the original Theorem C G₂ model. -/
theorem twoCore_images_eq_of_binary_g2_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple (B.map (QuotientGroup.mk' (pCore 2 G)))] {n : ℕ}
    (hmodel : ClassificationModels.IsG2At (L.map (QuotientGroup.mk' (pCore 2 G))) (2 ^ n)) :
    B.map (QuotientGroup.mk' (pCore 2 G)) =
      L.map (QuotientGroup.mk' (pCore 2 G)) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply eq_of_binary_g2_model
    (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
    ?_ (hL.map_quotient (pCore 2 G)) (map_mono hBL) hmodel
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
