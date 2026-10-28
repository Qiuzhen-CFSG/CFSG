module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.CubicResidual
public import Theory.SpecificGroups.Alternating.SevenComponent.SylowGeometry
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The normalized A₄ in the literal cubic preimage

The original marked seven-letter action identifies the cubic preimage with
the ambient two-core joined to the lifted cubic complement. Its actual
two-residual is A₄, has full cubic image, and is normalized by the given
two-group through characteristicity. This is the subgroup Y used in the
ordinary A₇ exclusion of C.1.29, printed p.134.
-/
public section
open Subgroup
open BinaryPermutation.SevenCubic
namespace CFSG.Quasithin.ChapterC.LocalC129
variable {G : Type*} [Group G] [Finite G]

/-- The marked cubic preimage has an actual A₄ residual normalized by the
original two-group, and its image is the full cubic subgroup. -/
theorem cubic_preimage_four {K : Subgroup G} (hK : IsBlock K)
    (rho : alternatingGroup (Fin 7) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 7))))
    (model : BlockModuleModel K rho)
    (hact : ∀ (g : alternatingGroup (Fin 7)) (v : Multiplicative (BinaryPermutation.natural (Fin 7))),
      (rho g v).toAdd = BinaryPermutation.naturalRepresentation (Fin 7) g.val v.toAdd)
    (f : G →* Equiv.Perm (Fin 7))
    (hf : ∀ k : K, f k = (model.quotientIso (QuotientGroup.mk' (pCore 2 K) k)).val)
    (hk : f.ker = pCore 2 G)
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hr : GorensteinWalter.d8rho ∈ P.map f) :
    ∃ Y : Subgroup G, Y ≤ C.comap f ∧
      Nonempty (Y ≃* alternatingGroup (Fin 4)) ∧
      P ≤ normalizer (Y : Set G) ∧ Y.map f = C := by
  obtain ⟨X, hX, himage, hres⟩ := exists_cubic_residual_of_model hK rho model hact
  have hXm : (X.map K.subtype).map f = C := by
    rw [map_map]
    have he : f.comp K.subtype = (alternatingGroup (Fin 7)).subtype.comp
        (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) :=
      MonoidHom.ext hf
    rwa [he]
  let H := C.comap f
  have hH : H = pCore 2 G ⊔ X.map K.subtype := by
    change C.comap f = _
    rw [← hXm, comap_map_eq, hk, sup_comm]
  have he : Nonempty (pResidual 2 H ≃* alternatingGroup (Fin 4)) := by
    rwa [hH]
  let Y := (pResidual 2 H).map H.subtype
  have hYm : Y.map f = C := by
    have hHC : H.map f = C := by
      apply map_comap_eq_self
      rw [← hXm]
      exact map_le_range f (X.map K.subtype)
    have hCres : pResidual 2 C = ⊤ := by
      apply top_unique
      intro c _
      apply mem_pResidual_of_orderOf_coprime
      have hc : Nat.Coprime 2 (Nat.card C) := by rw [card_actor]; decide
      exact hc.of_dvd_right (_root_.orderOf_dvd_natCard c)
    change ((pResidual 2 H).map H.subtype).map f = C
    rw [map_embedded_pResidual, hHC, hCres, ← MonoidHom.range_eq_map, range_subtype]
  have hPH : P ≤ normalizer (H : Set G) :=
    (map_le_iff_le_comap.mp
      (alternatingGroup.SevenComponent.normalizes_cubic_of_rho_mem (P.map f) (hP.map f) hr)).trans
      (le_normalizer_comap f)
  refine ⟨Y, map_subtype_le _, ?_, ?_, hYm⟩
  · obtain ⟨e⟩ := he
    exact ⟨((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm.trans e⟩
  · exact hPH.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
end CFSG.Quasithin.ChapterC.LocalC129
