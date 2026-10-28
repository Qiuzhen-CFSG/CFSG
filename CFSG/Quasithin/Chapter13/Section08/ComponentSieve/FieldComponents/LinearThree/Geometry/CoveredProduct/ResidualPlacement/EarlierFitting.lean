module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.QuotientActions
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.Representation.HexacodeAction.Cover

/-!
# The literal earlier Fitting residual

The construction is O²(O₂,F(H)), with the Fitting preimage taken under
the actual H → H/O₂(H) map. Its star image is F(H*): the latter has odd
order because O₂(H*) = 1. The concrete cover has center of order three,
so it cannot be the ordinary A₆ carrier, whose center is trivial.
Consequently the three earlier alternatives specialize to 1 or X in the
covered case, without assuming either residual placement or centralization.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.8.14, printed p.951, used in 13.8.21(1), p.957.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

def fittingPreimageResidual (H : Subgroup G) : Subgroup G :=
  residual (((fittingSubgroup (Source.Hstar H)).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype)

theorem fittingPreimageResidual_star (H : Subgroup G) :
    Source.starImage H (fittingPreimageResidual H) = fittingSubgroup (Source.Hstar H) := by
  have hcore : pCore 2 (Source.Hstar H) = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    have he := congrArg (map q) (q.comap_pCore_of_ker_isPGroup
      (QuotientGroup.mk'_surjective _) hk)
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at he
    exact he.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  have hres : pResidual 2 (fittingSubgroup (Source.Hstar H)) = ⊤ := by
    have hc := (pPrimeCore_coprime_card (p := 2) (G := Source.Hstar H)).of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime (hc.of_dvd_right (orderOf_dvd_natCard x))
  rw [fittingPreimageResidual, star_residual H _ (map_subtype_le _)]
  have himage : Source.starImage H
      (((fittingSubgroup (Source.Hstar H)).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype) =
      fittingSubgroup (Source.Hstar H) := by
    unfold Source.starImage subgroupOf
    rw [comap_map_eq_self_of_injective H.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  rw [himage, residual, hres, ← MonoidHom.range_eq_map, range_subtype]

theorem fitting_alternative_image (H L T V₁ : Subgroup G)
    (h : fittingPreimageResidual H = ⊥ ∨ fittingPreimageResidual H = plus L T V₁) :
    fittingSubgroup (Source.Hstar H) = ⊥ ∨
      fittingSubgroup (Source.Hstar H) = Source.starImage H (plus L T V₁) := by
  rw [← fittingPreimageResidual_star H]
  rcases h with h | h
  · left
    simp [h, Source.starImage]
  · exact Or.inr (congrArg (Source.starImage H) h)
omit [Finite G] in
theorem covered_fitting_alternative (H L T V₁ : Subgroup G)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (h : fittingPreimageResidual H = ⊥ ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        fittingPreimageResidual H = one L T V₁) ∨
      fittingPreimageResidual H = plus L T V₁) :
    fittingPreimageResidual H = ⊥ ∨ fittingPreimageResidual H = plus L T V₁ := by
  rcases h with h | ⟨⟨e⟩, _⟩ | h
  · exact Or.inl h
  · have hc := Nat.card_congr (centerCongr (eL.symm.trans e)).toEquiv
    rw [Representation.Hexacode.even_center_card,
      alternatingGroup.center_eq_bot (by simp), card_bot] at hc
    omega
  · exact Or.inr h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
