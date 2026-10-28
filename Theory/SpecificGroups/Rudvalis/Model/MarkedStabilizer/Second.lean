module
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.Orbits
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Normalizer
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.Comparison
/-!
# The second native Rudvalis stabilizer is the mixed PSL₂(25)⁺ group

Transport the original point-six stabilizer through the proved full-Ree
marking. Its order15600 invokes the actual full-Ree five-overgroup theorem,
which conjugates it to the marked max4 normalizer. The native semilinear
comparison then identifies the original subgroup with PSL₂(25)⁺.
Source: Aschbacher--Smith J.5.4, pp.445--446.
-/
public section
noncomputable section
namespace Rudvalis.MarkedStabilizer
open Subgroup MulAction Tits.ExceptionalParabolics.FullRee
open FiveOvergroups

/-- The actual second point stabilizer, with no abstract local-type assumption. -/
theorem second_plus :
    Nonempty (stabilizer pointStabilizer (6 : Fin 4060)≃*Tits.Max4Outer.Mixed.Plus) := by
  let J := (stabilizer pointStabilizer (6 : Fin 4060)).map fullEquiv.toMonoidHom
  have hc : Nat.card J=15600 :=
    (card_map_of_injective fullEquiv.injective).trans second_stabilizer_card
  have hD : ¬ D≤J := by
    intro h
    have hd : Nat.card D=17971200 :=
      (Nat.card_congr atlasDerivedEquiv.toEquiv).symm.trans Tits.atlas1600Group_card
    have hle := Nat.card_le_card_of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)
    rw [hd,hc] at hle
    omega
  obtain ⟨_,g,hg⟩ := large_conjugate_normalizer J hD (by rw [hc]; decide) (by rw [hc])
  obtain ⟨e,_,_⟩ := Tits.Max4Outer.Mixed.exists_normalizer_equiv_plus
  exact ⟨(fullEquiv.subgroupMap _).trans
    (((MulAut.conj (atlasEmbedding g)).subgroupMap J).trans
      ((MulEquiv.subgroupCongr hg).trans e))⟩
end Rudvalis.MarkedStabilizer
