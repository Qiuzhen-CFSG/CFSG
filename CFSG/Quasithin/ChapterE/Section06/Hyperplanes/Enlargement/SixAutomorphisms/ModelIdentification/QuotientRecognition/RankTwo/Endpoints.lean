module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Action
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# The two small derived endpoints in the rank-two catalogue

The actual quotient contains an embedded A₆ and has order strictly greater
than 360. The polar equivalence identifies PSp₄(2)' with A₆, excluding that
endpoint. The embedded A₆ also forces divisibility by 360, whereas the full
octonion automorphism group G₂(2) has order 12096. This excludes its derived
subgroup without requiring an unrelated identification with PSU₃(3).

Source: Aschbacher–Smith, Theorem C and Remark A.2.4, printed p.33, and
E.6.23, printed p.254 (PDF p.265), combined manuscript of 1 March 2004.
The concrete model equivalence and order formula come from the attributed
imports above.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G} {g : G}

omit [Finite G] in
/-- Lagrange applies to the actual faithful A₆ embedding downstairs. -/
theorem six_card_dvd_quotient
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    360 ∣ Nat.card (Y ⧸ center Y) := by
  have hd := Subgroup.card_dvd_of_injective
    ((QuotientGroup.mk' (center Y)).comp (inclusion hY.proper.le))
    (six_quotient_embedding_injective d hY)
  obtain ⟨e⟩ := d.six.model
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd
  norm_num at hd ⊢
  exact hd

/-- The small projective symplectic derived carrier has exactly order 360. -/
theorem not_symplectic_derived
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    (e : (Y ⧸ center Y) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : False := by
  let e₆ := e.trans
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  have hc := quotient_card_gt_six d hY
  rw [Nat.card_congr e₆.toEquiv, nat_card_alternatingGroup] at hc
  norm_num at hc

omit [Finite G] in
/-- The small G₂ derived carrier lies in a group whose order has no factor five. -/
theorem not_g2_derived
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    (e : (Y ⧸ center Y) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hd : Nat.card (Y ⧸ center Y) ∣ Nat.card (Atlas.G2.Model (ZMod 2)) := by
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hh := (six_card_dvd_quotient d hY).trans hd
  rw [Atlas.G2.card_Model] at hh
  norm_num at hh

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
