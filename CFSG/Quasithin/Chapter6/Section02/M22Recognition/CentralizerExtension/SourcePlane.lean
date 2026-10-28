module
public import CFSG.Quasithin.Chapter6.Section02.NaturalSylowGeometry
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension

/-!
# The canonical source plane in the M₂₂ centralizer construction

The subgroup used in the source is Z_S = C_[V₀,L](T ∩ L), restricted to
H = C_G(z). The original Sylow containment puts it in H. The natural
module output of 6.1.27 and the checked Sylow displacement calculation
supply its elementary structure, order four and literal ambient marking.
These inputs are now discharged in the existing centralizer-extension
construction, whose output is the actual normal elementary sixteen and
symmetric-four quotient in H.

The separate block/core equality, compatible symmetric-five marking,
extraspecial core and orbit geometry remain earlier source obligations.
This is a source application of that construction, not the final ambient
M₂₂ recognition or a proof of 6.1.27.
Source: Aschbacher–Smith, combined manuscript, 6.2.13, printed pp.686–688.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
open Source
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M V₀ : Subgroup G} {n : ℕ}

/-- Use the actual Z_S from Hypothesis 6.1.1. Its cardinality, elementary
structure and ambient identification are constructed rather than assumed. -/
theorem source_centralizer_extension_of_reduction
    (h611 : Hypothesis611 κ T L M V₀ n)
    (h6127 : Conclusion6127 (T : Subgroup G) L M V₀ n)
    (H : Subgroup G) (z : G) (hH : H = centralizer ({z} : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    (hblock : CFSG.Quasithin.ChapterC.IsBlock (L.subgroupOf M))
    (hcore : layer L V₀ = L.pCoreIn 2)
    [((layer L V₀).subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient ((layer L V₀).subgroupOf M) (L.subgroupOf M))
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (ha : NaturalFourOrbit P ((ZS (T : Subgroup G) L V₀).subgroupOf H))
    (hZS : coreCenter P ≤ (ZS (T : Subgroup G) L V₀).subgroupOf H)
    (hSP : (ZS (T : Subgroup G) L V₀).subgroupOf H ≤ P)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    (hbranch : (sourceEight ((ZS (T : Subgroup G) L V₀).subgroupOf H)).map H.subtype ⊓
      layer L V₀ = ZS (T : Subgroup G) L V₀)
    (d : G) (hdL : d ∈ L)
    (hdT : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd : orderOf d = 3)
    (hPP : P.map H.subtype ⊓ (P.map H.subtype).map (MulAut.conj d⁻¹).toMonoidHom =
      ZS (T : Subgroup G) L V₀) :
    let S := (ZS (T : Subgroup G) L V₀).subgroupOf H
    (centralizer (sourceEight S : Set H)).Normal ∧
      IsElementaryAbelian 2 (centralizer (sourceEight S : Set H)) ∧
      Nat.card (centralizer (sourceEight S : Set H)) = 16 ∧
      Nonempty ((H ⧸ centralizer (sourceEight S : Set H)) ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨hZE, hZcard, _⟩ := h611.natural_ZS_geometry h6127
  let : IsElementaryAbelian 2 (ZS (T : Subgroup G) L V₀) := hZE
  have hZH : ZS (T : Subgroup G) L V₀ ≤ H := h611.ZS_le_T.trans hTH
  let S := (ZS (T : Subgroup G) L V₀).subgroupOf H
  let : IsElementaryAbelian 2 S := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hZH).toMonoidHom (subgroupOfEquivOfLe hZH).injective
  have hS : Nat.card S = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv).trans hZcard
  have hSdef : S.map H.subtype = ZS (T : Subgroup G) L V₀ :=
    map_subgroupOf_eq_of_le hZH
  exact source_centralizer_extension H M L (layer L V₀) z hH T
    h611.sylow_le h611.L_le hTH hblock hcore h6127.2.1 hq P S hP ha hS hZS hSP
    hPT hSdef (hbranch.trans hSdef.symm) d hdL hdT hd (hPP.trans hSdef.symm)

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
