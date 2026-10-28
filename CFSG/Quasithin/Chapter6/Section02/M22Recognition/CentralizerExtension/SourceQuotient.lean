module
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.SourcePlane
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.Normalized
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.QuotientCore
public import Theory.GroupTheory.SylowKernelCore

/-!
# The source centralizer construction from its marked quotient

The original Hypothesis 6.1.1 supplies normalization of L by T. It also
makes the moved layer a two-group. The compatible symmetric-five quotient
therefore proves that this layer equals O₂(L), and normalization gives the
actual Sylow intersection T ∩ L. These remove the separate block and
core-equality premises from the source centralizer construction.

The remaining inputs are the natural-layer reduction 6.1.27, the marked
symmetric-five quotient, and the specific extraspecial-core and orbit
geometry. The result constructs the actual normal elementary sixteen in
H = C_G(z) and its symmetric-four quotient; global M₂₂ recognition remains
separate. Source: Aschbacher–Smith, 6.2.13, printed pp.687–688.
-/
public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
open Source
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M V₀ : Subgroup G} {n : ℕ}

/-- Restrict the already marked quotient to the original local subgroup. -/
theorem source_layer_eq_core_of_compatible_quotient
    (h611 : Hypothesis611 κ T L M V₀ n)
    [((layer L V₀).subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient ((layer L V₀).subgroupOf M) (L.subgroupOf M)) :
    layer L V₀ = L.pCoreIn 2 := by
  let : IsElementaryAbelian 2 V₀ := h611.V_mem.2.1
  have hp : IsPGroup 2 (layer L V₀) :=
    (IsElementaryAbelian.isPGroup 2 V₀).to_le h611.layer_le_V
  have he := congrArg (fun B : Subgroup M => B.map M.subtype)
    (hq.kernel_eq_layer_twoCore hp.comap_subtype)
  rwa [map_subgroupOf_eq_of_le (h611.layer_le_L.trans h611.L_le),
    map_pCoreIn_of_injective 2 _ _ M.subtype_injective,
    map_subgroupOf_eq_of_le h611.L_le] at he

/-- Use the actual Z_S from Hypothesis 6.1.1. Its cardinality, elementary
structure and ambient identification are constructed rather than assumed. -/
theorem source_centralizer_extension_of_marked_reduction
    (h611 : Hypothesis611 κ T L M V₀ n)
    (h6127 : Conclusion6127 (T : Subgroup G) L M V₀ n)
    (H : Subgroup G) (z : G) (hH : H = centralizer ({z} : Set G))
    (hTH : (T : Subgroup G) ≤ H)
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
  have hTL : (T : Subgroup G) ≤ normalizer (L : Set G) :=
    h611.sylow_le.trans ((normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal)
  have hcore := source_layer_eq_core_of_compatible_quotient h611 hq
  exact source_centralizer_extension_of_normalizes H M L (layer L V₀) z hH T
    h611.sylow_le h611.L_le hTH hTL hcore h6127.2.1 hq P S hP ha hS hZS hSP
    hPT hSdef (hbranch.trans hSdef.symm) d hdL hdT hd (hPP.trans hSdef.symm)

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
