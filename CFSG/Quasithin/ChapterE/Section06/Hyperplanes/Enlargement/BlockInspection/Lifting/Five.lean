module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.SourceInputs
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# The genuine A₅ local-family route in E.6.23

An A₅ block is two-perfect with quasisimple two-core quotient, so it is a
C-component, including minimality. The centralizer of the nonidentity
subspace has nontrivial two-core. Together with the common Sylow Q, this
puts the block in the actual family of Definition 1.2.3. The earlier
1.2.4 input then constructs a unique C-component of C_G(A) containing it.

The A₅ type retains its full deleted permutation module. No assertion
about A₃ family membership or block persistence is made. Classification
of the constructed C-component as a block or ordinary component is a
separate step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7,
C.1.12, pp.123–124; 1.2.3–4, p.505; E.6.23, p.254.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting

variable {D : Type*} [Group D]

/-- The order-three clause in the short-group definition cannot occur for
an A₅ block, whose actual two-core quotient has order sixty. -/
theorem alternating_five_quotient_quasisimple
    (h : ChapterC.IsAlternatingBlock D 5) : IsQuasisimple (D ⧸ pCore 2 D) := by
  rcases h.2.1.quotient with hq | hc
  · exact hq
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    have he : Nat.card (D ⧸ pCore 2 D) = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    omega

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- The A₅ alternative supplies a genuine C-component of C_G(U). -/
theorem five_cComponent {U L : Subgroup G} (hL : SmallBlock U L)
    (h5 : ChapterC.IsAlternatingBlock L 5) :
    L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)) := by
  let C := centralizer (U : Set G)
  let e : L ≃* L.subgroupOf C := (subgroupOfEquivOfLe hL.1).symm
  let : IsQuasisimple (L ⧸ pCore 2 L) := alternating_five_quotient_quasisimple h5
  let : IsQuasisimple ((L.subgroupOf C) ⧸ pCore 2 (L.subgroupOf C)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  exact ⟨hL.1, isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    hL.2.1.subnormal hL.2.1.short.twoPerfect⟩

/-- A nonidentity elementary subspace is central in its centralizer and
therefore lies in its two-core. -/
theorem obstruction_centralizer_mem_H
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U : Subgroup G} (hU : U ∈ obstructionFamily M V) :
    centralizer (U : Set G) ∈ Chapter1.H G := by
  let := h.elementary
  let H := centralizer (U : Set G)
  have hUH : U ≤ H := hU.1.trans (V.le_centralizer.trans (Subgroup.centralizer_le hU.1))
  have hcore : U ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le hU.1) hUH (centralizer_le_normalizer _)
  exact fun he => hU.2.1 (le_bot_iff.mp (he ▸ hcore))

/-- The A₅ block belongs to the genuine local C-component family for the
common Sylow subgroup Q. -/
theorem five_mem_localFamily
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U L : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hL : SmallBlock U L) (h5 : ChapterC.IsAlternatingBlock L 5) :
    L ∈ Chapter1.L G (sylowCentralizer (T : Subgroup G) V) :=
  Chapter1.mem_L_of_cComponent (obstruction_centralizer_mem_H h hU)
    (h.sylow_obstruction hU) hL.1 (five_cComponent hL h5).2

/-- Construct the unique containing C-component in the smaller-subspace
centralizer. Only the exact earlier 1.2.4 input remains explicit. -/
theorem exists_unique_cComponent_overgroup_of_five
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (earlier : LocalContainmentInput G)
    {U A L : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U)
    (hL : SmallBlock U L) (h5 : ChapterC.IsAlternatingBlock L 5) :
    ∃! X : Subgroup G, X ∈ Chapter1.cComponentsIn (centralizer (A : Set G)) ∧ L ≤ X := by
  let H := centralizer (A : Set G)
  let Q := sylowCentralizer (T : Subgroup G) V
  have hLH : L ≤ H := hL.1.trans (Subgroup.centralizer_le hAU)
  obtain ⟨S, hS⟩ := (common_sylow h hU hA).2.1
  change (S : Subgroup H).map H.subtype = Q at hS
  have hQH : Q ≤ H := hS ▸ map_subtype_le (S : Subgroup H)
  have hlocal := (Chapter1.mem_LIn_iff_subgroupOf hQH hLH).mp
    ⟨hLH, five_mem_localFamily h hU hL h5⟩
  have hQS : Q.subgroupOf H = (S : Subgroup H) := by
    rw [← hS]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  rw [hQS] at hlocal
  exact (Chapter1.existsUnique_cComponentsIn_iff hLH).mp
    (earlier H (obstruction_centralizer_mem_H h hA) S _ hlocal)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
