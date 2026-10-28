module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.Local
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.Definitions
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action

/-!
# The source intersection core in the unitary exclusion

An element of order five in M acts trivially on the natural orthogonal
module, whose actor has order 72. Hence an element of order five in the
component Borel belongs to the actual M ∩ Mc ∩ I, using Mc = C_G(Z).
Relative normality of L in I makes this local intersection normalize the
component Sylow subgroup. Its two-core contains O₂(M ∩ Mc) ∩ I.

`FiveCoreControl` states the remaining intrinsic Sylow calculation: in a
normalizer containing a five-element from L, the two-core centralizes the
Sylow center. It is an explicit proof obligation, not an assumed source
conclusion. The PSU₃(4) model must supply it and the five-element.

The source core is normal in T. Its nontrivial natural action follows from
the literal residual construction and the oriented plane-generation
hypothesis. The independent orthogonal Sylow calculation must detect that
action on the chosen plane inside S. Trivial plane action always means the
actual conjugation homomorphism `planeAction`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.2(1), 15.3.4, 15.3.7, 15.3.10--12, and 15.3.40,
printed pp.1121--1125 and 1138. The core argument makes explicit the
earlier local information needed by the unitary inference in 15.3.40;
Borel invariance and an S₃ automizer alone are not its hypotheses.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion
variable {G : Type*} [Group G]

private theorem order_five_centralizes {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) {x : G} (hx : x ∈ M)
    (h5 : orderOf x = 5) : x ∈ centralizer (V : Set G) := by
  let a : M := ⟨x, hx⟩
  have ha : orderOf a = 5 := (orderOf_injective M.subtype M.subtype_injective a).symm.trans h5
  have hplane : Nat.card OrthogonalPlaneActor = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hc : Nat.card OrthogonalActor = 72 := by
    rw [RegularWreathProduct.card, hplane]
    norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]
  have ha5 : orderOf (d.actor a) ∣ 5 := ha ▸ orderOf_map_dvd d.actor a
  have ha72 : orderOf (d.actor a) ∣ 72 := hc ▸ orderOf_dvd_natCard (d.actor a)
  have hone : orderOf (d.actor a) = 1 :=
    Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 5 72) ha5 ha72
  have hk : a ∈ d.actor.ker := orderOf_eq_one_iff.mp hone
  rw [d.ker_actor] at hk
  exact hk

/-- Triviality here is triviality of the actual conjugation homomorphism. -/
theorem planeAction_eq_one_iff {H W : Subgroup G}
    (hn : H ≤ normalizer (W : Set G)) :
    planeAction H W hn = 1 ↔ H ≤ centralizer (W : Set G) := by
  rw [← MonoidHom.ker_eq_top_iff, planeAction]
  change W.normalizerMonoidHom.ker.comap (inclusion hn) = ⊤ ↔ _
  rw [normalizerMonoidHom_ker]
  constructor
  · intro h x hx
    have hxk : (⟨x, hx⟩ : H) ∈
        ((centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))).comap
          (inclusion hn) := h ▸ mem_top _
    exact hxk
  · intro h
    apply top_unique
    exact fun x _ => h x.property

/-- The local model obligation, independent of the ambient orthogonal action. -/
def FiveCoreControl (L U W : Subgroup G) : Prop :=
  ∀ K : Subgroup G, K ≤ normalizer (U : Set G) →
    (∃ x : G, x ∈ K ⊓ L ∧ orderOf x = 5) →
    K.pCoreIn 2 ≤ centralizer (W : Set G)

/-- A central intersection core would make the actual residual central too. -/
theorem residual_centralizes_of_core_centralizes
    {M Mc V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hc : (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    residualY M Mc ≤ centralizer (V : Set G) := by
  have hker : ((M ⊓ Mc).pCoreIn 2).subgroupOf M ≤ d.actor.ker := by
    rw [d.ker_actor]
    exact fun x hx => hc hx
  have hcl := normalClosure_le_normal hker
  rintro x ⟨y, hy, rfl⟩
  have hyk := hcl (map_subtype_le _ hy)
  rw [d.ker_actor] at hyk
  exact hyk

/-- The oriented plane generation already forces the source core to act
nontrivially on V; no independent noncentral-core hypothesis is necessary. -/
theorem core_not_centralizing_of_plane_generation
    (d : CharacteristicTwo.LocalData G) (L : Subgroup G)
    (i : OrthogonalPlaneIndex)
    (hgen : ⁅d.V, componentFactor d.Yplus L⁆ = d.action.plane i) :
    ¬ (d.M ⊓ d.Mc).pCoreIn 2 ≤ centralizer (d.V : Set G) := by
  intro hc
  have hY := residual_centralizes_of_core_centralizes d.action hc
  have hplus : d.Yplus ≤ d.Y := by
    rcases d.choice with h | ⟨_, h⟩
    · exact h.le
    · rw [h]
      exact (map_subtype_le _).trans inf_le_left
  have hfac : componentFactor d.Yplus L ≤ centralizer (d.V : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans (hplus.trans hY))
  have he : d.action.plane i = ⊥ := hgen.symm.trans
    ((commutator_comm _ _).trans (commutator_eq_bot_iff_le_centralizer.mpr hfac))
  have hcard := d.action.card_plane i
  rw [he] at hcard
  norm_num at hcard

/-- The genuine intersection core remains normal in the local intersection. -/
theorem intersection_core_le_local_core (M Mc I : Subgroup G) :
    (M ⊓ Mc).pCoreIn 2 ⊓ I ≤ ((M ⊓ Mc) ⊓ I).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes
  · exact (isPGroup_pCoreIn 2 (M ⊓ Mc)).to_le inf_le_left
  · exact inf_le_inf_right I (pCoreIn_le 2 (M ⊓ Mc))
  · apply le_normalizer_inf
    · exact inf_le_left.trans ((M ⊓ Mc).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (M ⊓ Mc) (pCore 2 (M ⊓ Mc : Subgroup G))))
    · exact inf_le_right.trans I.le_normalizer

/-- The actual Mc makes T normalize its intersection core, which lies in T. -/
theorem intersection_core_sylow_data
    (d : CharacteristicTwo.LocalData G)
    (hMc : d.Mc = centralizer (d.Z : Set G)) :
    (d.M ⊓ d.Mc).pCoreIn 2 ≤ (d.T : Subgroup G) ∧
      (d.T : Subgroup G) ≤ normalizer ((d.M ⊓ d.Mc).pCoreIn 2 : Set G) := by
  have hTMc : (d.T : Subgroup G) ≤ d.Mc := by
    rw [hMc]
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow d.T hz t ht).symm
  refine ⟨Chapter14.SourcePreliminaries.intersectionCore_le_sylow
    d.M d.Mc d.T d.sylow_le hTMc, ?_⟩
  exact (le_inf d.sylow_le hTMc).trans ((d.M ⊓ d.Mc).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (d.M ⊓ d.Mc)
      (pCore 2 (d.M ⊓ d.Mc : Subgroup G))))

/-- Normality is relative to I, as in the source. -/
theorem local_normalizes_sylow [Finite G]
    {Yplus S M I L : Subgroup G}
    (h : Candidates.RankOneAction.Setup Yplus S M I L)
    [(L.subgroupOf I).Normal] (hf : RankOneBorelFacts L S) :
    M ⊓ I ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  rw [← h.intersection_twoCore hf]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (M ⊓ L) (pCore 2 (M ⊓ L : Subgroup G)))
  exact le_normalizer_inf (inf_le_left.trans M.le_normalizer)
    (inf_le_right.trans (le_normalizer_of_normal_subgroupOf h.component_le))

/-- An element of order five in the Borel belongs to the actual Mc = C_G(Z). -/
theorem borel_five_mem_local_intersection
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hLI : L ≤ I) (hMc : d.Mc = centralizer (d.Z : Set G))
    (hB : d.M ⊓ L = borel L d.S) {x : G}
    (hx : x ∈ borel L d.S) (hx5 : orderOf x = 5) :
    x ∈ ((d.M ⊓ d.Mc) ⊓ I) ⊓ L := by
  have hxML : x ∈ d.M ⊓ L := hB.symm ▸ hx
  have hxC := order_five_centralizes d.action hxML.1 hx5
  have hZV : d.Z ≤ d.V := le_conjugateSpanBy _ _
  exact ⟨⟨⟨hxML.1, hMc ▸ centralizer_le hZV hxC⟩, hLI hxML.2⟩, hxML.2⟩

/-- The intrinsic five-subgroup calculation forces the source core to
centralize the plane inside I. -/
theorem local_core_centralizes_of_five_control [Finite G]
    (d : CharacteristicTwo.LocalData G) {I L W : Subgroup G}
    (h : Candidates.RankOneAction.Setup d.Yplus d.S d.M I L)
    [(L.subgroupOf I).Normal]
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (hf : RankOneBorelFacts L d.S) (hB : d.M ⊓ L = borel L d.S)
    (hfive : ∃ x : G, x ∈ borel L d.S ∧ orderOf x = 5)
    (hcontrol : FiveCoreControl L (d.S ⊓ L) W) :
    (d.M ⊓ d.Mc).pCoreIn 2 ⊓ I ≤ centralizer (W : Set G) := by
  apply (intersection_core_le_local_core d.M d.Mc I).trans
  apply hcontrol ((d.M ⊓ d.Mc) ⊓ I)
  · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
      (local_normalizes_sylow h hf)
  · obtain ⟨x, hx, hx5⟩ := hfive
    exact ⟨x, borel_five_mem_local_intersection d h.component_le hMc hB hx hx5, hx5⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion
