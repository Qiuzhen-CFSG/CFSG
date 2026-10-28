module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Geometry
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.GroupTheory.ComponentLocalDirectPower

/-!
# Local component orbits for rank-one Borel placement

The stabilizer N_Q(L) preserves the Sylow-normalizer Borel B. The component
orbit theorem therefore makes ⟨B,Q⟩ a group of characteristic two whenever
B has characteristic two, even when Q permutes components. If L is centerless,
every relatively subnormal short subgroup of ⟨B,Q⟩ embeds subnormally in a
finite direct power of B. Thus intrinsic Borel calculations can exclude all
chi-zero blocks, after which the exact E.6.7 decomposition gives B ≤ M.

The final theorem is conditional: the center, characteristic-two and
short-subgroup calculations must be supplied by the actual model branches.
E.6.7 remains an explicit universally quantified earlier source theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
open InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] {T : Sylow 2 G} {M V U L : Subgroup G}

/-- Only the stabilizer of the component must preserve its marked Borel. -/
theorem sylowBorel_stable (S : Sylow 2 L) {Q : Subgroup G}
    (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    Q ⊓ normalizer (L : Set G) ≤ normalizer (sylowBorel S : Set G) := by
  rw [sylowBorel_eq S hS]
  have hN : Q ⊓ normalizer (L : Set G) ≤
      normalizer ((L ⊓ Q : Subgroup G) : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans Q.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf inf_le_right (hN.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

variable [Finite G]

/-- Component orbits permit adjoining Q without assuming Q normalizes L. -/
theorem sylowBorel_adjoin_characteristicTwo
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : HasCharacteristicTwo (sylowBorel S)) :
    HasCharacteristicTwo ↥(sylowBorel S ⊔ sylowCentralizer (T : Subgroup G) V) := by
  apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
  apply hL.2.relative_local_adjoin_centralizer hL.1 (sylowBorel_le S)
    (inf_le_right.trans (Subgroup.centralizer_le hU.1)) (T.isPGroup'.to_le inf_le_left)
    (sylowBorel_stable S hS)
  exact (inf_centralizer_pCoreIn_le_iff 2 _).mpr hB

/-- A relatively subnormal short subgroup embeds into a finite power of the
actual Borel, including when Q permutes the components of C_G(U). -/
theorem short_embedding_in_borel_power
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hZ : center L = ⊥) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (X : Subgroup (sylowBorel S ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G))
    (hs : X.IsSubnormal) (hx : ChapterC.IsShort X) :
    ∃ (k : ℕ) (f : X →* (Fin k → sylowBorel S)),
      Function.Injective f ∧ f.range.IsSubnormal := by
  let H := centralizer (U : Set G)
  let B := sylowBorel S
  let Q := sylowCentralizer (T : Subgroup G) V
  let B' := B.subgroupOf H
  let Q' := Q.subgroupOf H
  have hBH : B ≤ H := (sylowBorel_le S).trans hL.1
  have hQH : Q ≤ H := inf_le_right.trans (Subgroup.centralizer_le hU.1)
  have hinv : Q' ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (B' : Set H) := by
    rw [← subgroupOf_normalizer_eq hL.1, ← subgroupOf_normalizer_eq hBH]
    intro x hx
    exact sylowBorel_stable S hS hx
  have hmap : (B' ⊔ Q').map H.subtype = B ⊔ Q := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBH, map_subgroupOf_eq_of_le hQH]
  let eD := ((B' ⊔ Q').equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  let g := eD.symm.toMonoidHom.comp X.subtype
  have hg : Function.Injective g := eD.symm.injective.comp X.subtype_injective
  have hgs : g.range.IsSubnormal := by
    rw [MonoidHom.range_comp, X.range_subtype]
    exact hs.map eD.symm.surjective
  have hZH : center (L.subgroupOf H) = ⊥ := by
    apply (center (L.subgroupOf H)).eq_bot_iff_forall.mpr
    intro x hx
    have hxL : (subgroupOfEquivOfLe hL.1) x ∈ center L := by
      rw [mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := (subgroupOfEquivOfLe hL.1).surjective y
      exact (map_mul (subgroupOfEquivOfLe hL.1) z x).symm.trans
        ((congrArg (subgroupOfEquivOfLe hL.1) (mem_center_iff.mp hx z)).trans
          (map_mul (subgroupOfEquivOfLe hL.1) x z))
    have he : subgroupOfEquivOfLe hL.1 x = 1 := by simpa only [hZ, mem_bot] using hxL
    exact (subgroupOfEquivOfLe hL.1).injective (he.trans (map_one _).symm)
  obtain ⟨k, f, hf, hfs⟩ := hL.2.local_adjoin_embedding hZH
    (subgroupOf_mono H (sylowBorel_le S)) hinv
    (T.isPGroup'.to_le (show Q ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    hx.twoPerfect g hg hgs
  let E : (Fin k → B') ≃* (Fin k → B) :=
    MulEquiv.piCongrRight (fun _ => subgroupOfEquivOfLe hBH)
  refine ⟨k, E.toMonoidHom.comp f, E.injective.comp hf, ?_⟩
  rw [MonoidHom.range_comp]
  exact hfs.map E.surjective

/-- Intrinsic absence of subnormal short subgroups in Borel powers excludes
the actual relative chi-zero blocks of the intermediate group. -/
theorem sylowBorel_adjoin_noChiZeroBlocks
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hZ : center L = ⊥) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hfree : ∀ k, ∀ X : Subgroup (Fin k → sylowBorel S),
      X.IsSubnormal → ¬ ChapterC.IsShort X) :
    OtherTypes.NoChiZeroBlocks (sylowBorel S ⊔ sylowCentralizer (T : Subgroup G) V) := by
  intro X hXD hs hx
  have hshort := hx.chi.short.of_mulEquiv (subgroupOfEquivOfLe hXD).symm
  obtain ⟨k, f, hf, hfs⟩ := short_embedding_in_borel_power hU hL hZ S hS _ hs hshort
  exact hfree k f.range hfs (hshort.of_mulEquiv (MonoidHom.ofInjective hf))

/-- Conditional local assembly of E.6.8's placement step. The model-specific
center, characteristic-two and short-subgroup premises remain obligations. -/
theorem sylowBorel_le_of_intrinsic
    (h67 : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hZ : center L = ⊥) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : HasCharacteristicTwo (sylowBorel S))
    (hfree : ∀ k, ∀ X : Subgroup (Fin k → sylowBorel S),
      X.IsSubnormal → ¬ ChapterC.IsShort X) : sylowBorel S ≤ M := by
  obtain ⟨d⟩ := h67 U hU _ le_sup_right
    (sup_le ((sylowBorel_le S).trans hL.1)
      (inf_le_right.trans (Subgroup.centralizer_le hU.1)))
    (sylowBorel_adjoin_characteristicTwo hU hL S hS hB)
  exact le_sup_left.trans (OtherTypes.le_of_blockDecomposition d
    (sylowBorel_adjoin_noChiZeroBlocks hU hL hZ S hS hfree))

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
