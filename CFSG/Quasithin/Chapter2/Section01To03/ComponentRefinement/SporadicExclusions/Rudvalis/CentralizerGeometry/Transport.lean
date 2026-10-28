module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.CentralizerGeometry.CentralCover
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.CentralizerGeometry.Model
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.PowerCover

/-!
# Lifting the Rudvalis max4 seed through its component orbit

Pull back the prescribed-Sylow max4 seed along the literal O₂(L) quotient map,
then adjoin the supplied S. The stabilizer N_S(L) preserves the seed; the
component-orbit construction handles all other elements of S. Characteristic
two survives the central kernel and the component orbit. The original
involution in S makes the resulting two-core nontrivial.

The orbit base maps onto a finite direct power of the full max4 local, with
two-group kernel and two-group quotient above the base. The component center
is killed because it equals O₂(L). Generation uses the image of genuinely
centralizing lifts, not arbitrary elements fixed only modulo that kernel.

This follows the existing M₁₂ component-orbit transport. The final theorem
applies every geometric construction to the original `LocalSetup` and
`SporadicQuotientInput`, with no remaining local-geometry assumption.
Source: Aschbacher–Smith 2.3.9(7), printed p.526.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry
open Subgroup Theory.GroupTheory Rudvalis Rudvalis.SylowOvergroups
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- All hypotheses of the concrete max4 construction follow from the source input. -/
def transportedSeed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) :
    ModelSeed (modelSylow h d) (modelAut d d.action) := by
  let : IsSimpleGroup Model := model_simple h d
  exact Classical.choice (nonempty_modelSeed (model_center h d)
    (modelSylow h d) (modelAut d d.action) (modelAction_order h d)
    (modelAction_inner d) (modelSylow_fixed h d))

/-- Generation uses the actual image of the original involution centralizer. -/
theorem seed_centralizerImage_sup (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru)
    (s : ModelSeed (modelSylow h d) (modelAut d d.action)) :
    centralizerImage d ⊔ s.localSubgroup = ⊤ := by
  rw [centralizerImage_eq_fixedSubgroup h d]
  exact s.generated

/-- Every normalizer actor preserves the lifted seed, including the entire kernel. -/
theorem seed_normalized (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru)
    (s : ModelSeed (modelSylow h d) (modelAut d d.action)) :
    ((S : Subgroup H).map H.subtype) ⊓ normalizer (L : Set G) ≤
      normalizer (componentPreimage d s.localSubgroup : Set G) := by
  apply componentPreimage_normalized
  intro a ha
  exact s.invariant a (modelActors_preserve_sylow h d a ha)

/-- The full covering seed has a self-centralizing two-core. -/
theorem seed_selfCentralizingCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru)
    (s : ModelSeed (modelSylow h d) (modelAut d d.action)) :
    centralizer (pCore 2 (componentPreimage d s.localSubgroup) :
      Set (componentPreimage d s.localSubgroup)) ≤
        pCore 2 (componentPreimage d s.localSubgroup) := by
  have hi := preimage_selfCentralizingCore h d s.localSubgroup s.selfCentralizing
  let e := (s.localSubgroup.comap (quotientMap d)).equivMapOfInjective
    L.subtype L.subtype_injective
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hi

/-- Characteristic two lifts across the central kernel and the whole component orbit. -/
theorem seed_localOvergroup_even (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru)
    (s : ModelSeed (modelSylow h d) (modelAut d d.action)) :
    localOvergroup ((S : Subgroup H).map H.subtype) d s.localSubgroup ∈ Chapter1.He G := by
  let := h.finite
  exact h.component.relative_local_adjoin_centralizer h.component_le
    (componentPreimage_le d s.localSubgroup) (map_subtype_le _)
    (S.isPGroup'.map H.subtype) (seed_normalized h d s)
    ((inf_centralizer_pCoreIn_le_iff 2 _).mpr (seed_selfCentralizingCore h d s))
/-- Restrict the actual component quotient to the full preimage of P. -/
noncomputable def liftProjection (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : componentPreimage d P →* P :=
  ((quotientMap d).comp (inclusion (componentPreimage_le d P))).codRestrict P (by
    intro x
    rcases x.property with ⟨y, hy, he⟩
    change (y : G) = x.val at he
    have he' : y = inclusion (componentPreimage_le d P) x := Subtype.ext he
    change quotientMap d y ∈ P at hy
    change quotientMap d (inclusion (componentPreimage_le d P) x) ∈ P
    rw [← he']
    exact hy)

/-- The full preimage maps onto the prescribed native subgroup. -/
theorem liftProjection_surjective (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : Function.Surjective (liftProjection d P) := by
  intro p
  obtain ⟨l, hl⟩ := quotientMap_surjective d p.val
  refine ⟨⟨l, ⟨l, ?_, rfl⟩⟩, ?_⟩
  · change quotientMap d l ∈ P
    rw [hl]
    exact p.property
  · apply Subtype.ext
    change quotientMap d l = p.val
    exact hl

/-- The covering two-kernel is retained and is central in the lifted local. -/
theorem liftProjection_ker_central (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) (P : Subgroup Model) :
    (liftProjection d P).ker ≤ center (componentPreimage d P) := by
  intro x hx
  have hk : (⟨x.val, componentPreimage_le d P x.property⟩ : L) ∈ (quotientMap d).ker :=
    by
      change quotientMap d (inclusion (componentPreimage_le d P) x) = 1
      exact congrArg (fun p : P => (p : Model)) hx
  rw [quotientMap_ker] at hk
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (congrArg (fun l : L => (l : G))
    (mem_center_iff.mp (twoCore_le_center h d hk) ⟨y.val, componentPreimage_le d P y.property⟩))

/-- The full component center is killed by the specified quotient map,
because it is precisely the retained two-core. -/
theorem liftProjection_kills_center
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) (x : componentPreimage d P)
    (hx : inclusion (componentPreimage_le d P) x ∈ center L) :
    liftProjection d P x = 1 := by
  rw [center_eq_twoCore h d, ← quotientMap_ker d] at hx
  apply Subtype.ext
  exact hx

/-- The actual lifted seed gives a normal cover by full max4
factors, with two-group kernels below and above the normal orbit base. -/
theorem seed_normalPowerCover
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .ru)
    (s : ModelSeed (modelSylow h d) (modelAut d d.action)) :
    Nonempty (NormalPowerCover 2
      (localOvergroup ((S : Subgroup H).map H.subtype) d s.localSubgroup) max4) := by
  let := h.finite
  let f := s.modelIso.toMonoidHom.comp (liftProjection d s.localSubgroup)
  have hf : Function.Surjective f :=
    s.modelIso.surjective.comp (liftProjection_surjective d s.localSubgroup)
  have hcentral : f.ker ≤ center (componentPreimage d s.localSubgroup) := by
    intro x hx
    apply liftProjection_ker_central h d s.localSubgroup
    apply s.modelIso.injective
    exact hx.trans (map_one s.modelIso).symm
  have hkill (x : componentPreimage d s.localSubgroup)
      (hx : inclusion (componentPreimage_le d s.localSubgroup) x ∈ center L) : f x = 1 := by
    change s.modelIso (liftProjection d s.localSubgroup x) = 1
    rw [liftProjection_kills_center h d s.localSubgroup x hx, map_one]
  exact h.component.relative_local_adjoin_normalPowerCover h.component_le
    (componentPreimage_le d s.localSubgroup) (map_subtype_le _)
    (S.isPGroup'.map H.subtype) (seed_normalized h d s)
    (seed_selfCentralizingCore h d s) f hf hcentral hkill


/-- Characteristic two and the original involution force the local two-core
to be nontrivial; the overgroup contains the supplied S. -/
theorem seed_localOvergroup_mem_HeOver (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru)
    (s : ModelSeed (modelSylow h d) (modelAut d d.action)) :
    localOvergroup ((S : Subgroup H).map H.subtype) d s.localSubgroup ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype) : Set G) := by
  let K := localOvergroup ((S : Subgroup H).map H.subtype) d s.localSubgroup
  have heven := seed_localOvergroup_even h d s
  have hz : z ∈ K := le_localOvergroup _ d s.localSubgroup h.mem_sylow
  refine ⟨heven, ?_, le_localOvergroup _ d s.localSubgroup⟩
  change K.pCoreIn 2 ≠ ⊥
  intro he
  have hc : z ∈ centralizer (K.pCoreIn 2 : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy : y = 1 := by simpa only [he, Subgroup.coe_bot, Set.mem_singleton_iff] using hy
    simp [hy]
  have hm := heven ⟨hz, hc⟩
  rw [he, mem_bot] at hm
  have := h.involution
  rw [hm, orderOf_one] at this
  norm_num at this

/-- Source application: a concrete local with the required generation,
characteristic two and a full max4 factor cover. All geometry is discharged;
the passage from a normal power cover to the permitted factor series is separate. -/
theorem exists_local_with_max4_cover (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) :
    ∃ K : Subgroup G,
      L ≤ centralizer ({z} : Set G) ⊔ K ∧
      K ≤ L ⊔ (S : Subgroup H).map H.subtype ∧
      K ∈ Chapter1.HeOver G (((S : Subgroup H).map H.subtype) : Set G) ∧
      Nonempty (NormalPowerCover 2 K max4) := by
  let s := transportedSeed h d
  exact ⟨localOvergroup ((S : Subgroup H).map H.subtype) d s.localSubgroup,
    generated_of_model_join _ d s.localSubgroup (seed_centralizerImage_sup h d s),
    localOvergroup_le _ d s.localSubgroup,
    seed_localOvergroup_mem_HeOver h d s, seed_normalPowerCover h d s⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry

end
