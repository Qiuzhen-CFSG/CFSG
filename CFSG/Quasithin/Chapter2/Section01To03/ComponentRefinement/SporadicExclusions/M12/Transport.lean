module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M12.Transport.CentralCover
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.PowerCover

/-!
# Full-parabolic central-cover transport for the M₁₂ exclusion

The intrinsic geometry supplies an invariant model seed isomorphic to the
actual second parabolic. Pulling it back through the specified O₂(L) quotient
retains a central two-kernel. Centerlessness of M₁₂ identifies this kernel
with Z(L), so the component-orbit map has full second-parabolic factors.
The orbit centralizer calculation makes its central kernel a two-group;
the supplied Sylow subgroup gives a two-group quotient above the orbit.
All component subnormality is relative to H, and only N_S(L) acts on L.

Generation uses genuine centralizing lifts of the fixed-subgroup two-residual
and the remaining Sylow supplement. Together with the characteristic-two
calculation this proves the literal `LocalGeometry` contract. The only extra
input is the stated intrinsic geometry; constructing it and assembling the
unconditional M₁₂ exclusion remain with the source-theorem owner.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M12Exclusion
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Restrict the actual component quotient to the full preimage of P. -/
noncomputable def liftProjection (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) : componentPreimage d P →* P :=
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
theorem liftProjection_surjective (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) : Function.Surjective (liftProjection d P) := by
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
    (d : SporadicQuotientInput L z .m12) (P : Subgroup M12) :
    (liftProjection d P).ker ≤ center (componentPreimage d P) := by
  intro x hx
  have hk : (⟨x.val, componentPreimage_le d P x.property⟩ : L) ∈ (quotientMap d).ker :=
    by
      change quotientMap d (inclusion (componentPreimage_le d P) x) = 1
      exact congrArg (fun p : P => (p : M12)) hx
  rw [quotientMap_ker] at hk
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (congrArg (fun l : L => (l : G))
    (mem_center_iff.mp (twoCore_le_center h hk) ⟨y.val, componentPreimage_le d P y.property⟩))

/-- The full component center is killed by the specified quotient map,
because it is precisely the retained two-core. -/
theorem liftProjection_kills_center (g : BlockGeometry.Geometry)
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) (x : componentPreimage d P)
    (hx : inclusion (componentPreimage_le d P) x ∈ center L) :
    liftProjection d P x = 1 := by
  rw [center_eq_twoCore g h d, ← quotientMap_ker d] at hx
  apply Subtype.ext
  exact hx

/-- The actual lifted seed gives a normal cover by full second-parabolic
factors, with two-group kernels below and above the normal orbit base. -/
theorem seed_normalPowerCover (g : BlockGeometry.Geometry)
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m12)
    (s : BlockGeometry.LocalSeed (modelSylow h d) (modelAut d d.action)) :
    Nonempty (NormalPowerCover 2
      (localOvergroup ((S : Subgroup H).map H.subtype) d s.localSubgroup) secondParabolic) := by
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
    rw [liftProjection_kills_center g h d s.localSubgroup x hx, map_one]
  exact h.component.relative_local_adjoin_normalPowerCover h.component_le
    (componentPreimage_le d s.localSubgroup) (map_subtype_le _)
    (S.isPGroup'.map H.subtype) (seed_normalized h d s)
    (seed_selfCentralizingCore h d s) f hf hcentral hkill

/-- Conditional transport from the intrinsic geometry through the actual
central cover and component orbit. No additional local or model premise remains. -/
theorem localGeometry_of_intrinsicGeometry (g : BlockGeometry.Geometry)
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m12) :
    Nonempty (LocalGeometry ((S : Subgroup H).map H.subtype) d) := by
  let s := transportedSeed g h d
  obtain ⟨c⟩ := seed_normalPowerCover g h d s
  exact ⟨{
    localSubgroup := s.localSubgroup
    modelIso := s.modelIso
    generated := seed_centralizerImage_sup h d s
    even := seed_localOvergroup_even h d s
    sectionCover := c }⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.M12Exclusion
