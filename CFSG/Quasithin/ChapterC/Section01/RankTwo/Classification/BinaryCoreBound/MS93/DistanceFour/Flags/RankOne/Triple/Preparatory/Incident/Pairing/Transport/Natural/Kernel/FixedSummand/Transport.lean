module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Linear

/-!
# Transporting the fixed-summand calculation to the original edge group

The bar-image construction retains the onto map and exact kernel Z_alpha.
Relative invariance transports the literal local normal closure into the
linear orbit span. A residual-fixed element is cubic-fixed under a genuine
bar-action marking; the binary S₃ calculation then places it in the seed and
fixes it under the full first actor. Both conclusions lift through the exact
kernel, without identifying residual and full-actor fixed spaces globally.

`BarActionData` isolates the remaining concrete action construction: the
full actor must act through the literal S₃, a residual element must map to the
cubic, and the seed image must equal a reflection displacement. Existence of
these data is not asserted here. The unconditional `bar_core_le_kernel`
supplies the action-kernel containment needed for that construction.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(3), printed p.906;
the intrinsic fixed denominator in (1.7) is on printed pp.847--848.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {i : Bool}

/-- The literal image of an ambient subgroup in V_beta/Z_alpha. -/
noncomputable def barImage (b : FlagLayerModule source i (Z R (alpha R)))
    (A : Subgroup (FreeAmalgam R)) : Submodule (ZMod 2) b.Space :=
  AddSubgroup.toZModSubmodule 2
    ((A.subgroupOf (V R (beta R))).map b.projection).toAddSubgroup

/-- Membership retains a lift in the original subgroup. -/
theorem mem_barImage (b : FlagLayerModule source i (Z R (alpha R)))
    (A : Subgroup (FreeAmalgam R)) (v : b.Space) :
    v ∈ barImage b A ↔ ∃ x : V R (beta R), (x : FreeAmalgam R) ∈ A ∧
      (b.projection x).toAdd = v := Iff.rfl

private noncomputable def barPreimage (b : FlagLayerModule source i (Z R (alpha R)))
    (S : Submodule (ZMod 2) b.Space) : Subgroup (FreeAmalgam R) :=
  (S.toAddSubgroup.toSubgroup.comap b.projection).map (V R (beta R)).subtype

private theorem barImage_le_iff (b : FlagLayerModule source i (Z R (alpha R)))
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ V R (beta R))
    (S : Submodule (ZMod 2) b.Space) :
    barImage b A ≤ S ↔ A ≤ barPreimage b S := by
  constructor
  · intro h x hx
    exact ⟨⟨x, hA hx⟩, h ⟨⟨x, hA hx⟩, hx, rfl⟩, rfl⟩
  · intro h v hv
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨y, hy, he⟩ := h hx
    have he' : y = x := Subtype.ext he
    subst y
    exact hy

private theorem barPreimage_normalized [Finite M]
    (b : FlagLayerModule source i (Z R (alpha R)))
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hkernel : flagKernel source i = Q R (beta R))
    (S : Submodule (ZMod 2) b.Space)
    (hS : ∀ g : flagParabolic source i, ∀ v ∈ S, b.representation g v ∈ S) :
    flagParabolic source i ≤ normalizer (barPreimage b S) := by
  apply le_normalizer_iff.mpr
  rintro g hg x ⟨v, hv, rfl⟩
  let a : flagParabolic source i := ⟨g, hg⟩
  let w := edgeRadiusAction source geometry hlarge i hkernel a v
  refine ⟨w, ?_, edgeRadiusAction_apply source geometry hlarge i hkernel a v⟩
  change (b.projection w).toAdd ∈ S
  rw [b.action a v w (edgeRadiusAction_apply source geometry hlarge i hkernel a v)]
  exact hS a _ hv

private theorem orbitSpan_invariant {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) BinaryS3.Actor W) (D : Submodule (ZMod 2) W)
    (g : BinaryS3.Actor) {v : W} (hv : v ∈ BinaryS3.orbitSpan ρ D) :
    ρ g v ∈ BinaryS3.orbitSpan ρ D := by
  refine Submodule.iSup_induction (fun a : BinaryS3.Actor => D.map (ρ a))
    (motive := fun w => ρ g w ∈ BinaryS3.orbitSpan ρ D) hv ?_ ?_ ?_
  · rintro a _ ⟨w, hw, rfl⟩
    exact le_iSup (fun a : BinaryS3.Actor => D.map (ρ a)) (g * a)
      ⟨w, hw, by rw [map_mul, Module.End.mul_apply]⟩
  · simp
  · intro x y hx hy
    simpa only [map_add] using (BinaryS3.orbitSpan ρ D).add_mem hx hy

private theorem mem_of_barImage (b : FlagLayerModule source i (Z R (alpha R)))
    (A : Subgroup (FreeAmalgam R)) (hZA : Z R (alpha R) ≤ A)
    (x : V R (beta R)) (hx : (b.projection x).toAdd ∈ barImage b A) :
    (x : FreeAmalgam R) ∈ A := by
  obtain ⟨y, hy, he⟩ := hx
  have he' : b.projection y = b.projection x := he
  have hk : x * y⁻¹ ∈ b.projection.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he', mul_inv_cancel]
  rw [b.kernel] at hk
  have hh : (x : FreeAmalgam R) * (y : FreeAmalgam R)⁻¹ ∈ A := hZA hk
  have hm : (x : FreeAmalgam R) * (y : FreeAmalgam R)⁻¹ * (y : FreeAmalgam R) ∈ A :=
    A.mul_mem hh hy
  simpa only [inv_mul_cancel_right] using hm

private theorem action_fixed_of_commutator [Finite M]
    (b : FlagLayerModule source i (Z R (alpha R)))
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hkernel : flagKernel source i = Q R (beta R))
    (A E : Subgroup (FreeAmalgam R)) (hAE : ⁅A,E⁆ ≤ Z R (alpha R))
    (g : flagParabolic source i) (hg : (g : FreeAmalgam R) ∈ E)
    (x : V R (beta R)) (hx : (x : FreeAmalgam R) ∈ A) :
    b.representation g (b.projection x).toAdd = (b.projection x).toAdd := by
  let w := edgeRadiusAction source geometry hlarge i hkernel g x
  have hk : w * x⁻¹ ∈ b.projection.ker := by
    rw [b.kernel]
    have hEA : ⁅E,A⁆ ≤ Z R (alpha R) := by rwa [commutator_comm]
    exact commutator_le.mp hEA g hg x hx
  have he : b.projection w = b.projection x := by
    simpa only [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] using hk
  rw [← b.action g x w (edgeRadiusAction_apply source geometry hlarge i hkernel g x)]
  exact congrArg Multiplicative.toAdd he

/-- The first actual two-core acts trivially on the bar module. -/
theorem bar_core_le_kernel [Finite M] (b : FlagLayerModule source i (Z R (alpha R)))
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (hkernel : flagKernel source i = Q R (beta R)) :
    (flagKernel source i).subgroupOf (flagParabolic source i) ≤ b.representation.ker := by
  intro g hg
  apply MonoidHom.mem_ker.mpr
  ext v
  obtain ⟨x, rfl⟩ := b.onto (Multiplicative.ofAdd v)
  apply action_fixed_of_commutator b geometry common.large_distance hkernel
    (V R (beta R)) (flagKernel source i) ?_ g hg x x.property
  rw [hkernel]
  exact (edgeRadius_commutator_le_edgeZ geometry common.large_distance early).trans
    (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))

/-- A concrete S₃ marking of the bar action and the actual seed displacement.
These are construction obligations, not fixed-summand conclusions. -/
structure BarActionData (b : FlagLayerModule source i (Z R (alpha R))) (d : M) where
  projection : flagParabolic source i →* BinaryS3.Actor
  representation : Representation (ZMod 2) BinaryS3.Actor b.Space
  action : ∀ g v, b.representation g v = representation (projection g) v
  cubic_lift : ∃ r : flagParabolic source i,
    (r : FreeAmalgam R) ∈ flagResidual source i ∧ projection r = BinaryS3.cubic
  reflection : BinaryS3.Actor
  reflection_square : reflection ^ 2 = 1
  reflection_ne_one : reflection ≠ 1
  seed_image : barImage b (Pairing.seed source i d) =
    BinaryS3.displacement representation reflection

/-- The literal local closure maps into the orbit span of its actual displacement. -/
theorem barImage_localSpan_le_orbitSpan [Finite M]
    (b : FlagLayerModule source i (Z R (alpha R)))
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d) (a : BarActionData b d) :
    barImage b (Pairing.localSpan source i d) ≤
      BinaryS3.orbitSpan a.representation (BinaryS3.displacement a.representation a.reflection) := by
  let S := BinaryS3.orbitSpan a.representation
    (BinaryS3.displacement a.representation a.reflection)
  apply (barImage_le_iff b _ (localSpan_le_edgeRadius source geometry hlarge i hkernel d hd) S).mpr
  apply RankOnePairing.Incidence.localGenerated_le_of_normalizes
  · apply barPreimage_normalized b geometry hlarge hkernel S
    intro g v hv
    rw [a.action]
    exact orbitSpan_invariant _ _ _ hv
  · apply (barImage_le_iff b _ (Pairing.seed_le_firstLayer source geometry hlarge i hkernel d hd) S).mp
    rw [a.seed_image]
    intro v hv
    apply le_iSup (fun g : BinaryS3.Actor =>
      (BinaryS3.displacement a.representation a.reflection).map (a.representation g)) 1
    exact ⟨v, hv, by simp⟩

/-- Conditional source assembly of both fixed-summand conclusions. Constructing
`BarActionData` from the source hypotheses remains necessary before applying it. -/
theorem local_fixed_summand_of_barAction [Finite M]
    (b : FlagLayerModule source i (Z R (alpha R)))
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d) (a : BarActionData b d) :
    (flagFixedPreimage source i ⊓ Pairing.localSpan source i d ≤ Pairing.seed source i d) ∧
    ⁅flagFixedPreimage source i ⊓ Pairing.localSpan source i d,
      flagParabolic source i⁆ ≤ Z R (alpha R) := by
  let F := flagFixedPreimage source i ⊓ Pairing.localSpan source i d
  have hF : F ≤ V R (beta R) := inf_le_left.trans (flagFixedPreimage_bounds source i).2
  have hfix (x : V R (beta R)) (hx : (x : FreeAmalgam R) ∈ F) :
      (b.projection x).toAdd ∈ barImage b (Pairing.seed source i d) ∧
      ∀ g : flagParabolic source i,
        b.representation g (b.projection x).toAdd = (b.projection x).toAdd := by
    have hs := barImage_localSpan_le_orbitSpan b geometry hlarge hkernel d hd a
      (show (b.projection x).toAdd ∈ barImage b (Pairing.localSpan source i d) from ⟨x, hx.2, rfl⟩)
    obtain ⟨r, hr, he⟩ := a.cubic_lift
    have hc := action_fixed_of_commutator b geometry hlarge hkernel
      (flagFixedPreimage source i) (flagResidual source i)
      (commutator_commutatorPreimage_le _ _ _
        ((edgeRadius_le_stabilizer geometry hlarge).trans (Z_normalized R _)))
      r hr x hx.1
    rw [a.action, he] at hc
    have hh := BinaryS3.fixed_orbitSpan a.representation a.reflection
      a.reflection_square a.reflection_ne_one hs hc
    exact ⟨a.seed_image ▸ hh.1, fun g => (a.action g _).trans (hh.2 (a.projection g))⟩
  constructor
  · intro x hx
    exact mem_of_barImage b _ le_sup_left ⟨x, hF hx⟩ (hfix ⟨x, hF hx⟩ hx).1
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro g hg x hx
    let v : V R (beta R) := ⟨x, hF hx⟩
    let w := edgeRadiusAction source geometry hlarge i hkernel ⟨g, hg⟩ v
    have he : b.projection w = b.projection v := by
      apply Multiplicative.toAdd.injective
      rw [b.action ⟨g, hg⟩ v w (edgeRadiusAction_apply source geometry hlarge i hkernel ⟨g, hg⟩ v)]
      exact (hfix v hx).2 ⟨g, hg⟩
    have hk : w * v⁻¹ ∈ b.projection.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [b.kernel] at hk
    exact hk

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
