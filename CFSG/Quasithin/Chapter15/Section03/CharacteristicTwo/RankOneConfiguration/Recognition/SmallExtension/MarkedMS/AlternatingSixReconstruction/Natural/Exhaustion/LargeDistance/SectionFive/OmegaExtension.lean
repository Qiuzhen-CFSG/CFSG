module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullKernel

-- Internal continuation of FullSeed: coordinate equations are used only in proofs.
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed

/-!
# Full omega coordinates and the central-generation alternative

The saved full-X image comparison gives index two on the entire omega
layer at a small critical pair. Conjugation then gives displacement rank
one for every transposition on X, through the original symmetric quotient.
An equivariant map from the six-letter augmentation core has image exactly
the original moved subgroup. The same coordinate construction as for the
seed consequently describes displacement of every vector of X.

Even coordinate vectors lie in the moved subgroup plus the full fixed
subgroup. If these do not generate X, subtracting an even vector produces
an actual omega vector with singleton displacement coordinates. This gives
a precise alternative to central generation without assuming a complement
or identifying X with Z. Both moved cover orders and the order-32 constant
kernel remain intact.

The literal shifted-path application retains its component conjugator and
every shared vertex. Either R_3 = [D, X_z intersect Q_c] is the proved
central seed-kernel line, or the original omega layer supplies the explicit
singleton witness. Excluding this witness using source nonnormality,
comparing the spans, strict slices, the other radical images, intermediate
R_4/R_6 noncentrality and both terminal distance contradictions remain open.

This is an internal continuation of FullSeed; its private coordinate
bodies are imported only for proofs, without changing their public API.
Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), printed pp.866--867,
and the full X-kernel in (5.9), printed pp.920--922, especially p.921.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

local notation "X₀" => omegaCenterIn (pCore 2 d.overgroup)

private instance omega_normal : (X₀).Normal := by
  rw [← normalizer_eq_top_iff]
  apply top_unique
  rw [← normalizer_eq_top (pCore 2 d.overgroup)]
  exact normalizer_le_normalizer_omegaCenterIn _

include h in
private theorem omega_map : (X₀).map (embedM d.radical) = X d.radical (alpha d.radical) := by
  rw [X, Q_alpha d.radical (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d),omegaCenter_map _ _ (embedM_injective _)]
  rfl

include s in
private theorem omega_centralizer : centralizer (X₀ : Set d.overgroup) = pCore 2 d.overgroup := by
  apply le_antisymm
  · exact (centralizer_le (replacementMoved_le_omegaCenter h d)).trans_eq (moved_centralizer s)
  · exact le_centralizer_iff.mpr (fun _ hx => (mem_omegaCenterIn_iff _ _).mp hx |>.2.1)

variable [hOmega : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup))]

noncomputable def omegaAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive X₀) :=
  NormalElementaryQuotient.representation _ s.projection s.surjective
    (s.projection_kernel.trans (omega_centralizer s).symm)

theorem omegaAction_conjugate (g : d.overgroup) (z : Additive X₀) :
    ((omegaAction s (s.projection g) z).toMul : d.overgroup) = g*z.toMul*g⁻¹ :=
  NormalElementaryQuotient.representation_apply _ _ _ _ g z

private theorem core_join_relIndex {F : Type*} [Group F] (A B : Subgroup F)
    (hn : B ≤ normalizer (A : Set F)) : A.relIndex (A ⊔ B) = A.relIndex B := by
  let J := A ⊔ B
  let : (A.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hi := relIndex_sup_left (B.subgroupOf J) (A.subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  exact hi

omit hOmega in
include s in
/-- The entire omega layer has critical index two in the small branch. -/
theorem small_critical_X_indices (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    (Q d.radical z).relIndex (X d.radical a) = 2 := by
  let q : CriticalPath d.radical (replacementGeometry h d) z a :=
    CriticalPath.ofPair p.end_color (critical_reverse_pair s hc p)
  have hs : (Q d.radical a).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hXN := (CriticalCriterion.critical_X_le_stabilizer d.radical (replacementGeometry h d)
      (edgeCentralizerCondition s hc) (replacementDistance_pos h d) _ p.start_color _ p.critical).trans (Q_normalized d.radical z)
  have hZX : Z d.radical a ≤ X d.radical a := by
    apply (replacementGeometry h d).omega_bound a p.start_color
    rw [(replacementGeometry h d).distance_constant a p.start_color]
    exact replacementDistance_pos h d
  have hZN := hZX.trans hXN
  rw [←core_join_relIndex _ _ hXN,small_critical_X_join s hc q hs,
    core_join_relIndex _ _ hZN]
  exact (small_critical_indices s hc p hsmall).1

omit hOmega in
include s in
private theorem omega_critical_fixed_index (hc : DistanceTwo.CentralLayer d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    (centralizer ((Z d.radical a').comap (embedM d.radical) : Set d.overgroup)).relIndex X₀ = 2 := by
  let A := (Z d.radical a').comap (embedM d.radical)
  have hmA : A.map (embedM d.radical) = Z d.radical a' := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical)
      rfl (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical))
  have hfixed : X d.radical (alpha d.radical) ⊓ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) =
      X d.radical (alpha d.radical) ⊓ Q d.radical a' := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a' p.end_color]
      exact ⟨(CriticalCriterion.critical_X_le_stabilizer d.radical (replacementGeometry h d)
      (edgeCentralizerCondition s hc) (replacementDistance_pos h d) _ p.start_color _ p.critical) hx.1,hx.2⟩
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
  change (centralizer (A : Set d.overgroup)).relIndex X₀ = 2
  calc
    _ = ((X₀).map (embedM d.radical) ⊓
        centralizer (A.map (embedM d.radical) : Set (FreeAmalgam d.radical))).relIndex
        ((X₀).map (embedM d.radical)) := by
      rw [map_inf_centralizer_of_injective _ (embedM_injective d.radical),
        relIndex_map_map_of_injective _ _ (embedM_injective d.radical),inf_relIndex_left]
    _ = _ := by
      rw [hmA,omega_map (h := h),hfixed,inf_relIndex_left]
      exact small_critical_X_indices s hc p hsmall

private theorem omega_fixedCodim (A : Subgroup d.overgroup) :
    2 ^ fixedCodim (omegaAction s) (A.map s.projection) =
      (centralizer (A : Set d.overgroup)).relIndex X₀ := by
  exact (NormalElementaryQuotient.centralizer_index_eq_fixedCodim X₀
    s.projection s.surjective (s.projection_kernel.trans (omega_centralizer s).symm) A).symm

private theorem transposition_rank_of_image {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) Y]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) Y)
    (A : Subgroup (Equiv.Perm (Fin 6)))
    (hA : ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧ A = zpowers t)
    (hdim : 2 ^ fixedCodim ρ A = 2) (i j : Fin 6) (hij : i ≠ j) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ (Equiv.swap i j)-LinearMap.id)) = 1 := by
  obtain ⟨t,ht,rfl⟩ := hA
  apply BinaryPermutation.TransvectionCoreMap.swap_rank_one ρ ht _ i j hij
  rw [←fixedCodim_zpowers_eq_displacement_rank]
  exact (Nat.pow_right_injective (by decide : 1 < 2)) (hdim.trans (by decide : 2 = 2^1))

include s in
/-- A small critical pair makes every transposition rank one on full X. -/
theorem omega_transposition_rank_one (hc : DistanceTwo.CentralLayer d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (i j : Fin 6) (hij : i ≠ j) :
    Module.finrank (ZMod 2) (LinearMap.range (omegaAction s (Equiv.swap i j)-LinearMap.id)) = 1 := by
  apply transposition_rank_of_image (omegaAction s) (graphImage s (Z d.radical a'))
    (small_critical_image_eq_swap (κ := KnownSimple.IsKnownSimple) (h := h) (d := d) s hc p hsmall) _ i j hij
  exact (omega_fixedCodim s ((Z d.radical a').comap (embedM d.radical))).trans
    (omega_critical_fixed_index s hc p hsmall)

/-- Inclusion of the original moved cover in the full omega layer. -/
def omegaMovedMap : Additive (replacementMoved d) →ₗ[ZMod 2] Additive X₀ :=
  (Subgroup.inclusion (replacementMoved_le_omegaCenter h d)).toAdditive.toZModLinearMap 2

private theorem coreMap_of_cover {T Y : Type*} [AddCommGroup T] [Module (ZMod 2) T]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) T)
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) Y)
    (inc : T →ₗ[ZMod 2] Y) (hi : Function.Injective inc)
    (heq : ∀ g v, inc (σ g v) = ρ g (inc v))
    (hcover : BinaryPermutation.SixCover.IsNaturalOrCore σ (MonoidHom.id _)) :
    ∃ j : (coreRepresentation (Fin 6)).IntertwiningMap ρ,
      j.toLinearMap.range = inc.range ∧
      (∀ i k : Fin 6, i ≠ k → j (SeedCoordinates.pairVector i k) ≠ 0) := by
  have hpair (i k : Fin 6) (hik : i ≠ k) :
      coreToNatural (Fin 6) (SeedCoordinates.pairVector i k) ≠ 0 :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector_ne_zero hik
  rcases hcover with ⟨E,hE⟩ | ⟨E,hE⟩
  · let f := inc.comp (E.symm.toLinearMap.comp (coreToNatural (Fin 6)))
    have hf (g : Equiv.Perm (Fin 6)) (v : core (Fin 6)) :
        f (coreRepresentation (Fin 6) g v) = ρ g (f v) := by
      change inc (E.symm (coreToNatural (Fin 6) (coreRepresentation (Fin 6) g v))) = _
      rw [coreToNatural_equivariant]
      have hh := hE g (E.symm (coreToNatural (Fin 6) v))
      simp only [MonoidHom.id_apply,LinearEquiv.apply_symm_apply] at hh
      rw [←hh,E.symm_apply_apply,heq]
      rfl
    refine ⟨{toLinearMap := f,isIntertwining' := fun g => LinearMap.ext (hf g)},?_,?_⟩
    · change f.range = inc.range
      ext z
      constructor
      · rintro ⟨v,rfl⟩; exact LinearMap.mem_range_self inc _
      · rintro ⟨v,rfl⟩
        obtain ⟨w,hw⟩ := coreToNatural_surjective (E v)
        refine ⟨w,?_⟩
        change inc (E.symm (coreToNatural (Fin 6) w)) = inc v
        rw [hw,E.symm_apply_apply]
    · intro i k hik hz
      apply hpair i k hik
      apply E.symm.injective
      exact (hi (hz.trans (map_zero inc).symm)).trans (map_zero E.symm).symm
  · let f := inc.comp E.symm.toLinearMap
    have hf (g : Equiv.Perm (Fin 6)) (v : core (Fin 6)) :
        f (coreRepresentation (Fin 6) g v) = ρ g (f v) := by
      change inc (E.symm (coreRepresentation (Fin 6) g v)) = _
      have hh := hE g (E.symm v)
      simp only [MonoidHom.id_apply,LinearEquiv.apply_symm_apply] at hh
      rw [←hh,E.symm_apply_apply,heq]
      rfl
    refine ⟨{toLinearMap := f,isIntertwining' := fun g => LinearMap.ext (hf g)},?_,?_⟩
    · change f.range = inc.range
      ext z
      constructor
      · rintro ⟨v,rfl⟩; exact LinearMap.mem_range_self inc _
      · rintro ⟨v,rfl⟩
        exact ⟨E v,by change inc (E.symm (E v)) = inc v; rw [E.symm_apply_apply]⟩
    · intro i k hik hz
      have he : SeedCoordinates.pairVector i k = 0 := by
        apply E.symm.injective
        exact (hi (hz.trans (map_zero inc).symm)).trans (map_zero E.symm).symm
      exact hpair i k hik (he ▸ map_zero _)

/-- Every full omega vector has six-letter displacement coordinates. The
range of the core map is exactly the original moved cover. -/
theorem full_X_displacement_coordinates (hc : DistanceTwo.CentralLayer d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ j : (coreRepresentation (Fin 6)).IntertwiningMap (omegaAction s),
      j.toLinearMap.range = (omegaMovedMap (h := h) (d := d)).range ∧
      (∀ i k : Fin 6, i ≠ k → j (SeedCoordinates.pairVector i k) ≠ 0) ∧
      (∀ z : Additive X₀, ∃ w : Full (Fin 6), ∀ g : Equiv.Perm (Fin 6),
        omegaAction s g z-z = j (SeedCoordinates.displacement g w)) := by
  let ρ := omegaAction s
  let inc := omegaMovedMap (h := h) (d := d)
  have hi : Function.Injective inc := by
    intro v w he
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun x : Additive X₀ => (x.toMul : d.overgroup)) he
  have heq (g : Equiv.Perm (Fin 6)) (v : Additive (replacementMoved d)) :
      inc (coverAction s g v) = ρ g (inc v) := by
    obtain ⟨m,rfl⟩ := s.surjective g
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (coverAction_conjugate s m v).trans (omegaAction_conjugate s m (inc v)).symm
  obtain ⟨j,hjr,hj⟩ := coreMap_of_cover (coverAction s) ρ inc hi heq (cover_model s)
  refine ⟨j,hjr,hj,?_⟩
  intro z
  apply SeedCoordinates.exists_coordinates ρ j (fun i => hj _ _ (by
    simp only [ne_eq, Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]; omega)) _ z
  intro i
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact (omega_transposition_rank_one s hc p hsmall i.castSucc i.succ (by
    simp only [ne_eq, Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]; omega)).le

namespace SeedCoordinates
variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Displacement coordinates leave only the odd permutation-extension case
outside the moved subspace plus invariants. The witness has singleton
coordinates, rather than an unspecified extra trivial quotient. -/
theorem generation_or_singleton
    (ρ : Representation (ZMod 2) S Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hcoords : ∀ z : Y, ∃ w : Full (Fin 6), ∀ g : S,
      ρ g z-z = j (displacement g w)) :
    j.toLinearMap.range ⊔ ρ.invariants = ⊤ ∨
      ∃ z : Y, ∀ g : S, ρ g z-z = j (displacement g (Pi.single 0 1)) := by
  classical
  by_cases hgen : j.toLinearMap.range ⊔ ρ.invariants = ⊤
  · exact Or.inl hgen
  right
  have hex : ∃ z : Y, z ∉ j.toLinearMap.range ⊔ ρ.invariants := by
    by_contra! hh
    exact hgen (top_unique (fun z _ => hh z))
  obtain ⟨z,hz⟩ := hex
  obtain ⟨w,hw⟩ := hcoords z
  have hodd : augmentation (Fin 6) w ≠ 0 := by
    intro hzero
    let v : core (Fin 6) := ⟨w,hzero⟩
    have he (g : S) : displacement g w = coreRepresentation (Fin 6) g v-v := by
      apply Subtype.ext
      rfl
    have hf : z-j v ∈ ρ.invariants := by
      intro g
      have hh := hw g
      rw [he,map_sub,j.isIntertwining] at hh
      rw [map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.mp hh
    apply hz
    have hm := Submodule.add_mem_sup (LinearMap.mem_range_self j.toLinearMap v) hf
    change j v + (z-j v) ∈ j.toLinearMap.range ⊔ ρ.invariants at hm
    have he : j v + (z-j v) = z := by abel
    rwa [he] at hm
  have hone : augmentation (Fin 6) w = 1 :=
    (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hodd
  let v : core (Fin 6) := ⟨w-Pi.single 0 1, by
    change augmentation (Fin 6) (w-Pi.single 0 1) = 0
    rw [map_sub,hone]
    simp [augmentation]⟩
  refine ⟨z-j v,?_⟩
  intro g
  have he : displacement g w-(coreRepresentation (Fin 6) g v-v) =
      displacement g (Pi.single 0 1) := by
    apply Subtype.ext
    change (representation (Fin 6) g w-w)-
      (representation (Fin 6) g (w-Pi.single 0 1)-(w-Pi.single 0 1)) = _
    rw [map_sub]
    dsimp [displacement]
    abel
  calc
    _ = (ρ g z-z)-(ρ g (j v)-j v) := by rw [map_sub]; abel
    _ = j (displacement g w)-j (coreRepresentation (Fin 6) g v-v) := by
      rw [hw,map_sub,j.isIntertwining]
    _ = _ := by rw [←map_sub,he]
end SeedCoordinates

private theorem omega_generation_graph (hc : DistanceTwo.CentralLayer d)
    (hgen : (omegaMovedMap (h := h) (d := d)).range ⊔ (omegaAction s).invariants = ⊤) :
    X d.radical (alpha d.radical) = U d.radical (alpha d.radical) ⊔
      (X d.radical (alpha d.radical) ⊓ centralizer
        (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) := by
  have hlocal : X₀ = replacementMoved d ⊔ (X₀ ⊓ center d.overgroup) := by
    apply le_antisymm
    · intro x hx
      have hx' : Additive.ofMul (⟨x,hx⟩ : X₀) ∈
          (omegaMovedMap (h := h) (d := d)).range ⊔ (omegaAction s).invariants :=
        hgen.symm ▸ Submodule.mem_top
      obtain ⟨v,⟨v₀,rfl⟩,w,hw,he⟩ := Submodule.mem_sup.mp hx'
      have hwc : (w.toMul : d.overgroup) ∈ center d.overgroup := by
        apply mem_center_iff.mpr
        intro m
        have hh := congrArg (fun z : Additive X₀ => (z.toMul : d.overgroup))
          (hw (s.projection m))
        rw [omegaAction_conjugate] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      have hm : (v₀.toMul : d.overgroup) * (w.toMul : d.overgroup) = x :=
        congrArg (fun z : Additive X₀ => (z.toMul : d.overgroup)) he
      rw [←hm]
      exact (replacementMoved d ⊔ (X₀ ⊓ center d.overgroup)).mul_mem
        (mem_sup_left v₀.toMul.property) (mem_sup_right ⟨w.toMul.property,hwc⟩)
    · exact sup_le (replacementMoved_le_omegaCenter h d) inf_le_left
  have hh := congrArg (Subgroup.map (embedM d.radical)) hlocal
  rw [Subgroup.map_sup,omega_map (h := h),←hc.U_eq_moved] at hh
  have he : center d.overgroup = centralizer ((⊤ : Subgroup d.overgroup) : Set d.overgroup) := by
    rw [coe_top,centralizer_univ]
  rw [he,←map_inf_centralizer_of_injective _ (embedM_injective d.radical),
    omega_map (h := h),←MonoidHom.range_eq_map] at hh
  change X d.radical (alpha d.radical) = U d.radical (alpha d.radical) ⊔
    (X d.radical (alpha d.radical) ⊓ centralizer (Mbar d.radical : Set (FreeAmalgam d.radical))) at hh
  rw [←stabilizer_m_base] at hh
  exact hh

/-- Full X is generated by its original moved cover and fixed vectors, or
there is an explicit singleton-coordinate vector in that same omega layer.
The latter supplies the explicit witness for the permutation-extension
case still to be excluded by the source nonnormality argument. -/
theorem full_X_generation_or_singleton (hc : DistanceTwo.CentralLayer d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    (X d.radical (alpha d.radical) = U d.radical (alpha d.radical) ⊔
      (X d.radical (alpha d.radical) ⊓ centralizer
        (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))) ∨
      ∃ j : (coreRepresentation (Fin 6)).IntertwiningMap (omegaAction s),
        j.toLinearMap.range = (omegaMovedMap (h := h) (d := d)).range ∧
        (∀ i k : Fin 6, i ≠ k → j (SeedCoordinates.pairVector i k) ≠ 0) ∧
        ∃ x : Additive X₀, ∀ g : Equiv.Perm (Fin 6),
          omegaAction s g x-x = j (SeedCoordinates.displacement g (Pi.single 0 1)) := by
  obtain ⟨j,hjr,hj,hcoords⟩ := full_X_displacement_coordinates s hc p hsmall
  rcases SeedCoordinates.generation_or_singleton (omegaAction s) j hcoords with hgen | hext
  · left
    apply omega_generation_graph s hc
    rwa [hjr] at hgen
  · exact Or.inr ⟨j,hjr,hj,hext⟩

/-- The original shifted configuration retains every path vertex and the same
component conjugator. Either its literal full X-kernel commutator is the
proved central seed line, or the original omega layer has the explicit
singleton-coordinate extension witness. Both cover orders and the original
natural quotient are retained. -/
theorem full_point_small_shifted_X_extension_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      ∃ t, Adjacent d.radical c t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical c ∧
      ∃ y ∈ Ltilde d.radical c,
        let a := act d.radical y⁻¹ (alpha d.radical)
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
        let D := conjugateSpanBy (Z d.radical a) P
        let J := ⁅D,Z d.radical z ⊓ Q d.radical c⁆
        let A₀ := X d.radical z ⊓ Q d.radical c
        let R₃ := ⁅D,A₀⁆
        H₂ ≤ U d.radical c ⊓ Z d.radical t ∧
        P ⊔ Z d.radical z = stabilizer d.radical c ∧
        ¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        D ≤ Q d.radical a' ∧
        (Q d.radical z).relIndex (Z d.radical c) = 2 ∧
        Nat.card J = 2 ∧ J ≤ Z d.radical z ∧
        J ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) ∧
        J ⊓ ⁅Z d.radical c,Z d.radical z⁆ = ⊥ ∧
        J ≤ fixedCore d.radical c ∧ J ≤ Z d.radical a ∧ J ≠ H₂ ∧
        (∃ x ∈ P, ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,
          Z d.radical z ⊓ Q d.radical c⁆ = J) ∧
        Q d.radical c ⊔ X d.radical z = Q d.radical c ⊔ Z d.radical z ∧
        ⁅X d.radical c,X d.radical z⁆ = ⁅Z d.radical c,Z d.radical z⁆ ∧
        stabilizer d.radical z ⊓ centralizer (A₀ : Set (FreeAmalgam d.radical)) =
          Q d.radical z ⊔ Z d.radical c ∧
        J ≤ R₃ ∧ R₃ ≠ ⊥ ∧ R₃ ≤ D ⊓ A₀ ∧
        (R₃ = J ∨
          ∃ j : (coreRepresentation (Fin 6)).IntertwiningMap (omegaAction s),
            j.toLinearMap.range = (omegaMovedMap (h := h) (d := d)).range ∧
            (∀ i k : Fin 6, i ≠ k → j (SeedCoordinates.pairVector i k) ≠ 0) ∧
            ∃ x : Additive (omegaCenterIn (pCore 2 d.overgroup)),
              ∀ g : Equiv.Perm (Fin 6), omegaAction s g x-x =
                j (SeedCoordinates.displacement g (Pi.single 0 1))) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,haz,hover,hpre,t,hct,hQtgen,y,hy,hHseed,hPgen,hHmove,hDQ,
    hidx,hJcard,hJZ,hJG,hJcrit,hJcore,hJseed,hJne,hxJ,hjoin,hcom,hfix,hJR,hRne,hRA,heq⟩ :=
    full_point_small_shifted_X_kernel_knownSimple hb u hfull p hslice hsmall
  refine ⟨z,q,haz,hover,hpre,t,hct,hQtgen,y,hy,hHseed,hPgen,hHmove,hDQ,
    hidx,hJcard,hJZ,hJG,hJcrit,hJcore,hJseed,hJne,hxJ,hjoin,hcom,hfix,hJR,hRne,hRA,?_⟩
  rcases full_X_generation_or_singleton s hc p hsmall with hgen | hext
  · exact Or.inl (heq hgen)
  · exact Or.inr hext

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
