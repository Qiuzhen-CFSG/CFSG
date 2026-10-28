module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSlices
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallBackward

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed

/-!
# Displacement coordinates for the full cubic seed

The centralizer of the entire original seed is E, retaining E/Q of order
three. The seed action therefore descends through the original symmetric
projection. A small critical pair makes every transposition have rank one
on that full seed. The natural or augmentation moving cover supplies an
intertwining map from the binary augmentation module; its pair vectors
remain nonzero. The six-letter displacement theorem then gives one
component conjugate of any noncentral seed vector whose centralizer
generates the whole vertex group with the prescribed critical actor.

The graph application keeps the literal seed, original embeddings and
same conjugator for generation and movement. CubicForwardClosure uses it
to prove centrality of the forward line without assuming that line lies
in the moving cover. Neither whole-core reconstruction nor the terminal
distance exclusions are asserted here.

The private import of FullSeed is an intentional internal reuse of its
two coordinate definitions, pairVector and adjacent. Their public model
theorems are reused; no natural-replacement theorem is instantiated and
no private name occurs in this module's public statements.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and the generating-centralizer choice in (5.9), pp.920--922. Adapts
Natural.Exhaustion.LargeDistance.SectionFive.FullSeed to the cubic kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev coverAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive W) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private def coverMap : Additive W →ₗ[ZMod 2] natural (Fin 6) :=
  Classical.choose (CubicAction.moved_natural_projection h e hz hk)
private theorem coverMap_surjective : Function.Surjective (coverMap h e hz hk) :=
  (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).1
private theorem coverMap_equivariant (g : Equiv.Perm (Fin 6)) (v : Additive W) :
    coverMap h e hz hk (coverAction h e hz hk g v) =
      naturalRepresentation (Fin 6) g (coverMap h e hz hk v) := by
  let := h.relative_normal
  obtain ⟨a,rfl⟩ := CubicEven.projection_surjective h e hz hk g
  have he : coverAction h e hz hk (π a) v = Additive.ofMul (MulAut.conjNormal a v.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply W π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) a v
  rw [he]
  exact (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.2 a v




include h in
theorem seed_elementary : IsElementaryAbelian 2 (radiusSeed L R) := by
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) (alpha Rg) rfl
  exact IsElementaryAbelian.comap_of_injective (p := 2) (embedM Rg)
    (embedM_injective Rg) (Z Rg (alpha Rg))

include h e hz hk in
theorem seed_centralizer : centralizer (radiusSeed L R : Set M) = extensionKernel h := by
  have hWZ : W ≤ radiusSeed L R := by
    intro v hv
    have hh := mem_map_of_mem (embedM Rg) hv
    rw [graph_U_map h e hz] at hh
    exact DistanceEight.U_le_Z Rg _ hh
  have hZX : radiusSeed L R ≤ centralOmega L R := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rw [←graph_X h]
    exact (map_comap_le _ _).trans ((sourceGeometry h).omega_bound _ rfl (sourceDistance_pos h))
  apply le_antisymm
  · rw [←CubicAction.projection_kernel h e hz hk,
      CubicAction.moved_projection_kernel h e hz hk]
    exact centralizer_le hWZ
  · rw [←hk]
    exact centralizer_le hZX

private theorem coverAction_conjugate (g : M) (v : Additive W) :
    ((coverAction h e hz hk (π g) v).toMul : M) = g * (v.toMul : M) * g⁻¹ := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation_apply W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) g v

include h e hz hk in
theorem small_critical_image_eq_swap
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t : S, t.IsSwap ∧ ((Z Rg a').comap (embedM Rg)).map π = zpowers t := by
  let := h.relative_normal
  let A := (Z Rg a').comap (embedM Rg)
  have hmA : A.map (embedM Rg) = Z Rg a' := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  let := finite_Z Rg (alpha Rg)
  let : Finite (U Rg (alpha Rg)) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg (alpha Rg))) (inclusion_injective _)
  have hC : Q Rg a' ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a' p.end_color))
  have hidx : (centralizer (Z Rg a' : Set (FreeAmalgam Rg))).relIndex (U Rg (alpha Rg)) ≤ 2 :=
    ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg (alpha Rg)) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices h e hz hk p hsmall).1
  have hidx' : (centralizer (A : Set M)).relIndex W ≤ 2 := by
    rw [←graph_U_map h e hz,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective _ (embedM_injective Rg),
      relIndex_map_map_of_injective _ _ (embedM_injective Rg),inf_relIndex_left] at hidx
    exact hidx
  have hcodim : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim W π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)] at hidx'
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx'
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk) (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hcodim
  have hne : A.map π ≠ ⊥ := by
    intro hn
    have hAE : A ≤ extensionKernel h :=
      CubicAction.projection_kernel h e hz hk ▸ (map_eq_bot_iff A).mp hn
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
    have hAQ := two_subgroup_le_core_of_le_extensionKernel h hz A
      ((IsElementaryAbelian.isPGroup 2 (Z Rg a')).comap_of_injective _ (embedM_injective Rg)) hAE
    have hh := map_mono (f := embedM Rg) hAQ
    rw [hmA,←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
    exact (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      (alpha Rg) rfl (sourceDistance_pos h) a' p.end_color p.critical).2 hh
  obtain ⟨t,_,ht,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (A.map π) hne hnat
  exact ⟨t,ht,he⟩
section SeedAction
variable [IsElementaryAbelian 2 (radiusSeed L R)]

/-- Conjugation on the full seed through the original symmetric projection. -/
noncomputable def seedAction :
    Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive (radiusSeed L R)) :=
  NormalElementaryQuotient.representation _ π (CubicEven.projection_surjective h e hz hk)
    ((CubicAction.projection_kernel h e hz hk).trans (seed_centralizer h e hz hk).symm)

/-- The descended seed action agrees with literal original-group conjugation. -/
theorem seedAction_conjugate
    (g : M) (z : Additive (radiusSeed L R)) :
    ((seedAction h e hz hk (π g) z).toMul : M) = g*z.toMul*g⁻¹ :=
  NormalElementaryQuotient.representation_apply _ _ _ _ g z
include h e hz hk in
/-- One small critical pair makes every transposition a transvection on the
entire seed, including all its central attachments. -/
theorem seed_transposition_rank_one
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (i j : Fin 6) (hij : i ≠ j) :
    Module.finrank (ZMod 2) (LinearMap.range (seedAction h e hz hk (Equiv.swap i j)-LinearMap.id)) = 1 := by
  let A := (Z Rg a').comap (embedM Rg)
  have hmA : A.map (embedM Rg) = Z Rg a' := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg)
      rfl (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hmZ : (radiusSeed L R).map (embedM Rg) = Z Rg (alpha Rg) :=
    map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  have hfixed : Z Rg (alpha Rg) ⊓ centralizer (Z Rg a' : Set (FreeAmalgam Rg)) =
      Z Rg (alpha Rg) ⊓ Q Rg a' := by
    exact critical_seed_centralizer_intersection h e p
  have hidx : (centralizer (A : Set M)).relIndex (radiusSeed L R) = 2 := by
    calc
      _ = ((radiusSeed L R).map (embedM Rg) ⊓
          centralizer (A.map (embedM Rg) : Set (FreeAmalgam Rg))).relIndex
          ((radiusSeed L R).map (embedM Rg)) := by
        rw [map_inf_centralizer_of_injective _ (embedM_injective Rg),
          relIndex_map_map_of_injective _ _ (embedM_injective Rg),inf_relIndex_left]
      _ = _ := by
        rw [hmA,hmZ,hfixed,inf_relIndex_left]
        exact (small_critical_indices h e hz hk p hsmall).1
  obtain ⟨t,ht,him⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  have hdim : fixedCodim (seedAction h e hz hk) (zpowers t) = 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim (radiusSeed L R)
      π (CubicEven.projection_surjective h e hz hk) ((CubicAction.projection_kernel h e hz hk).trans (seed_centralizer h e hz hk).symm)] at hidx
    change 2 ^ fixedCodim (seedAction h e hz hk) (((Z Rg a').comap (embedM Rg)).map π) = 2 at hidx
    rw [him] at hidx
    exact (Nat.pow_right_injective (by decide : 1 < 2)) (hidx.trans (by decide : 2 = 2^1))
  apply BinaryPermutation.TransvectionCoreMap.swap_rank_one (seedAction h e hz hk) ht _ i j hij
  rw [←fixedCodim_zpowers_eq_displacement_rank]
  exact hdim

/-- Every vector of the full source seed has ordinary six-letter displacement
coordinates. The canonical core map retains its possible central kernel. -/
theorem full_seed_displacement_coordinates
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ j : (coreRepresentation (Fin 6)).IntertwiningMap (seedAction h e hz hk),
      (∀ i k : Fin 6, i ≠ k → j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.pairVector i k) ≠ 0) ∧
      (∀ z : Additive (radiusSeed L R), ∃ w : Full (Fin 6), ∀ g : Equiv.Perm (Fin 6),
        seedAction h e hz hk g z-z = j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.displacement g w)) := by
  let ρ := seedAction h e hz hk
  have hUZ : W ≤ radiusSeed L R := by
    intro v hv
    have hh := mem_map_of_mem (embedM Rg) hv
    rw [graph_U_map h e hz] at hh
    exact DistanceEight.U_le_Z Rg _ hh
  let inc : Additive (W) →ₗ[ZMod 2] Additive (radiusSeed L R) :=
    (Subgroup.inclusion hUZ).toAdditive.toZModLinearMap 2
  have hi : Function.Injective inc := by
    intro v w he
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun x : Additive (radiusSeed L R) => (x.toMul : M)) he
  have heq (g : Equiv.Perm (Fin 6)) (v : Additive (W)) :
      inc (coverAction h e hz hk g v) = ρ g (inc v) := by
    obtain ⟨m,rfl⟩ := (CubicEven.projection_surjective h e hz hk) g
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (coverAction_conjugate h e hz hk m v).trans (seedAction_conjugate h e hz hk m (inc v)).symm
  have hex : ∃ j : (coreRepresentation (Fin 6)).IntertwiningMap ρ,
      ∀ i k : Fin 6, i ≠ k → j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.pairVector i k) ≠ 0 := by
    have hpair (i k : Fin 6) (hik : i ≠ k) :
        coreToNatural (Fin 6) (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.pairVector i k) ≠ 0 :=
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector_ne_zero hik
    rcases moved_subgroup_cover_model h e hz hk with ⟨E,hE⟩ | ⟨E,hE⟩
    · let f := inc.comp (E.symm.toLinearMap.comp (coreToNatural (Fin 6)))
      have hf (g : Equiv.Perm (Fin 6)) (v : core (Fin 6)) :
          f (coreRepresentation (Fin 6) g v) = ρ g (f v) := by
        change inc (E.symm (coreToNatural (Fin 6) (coreRepresentation (Fin 6) g v))) = _
        rw [coreToNatural_equivariant]
        have hh := hE g (E.symm (coreToNatural (Fin 6) v))
        simp only [MonoidHom.id_apply,LinearEquiv.apply_symm_apply] at hh
        rw [←hh,E.symm_apply_apply,heq]
        rfl
      refine ⟨{toLinearMap := f,isIntertwining' := fun g => LinearMap.ext (hf g)},?_⟩
      intro i k hik hz
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
      refine ⟨{toLinearMap := f,isIntertwining' := fun g => LinearMap.ext (hf g)},?_⟩
      intro i k hik hz
      have he : Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.pairVector i k = 0 := by
        apply E.symm.injective
        exact (hi (hz.trans (map_zero inc).symm)).trans (map_zero E.symm).symm
      exact hpair i k hik (he ▸ map_zero _)
  obtain ⟨j,hj⟩ := hex
  let hr := seed_transposition_rank_one h e hz hk p hsmall
  refine ⟨j,hj,?_⟩
  intro z
  apply Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.exists_coordinates ρ j (fun i => hj _ _ (by simp only [ne_eq, Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]; omega)) _ z
  intro i
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact (hr i.castSucc i.succ (by simp only [ne_eq, Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]; omega)).le


end SeedAction
include h e hz hk in
/-- The full seed admits the same simultaneous generating-centralizer and
movement choice as the moved cover, using the literal small critical actor. -/
theorem exists_seed_conjugate_generator
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (v : radiusSeed L R) (hv : (v : M) ∉ center M) :
    let A := (Z Rg a').comap (embedM Rg)
    ∃ g ∈ L.subgroupOf (L ⊔ R),
      centralizer ({g*(v:M)*g⁻¹} : Set M) ⊔ A = ⊤ ∧
      g*(v:M)*g⁻¹ ∉ centralizer (A : Set M) := by
  let := seed_elementary (h := h)
  let ρ := seedAction h e hz hk
  let A := (Z Rg a').comap (embedM Rg)
  obtain ⟨j,hj,hcoords⟩ := full_seed_displacement_coordinates h e hz hk p hsmall
  obtain ⟨w,hw⟩ := hcoords (Additive.ofMul v)
  have hvfix : ¬ ∀ x, ρ x (Additive.ofMul v)=Additive.ofMul v := by
    intro hh
    apply hv
    apply mem_center_iff.mpr
    intro m
    have he := congrArg (fun y : Additive (radiusSeed L R) => (y.toMul : M)) (hh (π m))
    rw [seedAction_conjugate] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  obtain ⟨t,ht,him⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  obtain ⟨x,hxt⟩ := Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.exists_generating_conjugate ρ j hj (Additive.ofMul v) w hw hvfix t ht
  obtain ⟨g,hg,hgx⟩ := (show x.val ∈ (L.subgroupOf (L ⊔ R)).map π by
    rw [(CubicAction.component_image h e hz hk)];exact x.property)
  let v' : Additive (radiusSeed L R) := ρ x.val (Additive.ofMul v)
  have hv' : (v'.toMul : M) = g*(v:M)*g⁻¹ := by
    dsimp only [v']
    rw [←hgx]
    exact seedAction_conjugate h e hz hk g _
  let C := centralizer ({g*(v:M)*g⁻¹} : Set M)
  let D := C ⊔ A
  have hkerD : (π).ker ≤ D := by
    rw [(CubicAction.projection_kernel h e hz hk),←seed_centralizer h e hz hk]
    apply le_trans _ le_sup_left
    intro q hq
    rw [mem_centralizer_singleton_iff]
    exact (hq _ (hv' ▸ v'.toMul.property)).symm
  have htA : t ∈ A.map π := by
    change t ∈ ((Z Rg a').comap (embedM Rg)).map π
    rw [him]
    exact mem_zpowers t
  have hmD : D.map π = ⊤ := by
    apply hxt.2
    · intro y hy
      obtain ⟨m,rfl⟩ := (CubicEven.projection_surjective h e hz hk) y
      refine mem_map_of_mem _ (mem_sup_left ?_)
      rw [mem_centralizer_singleton_iff]
      have he := congrArg (fun z : Additive (radiusSeed L R) => (z.toMul : M)) hy
      change ((seedAction h e hz hk (π m) v').toMul : M) = (v'.toMul : M) at he
      rw [seedAction_conjugate,hv'] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · exact map_mono le_sup_right htA
  have hD : D = ⊤ := by
    have he := congrArg (Subgroup.comap π) hmD
    rwa [comap_map_eq,sup_eq_left.mpr hkerD,comap_top] at he
  refine ⟨g,hg,hD,?_⟩
  intro hfix
  obtain ⟨a,ha,hat⟩ := htA
  apply hxt.1
  change ρ t v' = v'
  rw [←hat]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [seedAction_conjugate,hv',hfix a ha,mul_inv_cancel_right]

include h e hz hk in
/-- One component conjugator supplies generation and movement for any
noncentral line in the full graph seed. -/
theorem exists_seed_line_generator
    {b : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) b)
    (hsmall : (Q Rg b).relIndex (Z Rg (alpha Rg)) < 4)
    (H : Subgroup (FreeAmalgam Rg)) (hHZ : H ≤ Z Rg (alpha Rg))
    (hcard : Nat.card H = 2)
    (hcentral : ¬ H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) :
    ∃ g ∈ Ltilde Rg (alpha Rg),
      (stabilizer Rg (alpha Rg) ⊓ centralizer
        (H.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam Rg))) ⊔
          Z Rg b = stabilizer Rg (alpha Rg) ∧
      ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer
        (Z Rg b : Set (FreeAmalgam Rg)) := by
  classical
  obtain ⟨z,hzn,hunique⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hcard
  have hznot : (z : FreeAmalgam Rg) ∉ centralizer
      (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    intro hz
    apply hcentral
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ one_mem _
    · have he : (⟨x,hx⟩ : H) = z := hunique _ (fun he => hx1 (congrArg Subtype.val he))
      have hxz : x = (z : FreeAmalgam Rg) := congrArg Subtype.val he
      rw [hxz]
      exact hz
  let := seed_elementary (h := h)
  let i := embedM Rg
  have hi := embedM_injective Rg
  have hir : i.range = stabilizer Rg (alpha Rg) := (stabilizer_m_base Rg).symm
  obtain ⟨v,hvz⟩ := (show (z : FreeAmalgam Rg) ∈ i.range from
    hir.symm ▸ (Z_le_stabilizer Rg _ (hHZ z.property)))
  have hv : v ∈ radiusSeed L R := by
    change i v ∈ Z Rg (alpha Rg)
    rw [hvz]
    exact hHZ z.property
  have hvnot : v ∉ center M := by
    intro hv
    apply hznot
    intro m hm
    obtain ⟨m,rfl⟩ := hir.symm ▸ hm
    rw [←hvz,←map_mul,←map_mul]
    exact congrArg i (mem_center_iff.mp hv m)
  have hA : Z Rg b ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) p.start_color
      (by rw [(sourceGeometry h).distance_constant (alpha Rg) p.start_color]
          exact sourceDistance_pos h) p.critical
  let A := (Z Rg b).comap i
  have hmA : A.map i = Z Rg b := map_comap_eq_self hA
  obtain ⟨g,hg,hgen,hmove⟩ := exists_seed_conjugate_generator h e hz hk p hsmall ⟨v,hv⟩ hvnot
  let j : M →* stabilizer Rg (alpha Rg) :=
    i.codRestrict _ (fun x => hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩))
  have hgL : i g ∈ Ltilde Rg (alpha Rg) := by
    have hg' : g ∈ pResidual 2 M := (h.relative_residual).symm ▸ hg
    exact mem_map_of_mem (stabilizer Rg (alpha Rg)).subtype
      ((map_pResidual_le 2 j) (mem_map_of_mem j hg'))
  let C := centralizer ({g * v * g⁻¹} : Set M)
  let HC := H.map (MulAut.conj (i g)).toMonoidHom
  have hC : C.map i ≤ stabilizer Rg (alpha Rg) ⊓
      centralizer (HC : Set (FreeAmalgam Rg)) := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩),?_⟩
    rintro y ⟨w,hw,rfl⟩
    by_cases hw1 : w = 1
    · simp only [hw1,map_one,one_mul,mul_one]
    · have he : (⟨w,hw⟩ : H) = z := hunique _ (fun he => hw1 (congrArg Subtype.val he))
      have hwz : w = (z : FreeAmalgam Rg) := congrArg Subtype.val he
      rw [hwz,←hvz]
      change (i g * i v * (i g)⁻¹) * i x = i x * (i g * i v * (i g)⁻¹)
      simpa only [map_mul,map_inv] using congrArg i
        (mem_centralizer_singleton_iff.mp hx).symm
  refine ⟨i g,hgL,?_,?_⟩
  · apply le_antisymm (sup_le inf_le_left (hA.trans_eq hir))
    have hm := congrArg (Subgroup.map i) hgen
    rw [Subgroup.map_sup,hmA,←MonoidHom.range_eq_map,hir] at hm
    calc
      stabilizer Rg (alpha Rg) = C.map i ⊔ Z Rg b := hm.symm
      _ ≤ _ := sup_le_sup_right hC _
  · intro hfix
    apply hmove
    intro x hx
    have hzH : i (g * v * g⁻¹) ∈ HC := by
      have hh := mem_map_of_mem (MulAut.conj (i g)).toMonoidHom z.property
      change (i g * (z : FreeAmalgam Rg) * (i g)⁻¹) ∈ HC at hh
      simpa only [←hvz,map_mul,map_inv] using hh
    apply hi
    simpa only [map_mul] using hfix hzH (i x) hx


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
