module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicShiftedOmega
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaExtension
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed

/-!
# Full omega control in the original cubic configuration

The original projection has kernel E = C_M(X), retaining E/Q of order
three. A small critical pair makes every transposition rank one on full X.
The natural or augmentation moving cover supplies an equivariant core map,
and six-letter displacement coordinates give two alternatives: X is generated
by U and its full central fixed subgroup, or every actor fixing the critical
line has its displacement controlled by that line and the full fixed kernel.

This uses only the general representation lemmas from the natural branch's
OmegaExtension and OmegaControl. No natural replacement, graph marking or
central-layer hypothesis is transferred to the cubic graph. The private
import supplies the generic core-map construction and coordinate definitions;
the original projection, subgroup inclusion and free-amalgam embeddings are
used for all group and graph transports here.

On the actual consecutive critical paths a--z and d--c, with midpoints c
and a, put Y = U_d intersect Q_c. In the noncentral extension case the result is
[Y,X_z] <= [Z_a,Z_z] join [Y,X_z intersect Q_a], and X_z normalizes
Y join Z_a. This is the full-omega version of the inequality in MS93 (5.12)(1).
In the central-generation case, the fixed omega subgroup lies in the actual
radical-center orbit, proving X_z = Z_z only in that branch.

The selected-path, whole-core and literal C.1.32 applications retain the
original span, both covers, its central derived line and the exact shifted
seed/full-omega commutator comparison. The central-generation branch has not
been excluded or shown to satisfy the inequality. The terminal contradiction,
plane/Sylow branches, natural exhaustion and both final reconstruction
outcomes therefore remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), pp.866--867, and (5.12)(1), pp.924--925;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "X₀" => centralOmega L R
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev coverAction : Representation (ZMod 2) S (Additive W₀) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W₀ π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private theorem coverAction_conjugate (g : M) (v : Additive W₀) :
    ((coverAction h e hz hk (π g) v).toMul : M) = g*v.toMul*g⁻¹ := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation_apply _ _ _ _ g v
private def omegaAction : Representation (ZMod 2) S (Additive X₀) :=
  NormalElementaryQuotient.representation X₀ π (CubicEven.projection_surjective h e hz hk)
    ((CubicAction.projection_kernel h e hz hk).trans hk.symm)
private theorem omegaAction_conjugate (g : M) (v : Additive X₀) :
    ((omegaAction h e hz hk (π g) v).toMul : M) = g*v.toMul*g⁻¹ :=
  NormalElementaryQuotient.representation_apply _ _ _ _ g v
private def omegaMovedMap : Additive W₀ →ₗ[ZMod 2] Additive X₀ :=
  (Subgroup.inclusion (commutator_le_left X₀ (L.subgroupOf (L ⊔ R)))).toAdditive.toZModLinearMap 2

include h e in
private theorem omega_seed_fixed {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z) :
    X Rg a ⊓ centralizer (Z Rg z : Set (FreeAmalgam Rg)) = X Rg a ⊓ Q Rg z := by
  obtain ⟨t,hzt,hta⟩ := exists_adjacent_dist_sub_one Rg z a (by
    rw [SimpleGraph.dist_comm,p.critical.1,(sourceGeometry h).distance_constant _ p.start_color]
    exact sourceDistance_pos h)
  have hXt : X Rg a ≤ Q Rg t :=
    X_le_Q_of_dist_lt Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color t (by
      rw [SimpleGraph.dist_comm,(sourceGeometry h).distance_constant _ p.start_color]
      have hh := p.critical.1.trans ((sourceGeometry h).distance_constant _ p.start_color)
      change (cosetGraph Rg).dist t a < sourceDistance h
      change (cosetGraph Rg).dist a z = sourceDistance h at hh
      have hh' : (cosetGraph Rg).dist z a = sourceDistance h := by
        rwa [SimpleGraph.dist_comm]
      omega)
  apply le_antisymm
  · rintro x ⟨hx,hfix⟩
    exact ⟨hx,(sourceEdgeCentralizer h e z t p.end_color hzt) ▸ ⟨hXt hx,hfix⟩⟩
  · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg z p.end_color)))

include h e hz hk in
private theorem omega_transposition_rank_one
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (i j : Fin 6) (hij : i ≠ j) :
    Module.finrank (ZMod 2) (LinearMap.range (omegaAction h e hz hk (Equiv.swap i j)-LinearMap.id)) = 1 := by
  let A := (Z Rg a').comap (embedM Rg)
  have hmA : A.map (embedM Rg) = Z Rg a' := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg)
      rfl (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  let pr : CriticalPath Rg (sourceGeometry h) a' (alpha Rg) :=
    CriticalPath.ofPair p.end_color (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      (alpha Rg) rfl (sourceDistance_pos h) a' p.end_color p.critical)
  have hreverse : (Q Rg (alpha Rg)).relIndex (Z Rg a') < 4 := by
    rw [(small_critical_indices h e hz hk p hsmall).2]
    decide
  have hidx : (centralizer (A : Set M)).relIndex X₀ = 2 := by
    calc
      _ = ((X₀).map (embedM Rg) ⊓ centralizer (A.map (embedM Rg) : Set (FreeAmalgam Rg))).relIndex
          ((X₀).map (embedM Rg)) := by
        rw [map_inf_centralizer_of_injective _ (embedM_injective Rg),
          relIndex_map_map_of_injective _ _ (embedM_injective Rg),inf_relIndex_left]
      _ = _ := by
        rw [hmA,←graph_X h,omega_seed_fixed h e p,inf_relIndex_left]
        exact small_critical_omega_core_index h e hz hk pr hreverse
  obtain ⟨t,ht,him⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  have hdim : fixedCodim (omegaAction h e hz hk) (zpowers t) = 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim X₀
      π (CubicEven.projection_surjective h e hz hk)
      ((CubicAction.projection_kernel h e hz hk).trans hk.symm)] at hidx
    change 2 ^ fixedCodim (omegaAction h e hz hk) (A.map π) = 2 at hidx
    rw [him] at hidx
    exact (Nat.pow_right_injective (by decide : 1 < 2)) (hidx.trans (by decide : 2 = 2^1))
  apply BinaryPermutation.TransvectionCoreMap.swap_rank_one (omegaAction h e hz hk) ht _ i j hij
  rw [←fixedCodim_zpowers_eq_displacement_rank]
  exact hdim
private theorem omega_coordinates
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ j : (coreRepresentation (Fin 6)).IntertwiningMap (omegaAction h e hz hk),
      j.toLinearMap.range = (omegaMovedMap (L := L) (R := R)).range ∧
      (∀ i k : Fin 6, i ≠ k → j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.pairVector i k) ≠ 0) ∧
      (∀ z : Additive X₀, ∃ w : Full (Fin 6), ∀ g : Equiv.Perm (Fin 6),
        omegaAction h e hz hk g z-z = j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.displacement g w)) := by
  let ρ := omegaAction h e hz hk
  let inc := omegaMovedMap (L := L) (R := R)
  have hi : Function.Injective inc := by
    intro v w he
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun x : Additive X₀ => (x.toMul : M)) he
  have heq (g : Equiv.Perm (Fin 6)) (v : Additive (W₀)) :
      inc (coverAction h e hz hk g v) = ρ g (inc v) := by
    obtain ⟨m,rfl⟩ := CubicEven.projection_surjective h e hz hk g
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (coverAction_conjugate h e hz hk m v).trans (omegaAction_conjugate h e hz hk m (inc v)).symm
  obtain ⟨j,hjr,hj⟩ := Natural.Exhaustion.LargeDistance.SectionFive.coreMap_of_cover (coverAction h e hz hk) ρ inc hi heq (moved_subgroup_cover_model h e hz hk)
  refine ⟨j,hjr,hj,?_⟩
  intro z
  apply Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.exists_coordinates ρ j (fun i => hj _ _ (by
    simp only [ne_eq, Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]; omega)) _ z
  intro i
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact (omega_transposition_rank_one h e hz hk p hsmall i.castSucc i.succ (by
    simp only [ne_eq, Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]; omega)).le
private theorem omega_generation_graph
    (hgen : (omegaMovedMap (L := L) (R := R)).range ⊔ (omegaAction h e hz hk).invariants = ⊤) :
    X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer
        (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) := by
  have hlocal : X₀ = W₀ ⊔ (X₀ ⊓ center M) := by
    apply le_antisymm
    · intro x hx
      have hx' : Additive.ofMul (⟨x,hx⟩ : X₀) ∈
          (omegaMovedMap (L := L) (R := R)).range ⊔ (omegaAction h e hz hk).invariants :=
        hgen.symm ▸ Submodule.mem_top
      obtain ⟨v,⟨v₀,rfl⟩,w,hw,he⟩ := Submodule.mem_sup.mp hx'
      have hwc : (w.toMul : M) ∈ center M := by
        apply mem_center_iff.mpr
        intro m
        have hh := congrArg (fun z : Additive X₀ => (z.toMul : M))
          (hw (π m))
        rw [omegaAction_conjugate] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      have hm : (v₀.toMul : M) * (w.toMul : M) = x :=
        congrArg (fun z : Additive X₀ => (z.toMul : M)) he
      rw [←hm]
      exact (W₀ ⊔ (X₀ ⊓ center M)).mul_mem
        (mem_sup_left v₀.toMul.property) (mem_sup_right ⟨w.toMul.property,hwc⟩)
    · exact sup_le (commutator_le_left X₀ (L.subgroupOf (L ⊔ R))) inf_le_left
  have hh := congrArg (Subgroup.map (embedM Rg)) hlocal
  rw [Subgroup.map_sup,←graph_X h,graph_U_map h e hz] at hh
  have he : center M = centralizer ((⊤ : Subgroup M) : Set M) := by
    rw [coe_top,centralizer_univ]
  rw [he,←map_inf_centralizer_of_injective _ (embedM_injective Rg),
    ←graph_X h,←MonoidHom.range_eq_map] at hh
  change X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
    (X Rg (alpha Rg) ⊓ centralizer (Mbar Rg : Set (FreeAmalgam Rg))) at hh
  rw [←stabilizer_m_base] at hh
  exact hh

/-- Full X is generated by its original moved cover and fixed vectors, or
there is an explicit singleton-coordinate vector in that same omega layer.
The latter supplies the explicit witness for the permutation-extension
case still to be excluded by the source nonnormality argument. -/
private theorem omega_generation_or_singleton
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4) :
    (X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer
        (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))) ∨
      ∃ j : (coreRepresentation (Fin 6)).IntertwiningMap (omegaAction h e hz hk),
        j.toLinearMap.range = (omegaMovedMap (L := L) (R := R)).range ∧
        (∀ i k : Fin 6, i ≠ k → j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.pairVector i k) ≠ 0) ∧
        ∃ x : Additive X₀, ∀ g : Equiv.Perm (Fin 6),
          omegaAction h e hz hk g x-x = j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.displacement g (Pi.single 0 1)) := by
  obtain ⟨j,hjr,hj,hcoords⟩ := omega_coordinates h e hz hk p hsmall
  rcases Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.generation_or_singleton (omegaAction h e hz hk) j hcoords with hgen | hext
  · left
    apply omega_generation_graph h e hz hk
    rwa [hjr] at hgen
  · exact Or.inr ⟨j,hjr,hj,hext⟩

private theorem omega_displacement_value (g : M) (v : Additive X₀) :
    ((omegaAction h e hz hk (π g) v-v).toMul : M) = ⁅g,(v.toMul : M)⁆ := by
  rw [toMul_sub,div_eq_mul_inv]
  change ((omegaAction h e hz hk (π g) v).toMul : M) * (v.toMul : M)⁻¹ = _
  rw [omegaAction_conjugate]
  rfl

/-- Literal full-omega displacement control, with the original projection and
with the entire fixed kernel retained. -/
private theorem omega_singleton_commutator_control
    (j : (coreRepresentation (Fin 6)).IntertwiningMap (omegaAction h e hz hk))
    (hj : ∀ i k : Fin 6, i ≠ k → j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.pairVector i k) ≠ 0)
    (x : Additive X₀)
    (hx : ∀ g : Equiv.Perm (Fin 6), omegaAction h e hz hk g x-x =
      j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.displacement g (Pi.single 0 1)))
    (A : Subgroup M) (i k : Fin 6) (hik : i ≠ k)
    (hA : A.map π = zpowers (Equiv.swap i k))
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (omegaAction h e hz hk (Equiv.swap i k)-LinearMap.id)) = 1)
    (Y : Subgroup M)
    (hY : Y ≤ centralizer ((⁅X₀,A⁆ : Subgroup M) : Set M)) :
    ⁅Y,X₀⁆ ≤ ⁅X₀,A⁆ ⊔ ⁅Y,X₀ ⊓ centralizer (A : Set M)⁆ := by
  let N := ⁅X₀,A⁆ ⊔ ⁅Y,X₀ ⊓ centralizer (A : Set M)⁆
  let W : Submodule (ZMod 2) (Additive X₀) :=
    AddSubgroup.toZModSubmodule 2 (N.subgroupOf X₀).toAddSubgroup
  let r := j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.pairVector i k)
  obtain ⟨c,hc,_⟩ := Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.singleton_fixed_complement (omegaAction h e hz hk) j hj x hx i k hik
  obtain ⟨a,ha,hat⟩ := (show Equiv.swap i k ∈ A.map π from hA.symm ▸ mem_zpowers _)
  have hrR : (r.toMul : M) ∈ ⁅X₀,A⁆ := by
    have he := congrArg (fun v : Additive X₀ => (v.toMul : M)) hc
    rw [←hat,omega_displacement_value] at he
    rw [←he,commutator_comm X₀ A]
    exact commutator_mem_commutator ha c.toMul.property
  apply commutator_le.mpr
  intro y hy v hv
  have hgr : omegaAction h e hz hk (π y) r = r := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [omegaAction_conjugate]
    exact mul_inv_eq_iff_eq_mul.mpr (hY hy _ hrR).symm
  have hNW : r ∈ W := (le_sup_left : ⁅X₀,A⁆ ≤ N) hrR
  have hfix (w : Additive X₀)
      (hw : omegaAction h e hz hk (Equiv.swap i k) w = w) :
      omegaAction h e hz hk (π y) w-w ∈ W := by
    have hwa : (w.toMul : M) ∈ centralizer (A : Set M) := by
      intro a ha
      have hmem : π a ∈ zpowers (Equiv.swap i k) := hA ▸ mem_map_of_mem _ ha
      have hh := ((mem_fixedSpace_zpowers_iff (omegaAction h e hz hk) (Equiv.swap i k) w).mpr hw)
        ⟨π a,hmem⟩
      change omegaAction h e hz hk (π a) w = w at hh
      have he := congrArg (fun v : Additive X₀ => (v.toMul : M)) hh
      rw [omegaAction_conjugate] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    change ((omegaAction h e hz hk (π y) w-w).toMul : M) ∈ N
    rw [omega_displacement_value]
    exact (le_sup_right : ⁅Y,X₀ ⊓ centralizer (A : Set M)⁆ ≤ N)
      (commutator_mem_commutator hy ⟨w.toMul.property,hwa⟩)
  have hh := Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.singleton_displacement_control (omegaAction h e hz hk) j hj x hx i k hik hr
    (π y) hgr W hNW hfix (Additive.ofMul (⟨v,hv⟩ : X₀))
  change ((omegaAction h e hz hk (π y) (Additive.ofMul (⟨v,hv⟩ : X₀))-
    Additive.ofMul (⟨v,hv⟩ : X₀)).toMul : M) ∈ N at hh
  rwa [omega_displacement_value] at hh

include h e hz hk in
/-- The original omega layer is centrally generated, or every local actor
fixing the critical line satisfies the full-kernel displacement bound. -/
private theorem omega_generation_or_control
    {z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer
        (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∨
    ∀ Y : Subgroup (FreeAmalgam Rg), Y ≤ stabilizer Rg (alpha Rg) →
      Y ≤ centralizer ((⁅X Rg (alpha Rg),Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) →
      ⁅Y,X Rg (alpha Rg)⁆ ≤ ⁅X Rg (alpha Rg),Z Rg z⁆ ⊔
        ⁅Y,X Rg (alpha Rg) ⊓ Q Rg z⁆ := by
  rcases omega_generation_or_singleton h e hz hk p hsmall with hgen | ⟨j,_,hj,x,hx⟩
  · exact Or.inl hgen
  right
  intro Y hYG hYR
  let A := (Z Rg z).comap (embedM Rg)
  let Y₀ := Y.comap (embedM Rg)
  have hAm : A.map (embedM Rg) = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hYm : Y₀.map (embedM Rg) = Y :=
    map_comap_eq_self (hYG.trans_eq (stabilizer_m_base Rg))
  have hRm : (⁅X₀,A⁆ : Subgroup M).map (embedM Rg) =
      ⁅X Rg (alpha Rg),Z Rg z⁆ := by
    rw [map_commutator,←graph_X h,hAm]
  have hY₀ : Y₀ ≤ centralizer ((⁅X₀,A⁆ : Subgroup M) : Set M) := by
    intro y hy r hr
    apply embedM_injective Rg
    simpa only [map_mul] using hYR hy (embedM Rg r)
      (hRm ▸ mem_map_of_mem (embedM Rg) hr)
  obtain ⟨t,⟨i,k,hik,rfl⟩,ht⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  have hbound := omega_singleton_commutator_control h e hz hk j hj x hx A i k hik ht
    (omega_transposition_rank_one h e hz hk p hsmall i k hik) Y₀ hY₀
  have hK := omega_seed_fixed h e p
  have hm := map_mono (f := embedM Rg) hbound
  rw [Subgroup.map_sup,map_commutator,hYm,←graph_X h,hRm,map_commutator,hYm,
    ←map_inf_centralizer_of_injective _ (embedM_injective Rg),
    ←graph_X h,hAm,hK] at hm
  exact hm

include h e hz hk in
/-- The full-kernel alternative at every actual vertex, transported through
free-amalgam conjugation rather than a new action marking. -/
theorem small_critical_omega_generation_or_control_at
    {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4) :
    X Rg a = U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∨
    ∀ Y : Subgroup (FreeAmalgam Rg), Y ≤ stabilizer Rg a →
      Y ≤ centralizer ((⁅X Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) →
      ⁅Y,X Rg a⁆ ≤ ⁅X Rg a,Z Rg z⁆ ⊔ ⁅Y,X Rg a ⊓ Q Rg z⁆ := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color Rg p.start_color
  subst a
  have hbase : act Rg g⁻¹ (mVertex Rg g) = alpha Rg := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have hi : Function.Injective f := (MulAut.conj (g⁻¹)⁻¹).injective
  have hh := omega_generation_or_control h e hz hk (z := act Rg g⁻¹ z)
  rw [←hbase] at hh
  have hs : (Q Rg (act Rg g⁻¹ z)).relIndex
      (Z Rg (act Rg g⁻¹ (mVertex Rg g))) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ hi]
    exact hsmall
  rcases hh (p.act g⁻¹) hs with hgen | hcontrol
  · left
    apply map_injective hi
    rw [Subgroup.map_sup,←map_inf_centralizer_of_injective _ hi]
    simpa only [X_act,U_act,stabilizer_act] using hgen
  · right
    intro Y hYG hYR
    have hYG' : Y.map f ≤ stabilizer Rg (act Rg g⁻¹ (mVertex Rg g)) := by
      rw [stabilizer_act]
      exact map_mono hYG
    have hYR' : Y.map f ≤ centralizer
        ((⁅X Rg (act Rg g⁻¹ (mVertex Rg g)),Z Rg (act Rg g⁻¹ z)⁆ :
          Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [X_act,Z_act,←map_commutator,←map_commutator,
        commutator_eq_bot_iff_le_centralizer.mpr hYR,Subgroup.map_bot]
    have hb := hcontrol (Y.map f) hYG' hYR'
    rw [X_act,Z_act,Q_act,←map_commutator,←map_commutator,
      ←Subgroup.map_inf _ _ f hi,←map_commutator,←Subgroup.map_sup] at hb
    exact (map_le_map_iff_of_injective hi).mp hb

include h e hz hk in
/-- On the same consecutive critical paths, the noncentral extension case
satisfies the literal full-X inequality of MS93 (5.12)(1). It also normalizes
the original shifted kernel joined to the starting seed. -/
theorem point_shifted_omega_generation_or_control
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a) :
    let Y := U Rg d ⊓ Q Rg c
    let R₁ := ⁅Y,X Rg z ⊓ Q Rg a⁆
    (X Rg z = U Rg z ⊔
      (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) ∨
      (⁅Y,X Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔ R₁ ∧
        X Rg z ≤ normalizer ((Y ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) := by
  let Y := U Rg d ⊓ Q Rg c
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      z p.end_color p.critical)
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).2.1]
    decide
  rcases small_critical_omega_generation_or_control_at h e hz hk pr hs with hgen | hcontrol
  · exact Or.inl hgen
  right
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hUV : U Rg d ≤ V Rg a := (DistanceEight.U_le_Z Rg d).trans
    (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hYQa : Y ≤ Q Rg a := (inf_le_left.trans hUV).trans
      (V_le_Q Rg (geometry := sourceGeometry h) p.start_color (distance_gt_two h e hz hk))
  have hYG : Y ≤ stabilizer Rg z := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two c z q.end_color p.end_color (by rw [←hpc,p.dist_end,hl]))
  have hXN : X Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_X_le_vertex h e z p.end_color a pr.critical).trans (Z_normalized Rg a)
  have hRZ : ⁅X Rg z,Z Rg a⁆ ≤ Z Rg a := le_normalizer_iff_commutator_le_right.mp hXN
  have hZaX : Z Rg a ≤ X Rg a := (sourceGeometry h).omega_bound a p.start_color (by
    rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
  have hZzX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z p.end_color (by
    rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
  have hRline : ⁅X Rg z,Z Rg a⁆ = ⁅Z Rg a,Z Rg z⁆ := by
    rw [commutator_comm (X Rg z)]
    apply le_antisymm _ (commutator_mono le_rfl hZzX)
    exact (commutator_mono hZaX le_rfl).trans_eq
      (small_critical_omega_commutator h e hz hk p (by
        rw [(point_image_critical_indices_two h e hz hk u hR p).1]; decide))
  have hYR : Y ≤ centralizer ((⁅X Rg z,Z Rg a⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
    (hYQa.trans (Q_le_centralizer_X Rg a)).trans (centralizer_le (hRZ.trans hZaX))
  have hbound := hcontrol Y hYG hYR
  have hline := point_shifted_omega_kernel_placement h e hz hk u hR p q.start_color hda
  rw [hpc] at hline
  have hRY : ⁅Y,X Rg z ⊓ Q Rg a⁆ ≤ Y := hline.1.trans inf_le_left
  refine ⟨by simpa only [hRline] using hbound,?_⟩
  have hcom : ⁅X Rg z,Y⁆ ≤ Y ⊔ Z Rg a := by
    rw [commutator_comm]
    exact hbound.trans (sup_le (hRZ.trans le_sup_right) (hRY.trans le_sup_left))
  apply le_normalizer_iff.mpr
  intro x hx v hv
  have hm : (Y ⊔ Z Rg a).map (MulAut.conj x).toMonoidHom ≤ Y ⊔ Z Rg a := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXN hx)).le.trans le_sup_right)
    rintro _ ⟨y,hy,rfl⟩
    have hh := (Y ⊔ Z Rg a).mul_mem
      (hcom (commutator_mem_commutator hx hy)) (mem_sup_left hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)

include h in
private theorem omega_fixed_le_seed (a : Vertex Rg) (ha : color Rg a = false) :
    X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ≤ Z Rg a := by
  have hbase : X Rg (alpha Rg) ⊓
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ≤ Z Rg (alpha Rg) := by
    rintro x ⟨hx,hfix⟩
    rw [graph_X h] at hx
    obtain ⟨m,hm,rfl⟩ := hx
    obtain ⟨hmQ,_,hm2⟩ := (mem_omegaCenterIn_iff _ _).mp hm
    have hmR : m ∈ omegaCenterIn Rg := by
      refine (mem_omegaCenterIn_iff _ _).mpr ⟨h.relative_radical.twoCore_le hmQ,?_,hm2⟩
      intro r _
      apply embedM_injective Rg
      simp only [map_mul]
      exact hfix (embedM Rg r) (by
        change embedM Rg r ∈ stabilizer Rg (mVertex Rg 1)
        rw [stabilizer_m_base]; exact ⟨r,rfl⟩)
    rw [graph_Z]
    exact mem_map_of_mem _ (subset_normalClosure hmR)
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color Rg ha
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
  rw [←map_inf_centralizer_of_injective _ (MulAut.conj g⁻¹).injective,
    ←X_act,←stabilizer_act,←Z_act] at hh
  simpa only [alpha,act_mVertex,one_mul] using hh

include h in
/-- Central generation identifies X with its actual omega orbit Z. This
implication is conditional on central generation and preserves both layers
throughout the other branch. -/
theorem omega_eq_seed_of_central_generation
    (a : Vertex Rg) (ha : color Rg a = false)
    (hgen : X Rg a = U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) :
    X Rg a = Z Rg a := by
  apply le_antisymm
  · calc X Rg a = _ := hgen
         _ ≤ Z Rg a := sup_le (DistanceEight.U_le_Z Rg a) (omega_fixed_le_seed h a ha)
  · apply (sourceGeometry h).omega_bound a ha
    rw [(sourceGeometry h).distance_constant _ ha]
    exact sourceDistance_pos h

include h e hz hk in
/-- The actual selected span and shifted line retain the source control
alternative, with the central-generation branch explicitly identified. -/
theorem point_image_selected_omega_control
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
      ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
        (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 2 = alpha Rg ∧
      let c := p.walk.getVert (p.walk.length-2)
      let P := localZSpan Rg c (alpha Rg)
      let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
      let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
      Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
      Nat.card H = 2 ∧ H ≤ X Rg (alpha Rg) ∧
      (R₁ = ⊥ ∨ R₁ = H) ∧ R₁ ≤ U Rg d ⊓ U Rg z ∧
      R₁ ≤ centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      R₁ ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
      R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
      R₁ ≤ X Rg (alpha Rg) ⊓ X Rg c ∧
      (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆) ∧
      ((X Rg z = U Rg z ⊔
          (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
        X Rg z = Z Rg z) ∨
        (⁅U Rg d ⊓ Q Rg c,X Rg z⁆ ≤ ⁅Z Rg (alpha Rg),Z Rg z⁆ ⊔ R₁ ∧
          X Rg z ≤ normalizer (((U Rg d ⊓ Q Rg c) ⊔ Z Rg (alpha Rg) :
            Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)))) := by
  obtain ⟨z,p,d,q,hqa,hcard,hcentral,hradius,hHcard,hHX,hRalt,hRU,hRVa,hRVc,hRseed,hRX,hRident⟩ :=
    point_image_selected_shifted_omega_line h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  refine ⟨z,p,d,q,hqa,hcard,hcentral,hradius,hHcard,hHX,hRalt,hRU,hRVa,hRVc,hRseed,hRX,hRident,?_⟩
  rcases point_shifted_omega_generation_or_control h e hz hk u hR p q
    (by simp only [hl,Nat.reduceSub]) hqa with hgen | hcontrol
  · exact Or.inl ⟨hgen,omega_eq_seed_of_central_generation h z p.end_color hgen⟩
  · exact Or.inr hcontrol

omit hk in
include h e hz in
/-- Whole-core application of full omega control on the selected paths. Both covers,
the original nonsylow radical, and the odd cubic kernel are retained. -/
theorem coreExhaustion_or_cubic_omega_control :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            ⁅X Rg a,stabilizer Rg a⁆ = U Rg a) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
          ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 2 = alpha Rg ∧
          let c := p.walk.getVert (p.walk.length-2)
          let P := localZSpan Rg c (alpha Rg)
          let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
          let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
          Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
          Nat.card H = 2 ∧ H ≤ X Rg (alpha Rg) ∧
          (R₁ = ⊥ ∨ R₁ = H) ∧ R₁ ≤ U Rg d ⊓ U Rg z ∧
          R₁ ≤ centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          R₁ ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
          R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
          R₁ ≤ X Rg (alpha Rg) ⊓ X Rg c ∧
          (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆) ∧
      ((X Rg z = U Rg z ⊔
          (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
        X Rg z = Z Rg z) ∨
        (⁅U Rg d ⊓ Q Rg c,X Rg z⁆ ≤ ⁅Z Rg (alpha Rg),Z Rg z⁆ ⊔ R₁ ∧
          X Rg z ≤ normalizer (((U Rg d ⊓ Q Rg c) ⊔ Z Rg (alpha Rg) :
            Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)))))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint.2,hpoint.1,
      point_omega_stabilizer_commutator h e hz hk u hpoint.2.le,
      point_image_selected_omega_control h e hz hk u hpoint.2.le⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Full omega control in the literal C.1.32 consumer, retaining the central-generation, plane and Sylow branches. -/
theorem rankTwo_or_cubic_omega_control :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            ⁅X Rg a,stabilizer Rg a⁆ = U Rg a) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
          ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 2 = alpha Rg ∧
          let c := p.walk.getVert (p.walk.length-2)
          let P := localZSpan Rg c (alpha Rg)
          let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
          let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
          Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
          Nat.card H = 2 ∧ H ≤ X Rg (alpha Rg) ∧
          (R₁ = ⊥ ∨ R₁ = H) ∧ R₁ ≤ U Rg d ⊓ U Rg z ∧
          R₁ ≤ centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          R₁ ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
          R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
          R₁ ≤ X Rg (alpha Rg) ⊓ X Rg c ∧
          (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆) ∧
      ((X Rg z = U Rg z ⊔
          (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
        X Rg z = Z Rg z) ∨
        (⁅U Rg d ⊓ Q Rg c,X Rg z⁆ ≤ ⁅Z Rg (alpha Rg),Z Rg z⁆ ⊔ R₁ ∧
          X Rg z ≤ normalizer (((U Rg d ⊓ Q Rg c) ⊔ Z Rg (alpha Rg) :
            Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)))))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_omega_control h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
