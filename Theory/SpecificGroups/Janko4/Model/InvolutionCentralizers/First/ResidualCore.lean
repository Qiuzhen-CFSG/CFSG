module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual.Contained
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.CentralCoverCenteredModules
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Full two-core movement in the first J₄ centralizer residual

The marked scalar cubic fixes only the center of the extraspecial core.
Coprime decomposition and the center–Frattini equality show that its
commutators generate the entire core. The scalar lies in the perfect
residual, so the residual contains that core and moves it fully.

This identity lifts through any specified odd central cover: core images
are surjective through a central kernel, and the map is injective on the
two-core. Consequently every quasisimple image of the original perfect
residual kills its full two-core. The covering kernel is retained.

Source: Aschbacher–Smith 4.4.3, printed p.623, in the comparison of the
original involution-centralizer seed with the exceptional cubic residual.
The native ATLAS matrices and certificates retain their imported attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Janko4.InvolutionCentralizers.First
open CubicResidual QuotientExtension
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The marked cubic generates the whole extraspecial core by commutators. -/
theorem scalar_lift_moves_entire_core (x : centralizer) (hx : orderOf x = 3)
    (hs : centralizerExtension.rightHom x = scalarElement) :
    ⁅pCore 2 centralizer, zpowers x⁆ = pCore 2 centralizer := by
  let Q := pCore 2 centralizer
  let Z := (center Q).map Q.subtype
  let R := ⁅Q,zpowers x⁆
  let : IsExtraspecial 2 Q := centralizer_twoCore_extraspecial
  have hRQ : R ≤ Q := commutator_le_left _ _
  have hfixed : Q ⊓ Subgroup.centralizer (zpowers x : Set centralizer) ≤ Z := by
    intro q hq
    exact ⟨⟨q,hq.1⟩,scalar_lift_core_fixed x hs ⟨q,hq.1⟩
      (hq.2 x (mem_zpowers x)).symm,rfl⟩
  have hcop : Nat.Coprime (Nat.card (zpowers x)) (Nat.card Q) := by
    rw [Nat.card_zpowers,hx,centralizer_twoCore_card]
    norm_num
  let : Group.IsNilpotent Q := pCore_isPGroup.isNilpotent
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime Q (zpowers x)
    (by simp [normalizer_eq_top]) inferInstance hcop
  have hsup : R ⊔ Z = Q := le_antisymm
    (sup_le hRQ (map_subtype_le _)) (hsplit ▸ sup_le_sup_left hfixed R)
  have hfull : R.subgroupOf Q = ⊤ := by
    apply frattini_nongenerating
    apply (Subgroup.map_injective (f := Q.subtype) Q.subtype_injective)
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRQ,
      IsExtraspecial.frattini_eq_center (p := 2),
      ←MonoidHom.range_eq_map,range_subtype]
    exact hsup
  have hm := congrArg (map Q.subtype) hfull
  simpa only [map_subgroupOf_eq_of_le hRQ,←MonoidHom.range_eq_map,range_subtype] using hm

/-- The first centralizer's entire two-core belongs to its perfect residual. -/
theorem twoCore_le_residual : pCore 2 centralizer ≤ solvableResidual centralizer := by
  obtain ⟨x,hx,hs⟩ := exists_scalar_lift
  have hxp : x ∈ solvableResidual centralizer :=
    map_solvableResidual_le (Subgroup.centralizer ({x} : Set centralizer)).subtype
      (mem_map_of_mem _ (scalar_lift_mem_residual x hx hs))
  rw [←scalar_lift_moves_entire_core x hx hs]
  exact (commutator_mono le_rfl (zpowers_le.mpr hxp)).trans (commutator_le_right _ _)

/-- The intrinsic two-core of the perfect residual is fully moved. -/
theorem residual_core_fully_moved :
    ⁅pCore 2 (solvableResidual centralizer),
      (⊤ : Subgroup (solvableResidual centralizer))⁆ =
        pCore 2 (solvableResidual centralizer) := by
  let P := solvableResidual centralizer
  have hmap : (pCore 2 P).map P.subtype = pCore 2 centralizer := by
    exact (pCore_eq_map_of_normal_of_le 2 P twoCore_le_residual).symm
  apply le_antisymm (commutator_le_left _ _)
  apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
  rw [map_commutator,hmap,←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨x,hx,hs⟩ := exists_scalar_lift
  have hxp : x ∈ P :=
    map_solvableResidual_le (Subgroup.centralizer ({x} : Set centralizer)).subtype
      (mem_map_of_mem _ (scalar_lift_mem_residual x hx hs))
  calc
    pCore 2 centralizer = ⁅pCore 2 centralizer,zpowers x⁆ :=
      (scalar_lift_moves_entire_core x hx hs).symm
    _ ≤ ⁅pCore 2 centralizer,P⁆ := commutator_mono le_rfl (zpowers_le.mpr hxp)

/-- Every quasisimple quotient kills the native residual's entire two-core. -/
theorem residual_quasisimple_image_kills_twoCore
    {Y : Type*} [Group Y] [IsQuasisimple Y]
    (f : solvableResidual centralizer →* Y) (hf : Function.Surjective f) :
    pCore 2 (solvableResidual centralizer) ≤ f.ker := by
  let P := solvableResidual centralizer
  let : Finite Y := Finite.of_surjective f hf
  have hn : ((pCore 2 P).map f).Normal :=
    (inferInstance : (pCore 2 P).Normal).map f hf
  have hc : (pCore 2 P).map f ≤ center Y :=
    (le_sSup ⟨hn,pCore_isPGroup.map f⟩ : (pCore 2 P).map f ≤ pCore 2 Y).trans
      (IsQuasisimple.pCore_le_center 2)
  apply (Subgroup.map_eq_bot_iff _).mp
  conv_lhs => rw [←residual_core_fully_moved]
  rw [map_commutator,map_top_of_surjective f hf]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (center_le_centralizer _))

end Janko4.InvolutionCentralizers.First

namespace Janko4.InvolutionCentralizers.First
private theorem core_movement_of_odd_central_cover
    {X Y : Type*} [Group X] [Finite X] [Group Y]
    (q : X →* Y) (hq : Function.Surjective q) (hc : q.ker ≤ center X)
    (ho : Nat.Coprime 2 (Nat.card q.ker))
    (hm : ⁅pCore 2 Y,(⊤ : Subgroup Y)⁆ = pCore 2 Y) :
    ⁅pCore 2 X,(⊤ : Subgroup X)⁆ = pCore 2 X := by
  let R := ⁅pCore 2 X,(⊤ : Subgroup X)⁆
  have hR : R ≤ pCore 2 X := commutator_le_left _ _
  have hcore := q.map_pCore_of_central_kernel_centered hq hc (p := 2)
  have hmap : R.map q = (pCore 2 X).map q := by
    rw [show R = ⁅pCore 2 X,⊤⁆ from rfl,map_commutator,
      map_top_of_surjective q hq,hcore,hm]
  have hi := injective_comp_subtype_of_coprime_ker q ho (pCore 2 X) pCore_isPGroup
  apply le_antisymm hR
  intro x hx
  obtain ⟨r,hr,he⟩ := hmap.symm ▸ mem_map_of_mem q hx
  have heq : (⟨r,hR hr⟩ : pCore 2 X) = ⟨x,hx⟩ := hi he
  have heq' : r = x := congrArg (pCore 2 X).subtype heq
  exact heq' ▸ hr

/-- Full two-core movement lifts through every specified odd central cover
of the first involution centralizer, without dropping the covering kernel. -/
theorem residual_cover_core_fully_moved
    {X : Type*} [Group X] [Finite X]
    (q : X →* centralizer) (hq : Function.Surjective q) (hc : q.ker ≤ center X)
    (ho : Nat.Coprime 2 (Nat.card q.ker)) :
    ⁅pCore 2 (solvableResidual X),(⊤ : Subgroup (solvableResidual X))⁆ =
      pCore 2 (solvableResidual X) := by
  let P := solvableResidual X
  let e := MulEquiv.subgroupCongr (map_solvableResidual_eq q hq)
  let g : P →* solvableResidual centralizer := e.toMonoidHom.comp (q.subgroupMap P)
  have hg : Function.Surjective g := e.surjective.comp (q.subgroupMap_surjective _)
  have hk : g.ker = q.ker.subgroupOf P := by
    rw [show g = e.toMonoidHom.comp (q.subgroupMap P) from rfl,
      MonoidHom.ker_comp_of_injective _ _ e.injective,ker_subgroupMap]
  have hgc : g.ker ≤ center P := by
    intro x hx
    have hqx : (x : X) ∈ q.ker := by
      change x ∈ q.ker.subgroupOf P
      rwa [←hk]
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hc hqx) y))
  have hgo : Nat.Coprime 2 (Nat.card g.ker) := by
    rw [hk]
    exact ho.of_dvd_right (card_dvd_of_injective (P.subtype.subgroupComap q.ker)
      (fun x y hh => Subtype.ext (Subtype.ext
        (congrArg (fun z : q.ker => (z : X)) hh))))
  exact core_movement_of_odd_central_cover g hg hgc hgo residual_core_fully_moved

/-- A quasisimple image of the original first-centralizer residual kills
its entire two-core, even before the odd central covering kernel is removed. -/
theorem residual_cover_quasisimple_image_kills_twoCore
    {X Y : Type*} [Group X] [Finite X] [Group Y] [IsQuasisimple Y]
    (q : X →* centralizer) (hq : Function.Surjective q) (hc : q.ker ≤ center X)
    (ho : Nat.Coprime 2 (Nat.card q.ker))
    (f : solvableResidual X →* Y) (hf : Function.Surjective f) :
    pCore 2 (solvableResidual X) ≤ f.ker := by
  let : Finite Y := Finite.of_surjective f hf
  have hn : ((pCore 2 (solvableResidual X)).map f).Normal :=
    (inferInstance : (pCore 2 (solvableResidual X)).Normal).map f hf
  have hz : (pCore 2 (solvableResidual X)).map f ≤ center Y :=
    (le_sSup ⟨hn,pCore_isPGroup.map f⟩ :
      (pCore 2 (solvableResidual X)).map f ≤ pCore 2 Y).trans
      (IsQuasisimple.pCore_le_center 2)
  apply (Subgroup.map_eq_bot_iff _).mp
  conv_lhs => rw [←residual_cover_core_fully_moved q hq hc ho]
  rw [map_commutator,map_top_of_surjective f hf]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hz.trans (center_le_centralizer _))
end Janko4.InvolutionCentralizers.First
