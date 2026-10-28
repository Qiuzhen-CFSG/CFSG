module
public import CFSG.Quasithin.ChapterG.Section10.Components.Exchanged
public import Theory.Representation.BinaryTransvectionGroups.NormalFullCenter
public import Theory.Representation.BinaryOffender.Homogeneous.Core
public import Theory.Representation.NormalComponentConstituents.Orthogonal
public import Theory.Representation.Quotient

/-!
# Completing the exchanged constituent from its proper action

The separate assertion G.10.15(3) says that the actual H-action on I is proper
in GL(I). Under this explicit premise the full-center geometry excludes
I contained in v-perp: irreducibility and full-center generation would force
H to induce GL(I).

The orthogonal complement of the X-orbit span is HX-invariant. If it were
nonzero, G.10.10 would put v in it, contradicting the preceding exclusion.
Thus the orbit spans V. Commutativity of X and faithfulness on V then make
N_X(I) faithful on I; the odd linear centralizer of the irreducible H-action
makes N_X(I) faithful on H as well.

This completes the implication from (3) to the remaining assertions of
Aschbacher--Smith G.10.15(1)(ii), printed pp.361--362. The non-GL premise
remains explicit; this module does not prove G.10.15(3).
-/

public noncomputable section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
open Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

theorem exchanged_constituent_not_le_axis (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hv : v ∉ I)
    (hproper : ¬ Function.Surjective
      (invariantSubspace ρ (componentOrbit L ⊤) I hI.invariant).toRepresentation.asGroupHom) :
    ¬ I ≤ (B v).ker := by
  intro haxis
  obtain ⟨x,hx,hop,hdis,hindex,hgeo⟩ := h.exchanged_constituent_geometry hn hL hm S hnX hind hI hv
  have haxis' : I ⊓ (B v).ker = I := inf_eq_left.mpr haxis
  dsimp only at hgeo
  rw [haxis'] at hgeo
  obtain ⟨i,hi0,hvi,hiW,hcenter⟩ := hgeo
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  let N := subspaceStabilizer ρ I
  let Y := N.subgroupOf X
  let σ := stabilizerRepresentation ρ I
  let α : Y →* N :=
    { toFun := fun y => ⟨((y:X):G),y.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let e := subgroupOfEquivOfLe hI.invariant
  let R := invariantSubspace ρ H I hI.invariant
  have hiR : IsIrreducible R.toRepresentation :=
    hI.isIrrPlus.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H
  have hiσ : IsIrreducible (σ.comp (H.subgroupOf N).subtype) := by
    change IsIrreducible (R.toRepresentation.comp e.toMonoidHom)
    exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective R.toRepresentation).mpr hiR
  have hfull : ∀ f : Module.Dual (ZMod 2) I, f i = 0 →
      ∃ a : Y, ∀ w : I, σ (α a) w = w + f w • i := by
    intro f hf
    obtain ⟨a,ha⟩ := hcenter.full f hf
    exact ⟨a, fun w => Subtype.ext (ha w)⟩
  have hsurj := Representation.normalAction_surjective_of_full_center σ (H.subgroupOf N) α
    hiσ (hI.isIrrPlus.finrank_gt_two ρ H) i (fun he => hi0 (congrArg Subtype.val he)) hfull
  apply hproper
  intro a
  obtain ⟨g,hg⟩ := hsurj a
  exact ⟨e g,hg⟩



/-- G.10.15(3) forces the exchanged constituent orbit to be the whole module. -/
theorem exchanged_orbitSpan_eq_top (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hv : v ∉ I)
    (hproper : ¬ Function.Surjective
      (invariantSubspace ρ (componentOrbit L ⊤) I hI.invariant).toRepresentation.asGroupHom) :
    Homogeneous.orbitSpan ρ X I = ⊤ := by
  let O := Homogeneous.orbitSpan ρ X I
  have hHI := Homogeneous.orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus
  have hXI := Homogeneous.orbitSpan_invariant ρ X I
  have horth : B.orthogonal O = ⊥ := by
    by_contra hne
    have hvO := h.point_mem_normal_component_subspace hn hL hm S hnX hind
      (B.orthogonal O) (orthogonal_invariant ρ B h.preserves hHI)
      (orthogonal_invariant ρ B h.preserves hXI) hne
    apply h.exchanged_constituent_not_le_axis hn hL hm S hnX hind hI hv hproper
    intro u hu
    exact h.alternating.isRefl u v (hvO u (Homogeneous.le_orbitSpan ρ X I hu))
  have hh := B.orthogonal_orthogonal h.nondegenerate h.alternating.isRefl O
  rw [horth,LinearMap.BilinForm.orthogonal_bot] at hh
  exact hh.symm

omit [FiniteDimensional (ZMod 2) V] in
/-- An actor fixing a seed pointwise fixes its orbit under the commutative actor. -/
theorem eq_one_of_fixes_spanning_constituent
    {I : Submodule (ZMod 2) V} (hgen : Homogeneous.orbitSpan ρ X I = ⊤)
    {y : G} (hy : y ∈ X) (hfix : ∀ u ∈ I, ρ y u = u) : y = 1 := by
  have hO : Homogeneous.orbitSpan ρ X I ≤ (ρ y - LinearMap.id).ker := by
    apply iSup_le
    rintro x _ ⟨u,hu,rfl⟩
    change ρ y (ρ x u) - ρ x u = 0
    apply sub_eq_zero.mpr
    calc
      ρ y (ρ x u) = ρ x (ρ y u) := by
        rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul]
        exact congrArg (fun g : G => ρ g u) (congrArg Subtype.val (mul_comm (⟨y,hy⟩ : X) x))
      _ = ρ x u := congrArg (ρ x) (hfix u hu)
  apply h.faithful
  apply LinearMap.ext
  intro u
  rw [hgen] at hO
  have hh : ρ y u - u = 0 := hO Submodule.mem_top
  simpa only [map_one,Module.End.one_apply] using sub_eq_zero.mp hh

omit [FiniteDimensional (ZMod 2) V] in
/-- The exchanged stabilizer acts faithfully on its constituent. -/
theorem spanning_constituent_stabilizer_faithful
    {I : Submodule (ZMod 2) V} (hgen : Homogeneous.orbitSpan ρ X I = ⊤) :
    Function.Injective ((stabilizerRepresentation ρ I).comp
      (inclusion (show ((subspaceStabilizer ρ I) ⊓ X) ≤ subspaceStabilizer ρ I from inf_le_left))) := by
  apply (injective_iff_map_eq_one _).mpr
  intro y hy
  apply Subtype.ext
  apply h.eq_one_of_fixes_spanning_constituent hgen y.property.2
  intro u hu
  have he := congrArg (fun f : Module.End (ZMod 2) I => (f ⟨u,hu⟩ : V)) hy
  exact he

/-- The exchanged stabilizer has trivial centralizer of the component orbit. -/
theorem spanning_constituent_stabilizer_centralizer_eq_bot
    {H : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ H I)
    (hgen : Homogeneous.orbitSpan ρ X I = ⊤) :
    ((subspaceStabilizer ρ I) ⊓ X) ⊓ centralizer (H : Set G) = ⊥ := by
  let P := ((subspaceStabilizer ρ I) ⊓ X) ⊓ centralizer (H : Set G)
  have hPX : P ≤ X := inf_le_left.trans inf_le_right
  have hp : IsPGroup 2 P := (IsElementaryAbelian.isPGroup 2 X).to_le hPX
  have hfix := Homogeneous.IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes ρ hI hp
    (show P ≤ centralizer (H : Set G) from inf_le_right)
    (show P ≤ subspaceStabilizer ρ I from inf_le_left.trans inf_le_left)
  apply bot_unique
  intro y hy
  apply mem_bot.mpr
  exact h.eq_one_of_fixes_spanning_constituent hgen (hPX hy)
    (fun u hu => hfix hu ⟨y,hy⟩)



/-- The exchanged alternative is complete once the actual component action
on I is proper in GL(I), the separate assertion G.10.15(3). -/
theorem exchanged_constituent_completion (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hv : v ∉ I)
    (hproper : ¬ Function.Surjective
      (invariantSubspace ρ (componentOrbit L ⊤) I hI.invariant).toRepresentation.asGroupHom) :
    ExchangedConstituentGeometry ρ B v W X I ∧
    Homogeneous.orbitSpan ρ X I = ⊤ ∧
    let Y := (subspaceStabilizer ρ I).subgroupOf X
    (∀ y : Y, (∀ u : I, ρ ((y : X) : G) u = u) → y = 1) ∧
    (∀ y : Y, ((y : X) : G) ∈ centralizer (componentOrbit L ⊤ : Set G) → y = 1) := by
  have hgen := h.exchanged_orbitSpan_eq_top hn hL hm S hnX hind hI hv hproper
  refine ⟨h.exchanged_constituent_geometry hn hL hm S hnX hind hI hv,hgen,?_,?_⟩
  · intro y hy
    apply Subtype.ext
    apply Subtype.ext
    exact h.eq_one_of_fixes_spanning_constituent hgen y.val.property (fun u hu => hy ⟨u,hu⟩)
  · intro y hy
    apply Subtype.ext
    apply Subtype.ext
    apply mem_bot.mp
    rw [← h.spanning_constituent_stabilizer_centralizer_eq_bot hI.isIrrPlus hgen]
    exact ⟨⟨y.property,y.val.property⟩,hy⟩

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
