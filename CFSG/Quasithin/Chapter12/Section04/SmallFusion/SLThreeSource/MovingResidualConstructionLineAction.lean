module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionAssembly
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PResidual.CubicActionKernel

/-!
# The centralizing line of the actual moving span

Restrict the actual N_G(L)-action on L/O₂(L) to X and identify its kernel
with X intersected with the embedded normalizer-action kernel. The actual
L₁ is two-perfect and acts nontrivially: centerlessness identifies its
inner-action kernel with its intersection with O₂(L), and its cubic
quotient excludes containment there. The order-336 automorphism theorem
and the order-nine quotient of X now give the literal centralizing line
order three, without assuming that O₂(X) acts trivially on L/O₂(L).

Source: Aschbacher–Smith, proof of 12.4.6, printed p.814.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
private theorem componentCoreAction_restrict_ker
    (hc : center (L ⧸ pCore 2 L) = ⊥) :
    ((componentCoreAction L).comp (inclusion L.le_normalizer)).ker = pCore 2 L := by
  exact pCoreJoinAction_restrict_ker 2 (L := L) (U := ⊥) bot_le hc

omit [Finite G] in
private theorem mem_coreActionKernel_iff (L : Subgroup G)
    (x : normalizer (L : Set G)) :
    (x : G) ∈ coreActionKernel L ↔ x ∈ (componentCoreAction L).ker := by
  change (x : G) ∈ (componentCoreAction L).ker.map (normalizer (L : Set G)).subtype ↔ _
  rw [mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

namespace LocalGeometry
variable (d : LocalGeometry D)

private theorem lineResidual_not_le_coreActionKernel
    (ext : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (hFE : fixedSubgroup L V ≤ d.E) : ¬ d.L₁ ≤ coreActionKernel L := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply bot_unique
    intro x hx
    apply ext.quotientEquiv.map_eq_one_iff.mp
    exact Matrix.PSL3Two.center_eq_bot.le
      ((centerCongr ext.quotientEquiv ⟨x, hx⟩).property)
  intro hK
  let i : d.L₁ →* L := inclusion (d.lineResidual_le.trans inf_le_left)
  have hi (x : d.L₁) : i x ∈ pCore 2 L := by
    rw [← componentCoreAction_restrict_ker hz]
    exact (mem_coreActionKernel_iff L _).mp (hK x.property)
  let f : d.L₁ →* pCore 2 L := i.codRestrict _ hi
  have hf := d.lineResidual_twoPerfect.hom_eq_one_of_isPGroup pCore_isPGroup f
  have hbot : d.L₁ = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he := DFunLike.congr_fun hf ⟨x, hx⟩
    exact congrArg (fun a : pCore 2 L => ((a : L) : G)) he
  have hd := card_quotient_dvd_card (pCore 2 d.L₁)
  rw [d.lineResidual_quotient_card ext hne hFE, hbot, card_bot] at hd
  norm_num at hd

/-- The actual centralizing kernel image in the moving-span quotient has order three. -/
theorem centralizingLine_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) :
    Nat.card (centralizingLine L d.movingSpan) = 3 := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hFE := d.fixed_le_plane h structural marked hmodel hne hescape
  obtain ⟨_, _, _, hNE, _⟩ := d.escape_geometry h structural marked hmodel hne hescape
  have hCM := d.plane_centralizer_le_normalizer h structural marked hmodel hne hescape
  have hXM := (d.movingSpan_le_centralizer hNE).trans hCM
  let f := (componentCoreAction L).comp (inclusion hXM)
  have hk : f.ker = (d.movingSpan ⊓ coreActionKernel L).subgroupOf d.movingSpan := by
    ext x
    change f x = 1 ↔ (x : G) ∈ d.movingSpan ∧ (x : G) ∈ coreActionKernel L
    rw [and_iff_right x.property]
    exact (mem_coreActionKernel_iff L (inclusion hXM x)).symm
  let P := d.L₁.subgroupOf d.movingSpan
  let e := subgroupOfEquivOfLe d.lineResidual_le_movingSpan
  have hp : IsPPerfect 2 P := d.lineResidual_twoPerfect.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hout : ¬ P ≤ f.ker := by
    intro hPk
    apply d.lineResidual_not_le_coreActionKernel ext hne hFE
    intro x hx
    have hmem := hPk (show (⟨x, d.lineResidual_le_movingSpan hx⟩ : d.movingSpan) ∈ P from hx)
    rw [hk] at hmem
    exact hmem.2
  have h9 := (d.movingSpan_quotient h structural marked hmodel hne hescape hmoves).2
  let eq := ext.quotientEquiv.trans Matrix.PSL3Two.equiv
  have hAut : Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 :=
    (Nat.card_congr (MulAut.congr eq).toEquiv).trans Matrix.PSL3Two.Automorphisms.card_aut
  have hc := f.card_kernel_image_cubic P hp hout h9 (by rw [hAut]; decide)
  rw [hk] at hc
  exact hc

end LocalGeometry

/-- The exact source callback, with only the earlier structural and module inputs. -/
theorem movingCentralizingLineCalculation
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    MovingCentralizingLineCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d hescape hmoves
  exact d.centralizingLine_card h structural marked hmodel hne hescape hmoves

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

