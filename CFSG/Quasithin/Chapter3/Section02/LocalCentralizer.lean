module

public import CFSG.Quasithin.Chapter3.Section02.LocalModule
public import Theory.GroupTheory.PCoreResidualFrattiniKernel

/-!
# The original Sylow centralizer of the local FSU module

The local action kills O₂(L₀T), because its module lies in R₂(L₀T).
Its actor kernel has the precise core–Frattini bound from D.3.3(2), and
L₀ is the two-residual. The Sylow Frattini-kernel theorem therefore
identifies the Sylow/kernel intersection with O₂(L₀T). Transport through
the original conjugation map gives exactly C_T(V), preserving both
original subgroups in G.

Source: Aschbacher–Smith, Lemma 3.2.2(8), combined manuscript of
1 March 2004, printed p.579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- The actual source equality C_T(V)=O₂(L₀T). -/
theorem sylow_centralizer_module
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    (T : Subgroup G) ⊓ centralizer (D.moduleSubgroup : Set G) = (localJoin T L).pCoreIn 2 := by
  let H := localJoin T L
  let X := (localOrbit T L).subgroupOf H
  let S : Sylow 2 H := T.subtype le_sup_right
  let ρ := ReducedNormal.representation H
  let W := orbitSpan ρ ⊤ D.seedSpace
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ D.seedSpace)
  have hi := D.local_internal_module h127
  let := hi.normal
  have hgen : X ⊔ (S : Subgroup H) = ⊤ := by
    change (localOrbit T L).subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hR : pResidual 2 H = X := pResidual_eq_of_isPPerfect_sup X S
    ((pResidual_eq_top_iff 2 X).mp hi.residual) S.isPGroup' hgen
  have hc : pCore 2 H ≤ (actionHom ρ).ker := by
    rw [ReducedNormal.representation_action_kernel]
    exact le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 H)
  have hkill : pCore 2 H ≤ f.ker := by
    rw [invariantActionHom_ker]
    intro g hg
    exact ⟨mem_top _, fun v _ => (actionHom_eq_one_iff ρ g).mp (hc hg) v⟩
  have hkX : X ⊓ f.ker ≤ (coreFrattiniIn X).map X.subtype := by
    intro x hx
    apply hi.orbit_actorKernel_le_coreFrattini
    rw [invariantActionHom_ker] at hx
    exact ⟨hx.1, hx.2.2⟩
  have hk : pResidual 2 H ⊓ f.ker ≤
      (coreFrattiniIn (pResidual 2 H)).map (pResidual 2 H).subtype := by
    rw [hR]
    exact hkX
  have he := f.sylow_inf_ker_eq_pCore_of_residual_frattini_kernel
    (invariantActionHom_surjective ρ W _) S hkill hk
  have hmap : ((S : Subgroup H) ⊓ f.ker).map H.subtype =
      (T : Subgroup G) ⊓ centralizer (D.moduleSubgroup : Set G) := by
    ext g
    constructor
    · rintro ⟨x, ⟨hxS, hxf⟩, rfl⟩
      refine ⟨hxS, mem_centralizer_iff.mpr ?_⟩
      intro v hv
      rw [← D.local_orbitImage_eq_module] at hv
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hv
      have hfix : ∀ z ∈ W, ρ x z = z := by
        rw [invariantActionHom_ker] at hxf
        exact hxf.2
      have hh := congrArg (fun z : Additive (ReducedNormal.ModuleGroup H) => z.toMul.val.val)
        (hfix (Additive.ofMul w) hw)
      change (x : G) * w.val.val * (x : G)⁻¹ = w.val.val at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · rintro ⟨hgT, hgC⟩
      let x : H := ⟨g, (show (T : Subgroup G) ≤ H from le_sup_right) hgT⟩
      refine ⟨x, ⟨hgT, ?_⟩, rfl⟩
      rw [invariantActionHom_ker]
      refine ⟨mem_top _, ?_⟩
      intro v hv
      apply ReducedNormal.representation_fixes_of_centralizes_subspaceImage H W x
        (by rwa [D.local_orbitImage_eq_module]) v hv
  have hm := congrArg (map H.subtype) he
  rw [hmap] at hm
  exact hm

/-- Both original local module conclusions in 3.2.2(8) hold in FSU. -/
theorem local_module_reduced_and_centralizer
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    IsPReduced 2 (D.moduleSubgroup.subgroupOf (localJoin T L)) ∧
      (T : Subgroup G) ⊓ centralizer (D.moduleSubgroup : Set G) =
        (localJoin T L).pCoreIn 2 :=
  ⟨D.module_reduced h127, D.sylow_centralizer_module h127⟩

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
