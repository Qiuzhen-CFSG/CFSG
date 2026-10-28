module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Inputs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Sylow
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Cubic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Normalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Marking

/-!
# Applications of the checked orthogonal reductions to the original source

The first application derives C_T(L) = 1, O₂(LT) = V, and actual Sylow
placement in L once the odd-degree calculation supplies T = T_L. It also
places the original Y and P inside the characteristic-two local G_P.
The second application finishes the odd-index residual equality from
normality, Sylow containment, and two-generation of the actual L₂.

The input record contains only earlier source conclusions. The remaining
premises belong to the cubic Cartan and relative-component arguments.
Constructing the orthogonal marking and proving X is a Cartan of Y remain
open. These applications do not assert completion of the p.774 paragraph.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, printed p.774.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)

include d

/-- Discharge the cohomology and local-placement steps on the original source.
The equality T = T_L must still be supplied by the odd-degree argument. -/
theorem source_sylow_and_normalizer (hTL : sourceTL T L = (T : Subgroup G)) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 = V ∧
      (T : Subgroup G) ≤ L ∧
      (∃ t : Sylow 2 L, (t : Subgroup L).map L.subtype = (T : Subgroup G)) ∧
      coreNormalizer V H h ∈ Chapter1.He G ∧
      orthogonalJoin (f.Li 1) V h ≤ coreNormalizer V H h ∧
      ((pairCore V H h).subgroupOf (orthogonalJoin (f.Li 1) V h)).Normal := by
  exact ⟨sylow_centralizer_of_omega_fixed D d.omega_fixed,
    join_core_eq D S m d.seed_core d.omega_fixed,
    sylow_le_component D S m d.seed_core d.omega_fixed hTL,
    sylow_placement D S m d.seed_core d.omega_fixed hTL,
    coreNormalizer_mem_He f d.conjugator_mem d.axis_eq_plane d.local_core,
    orthogonalJoin_le_coreNormalizer d.source d.conjugator_mem (f.Li 1) d.local_core,
    pairCore_normal_in_orthogonalJoin d.source d.conjugator_mem (f.Li 1) d.local_core⟩

/-- The component calculation's remaining premises finish the literal
O^{2′}(G_P) equality; O²(H) has not been substituted for this residual. -/
theorem source_orthogonalJoin_eq_oddResidual
    (hres : primeToResidual 2 (f.Li 1) = ⊤)
    (hn : ((orthogonalJoin (f.Li 1) V h).subgroupOf (coreNormalizer V H h)).Normal)
    (hT : (T : Subgroup G) ≤ orthogonalJoin (f.Li 1) V h) :
    orthogonalJoin (f.Li 1) V h =
      (primeToResidual 2 (coreNormalizer V H h)).map (coreNormalizer V H h).subtype :=
  orthogonalJoin_eq_oddResidual d.source d.conjugator_mem (f.Li 1) d.local_core hres hn hT

/-- The actual common-core input specializes the coprime cubic contradiction.
The Cartan argument must construct this order-three subgroup and prove the
two displayed action properties; they are not fields of `OrthogonalInput`. -/
theorem source_cubic_contradiction (C : Subgroup G) (hC : Nat.card C = 3)
    (hn : C ≤ normalizer (pairCore V H h : Set G))
    (hfixed : pairCore V H h ⊓ centralizer (C : Set G) = ⊥)
    (hscalar : ⁅L,C⁆ ≤ V) : False :=
  source_cubic_obstruction d.source f d.conjugator_mem d.conjugates_disjoint
    d.axis_eq_plane d.local_core C hC hn hfixed hscalar

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
