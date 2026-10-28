module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.Theta
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.SourcePair.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.SourcePair.Numerics
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.QuotientAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.Contradiction

/-!
# The source wreath overgroup and its full overlap automizer

A T-compatible pair of actual binary parabolics gives a solvable overgroup
of L₁T in H. The universal solvable-overgroup exclusion 13.8.13 puts it in
H ∩ M. Once its wreath quotient is constructed, the theta comparison and
13.7.3(9) identify its two-residual with L₁ in the ambient subgroup lattice.

`exists_source_wreath_overgroup` completes this construction from the earlier
source outputs in `SourcePair.Input`, the universal solvable-overgroup
exclusion 13.8.13 and the theta identity 13.7.3(9). The actual projections of
the solvable L₁T select the T-compatible parabolics in the moving PSL₃(2)
factors. Their six-point core action supplies the quotient, including its
two-core kernel and order 72. No parabolic choice, action, quotient, residual
identity or automizer comparison is an input to this assembly.

The computed bound 27 ∤ |H| and the actual Sylow marking identify the full
overlap automizer image with the constructed H₁ image. The resulting D₈
equivalence uses the existing marked wreath calculation. The later marked
Â₆ automizer and terminal contradiction belong to the branch assembly.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952 (PDF p.969).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup

/-- Explicit conversion between the permutation and SL₂(2) wreath carriers. -/
noncomputable def s3WreathEquivModel : S3Wreath ≃* WreathModel.W :=
  RegularWreathProduct.congr
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm
    (MulEquiv.refl C2)

/-- The existing two-block construction can feed the established residual
and dihedral calculations without repeating either model calculation. -/
noncomputable def modelQuotientEquiv {X : Type*} [Group X]
    (a : TwoBlockQuotientData (H₁ := X)) : X ⧸ pCore 2 X ≃* WreathModel.W :=
  a.quotientEquiv.trans s3WreathEquivModel

variable {G : Type*} [Group G] [Finite G]
variable {H L₁ T : Subgroup G}

/-- Apply the genuine universal form of 13.8.13 to the constructed lift.
Its solvability and containment of T are proved from the pair geometry. -/
theorem overgroup_le_overlap (d : ParabolicPair H L₁ T) (G₁ M : Subgroup G)
    (hH : H ≤ G₁)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) : d.overgroup ≤ H ⊓ M :=
  le_inf d.overgroup_le (hex _ d.base_le_overgroup
    (d.overgroup_le.trans hH) d.overgroup_solvable)

/-- The earlier theta identity identifies the *ambient image* of O²(H₁).
The source assembly below supplies this quotient by the two-block action. -/
theorem overgroup_residual (d : ParabolicPair H L₁ T) (G₁ M : Subgroup G)
    (hH : H ≤ G₁)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (e : d.overgroup ⧸ pCore 2 d.overgroup ≃* WreathModel.W) :
    L₁ = (pResidual 2 d.overgroup).map d.overgroup.subtype :=
  residual_eq_of_theta L₁ d.overgroup (H ⊓ M)
    (le_sup_left.trans d.base_le_overgroup)
    (overgroup_le_overlap d G₁ M hH hex) htheta e

/-- The literal action of the constructed overgroup on the marked section.
`source_overlap_range_eq` below identifies the full overlap image with it. -/
noncomputable def overgroupActionEquivDihedral (d : ParabolicPair H L₁ T)
    (G₁ M : Subgroup G) (hH : H ≤ G₁)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (e : d.overgroup ⧸ pCore 2 d.overgroup ≃* WreathModel.W) :
    (quotientAction L₁ d.overgroup (normalizes_embedded_residual L₁ d.overgroup
      (overgroup_residual d G₁ M hH hex htheta e))).range ≃* D8 :=
  markedActionEquivDihedral L₁ d.overgroup
    (overgroup_residual d G₁ M hH hex htheta e) _ e

section SourceAssembly
variable {K K₀ : Subgroup G} (d : SourcePair.Input H L₁ T K K₀)
variable (G₁ M : Subgroup G) (hH : H ≤ G₁)
variable (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
  Group.IsSolvable J → J ≤ M)
variable (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
include d G₁ M hH hex htheta

/-- The selected parabolics and their literal quotient discharge the quotient
premise of the theta comparison. This is the ambient equality L₁ = O²(H₁)
in the moving PSL₃(2) branch; only earlier source outputs remain as inputs. -/
theorem source_overgroup_residual :
    L₁ = (pResidual 2 d.parabolicPair.overgroup).map d.parabolicPair.overgroup.subtype :=
  overgroup_residual d.parabolicPair G₁ M hH hex htheta
    d.parabolicPair.overgroupQuotientEquiv

/-- The full overlap image equals the image of the constructed H₁. The
order bound and shared Sylow subgroup are derived from the actual component
models and the ambient Sylow marking, rather than assumed image data. -/
theorem source_overlap_range_eq :
    (automizerAction L₁ (H ⊓ M)).range =
      (quotientAction L₁ d.parabolicPair.overgroup
        (normalizes_embedded_residual L₁ d.parabolicPair.overgroup
          (source_overgroup_residual d G₁ M hH hex htheta))).range := by
  obtain ⟨S, hS⟩ := d.sylow_marking
  apply automizer_range_eq L₁ d.parabolicPair.overgroup (H ⊓ M) H
    (overgroup_le_overlap d.parabolicPair G₁ M hH hex) inf_le_left
    (source_overgroup_residual d G₁ M hH hex htheta)
    d.parabolicPair.overgroupQuotientEquiv d.not_twentyseven_dvd_card S
  rw [hS]
  exact le_sup_right.trans d.parabolicPair.base_le_overgroup

/-- The actual Aut_{H ∩ M}(L₁/O₂(L₁)) is dihedral of order eight.
The equivalence transports the proved equality of literal action images. -/
noncomputable def sourceOverlapEquivDihedral :
    (automizerAction L₁ (H ⊓ M)).range ≃* D8 :=
  (MulEquiv.subgroupCongr (source_overlap_range_eq d G₁ M hH hex htheta)).trans
    (overgroupActionEquivDihedral d.parabolicPair G₁ M hH hex htheta
      d.parabolicPair.overgroupQuotientEquiv)

/-- The wreath overgroup construction in 13.8.16(1), with all its requested
source conclusions on the same ambient subgroup and the same marked section.
The witness is the lift of the selected parabolic pair. In particular it
contains T and is solvable; it is not the nonsolvable component orbit.

The exact earlier inputs are the moving-component data in `SourcePair.Input`,
H ≤ G₁ from the standing Hz setup, 13.8.13 (`hex`), and 13.7.3(9) (`htheta`).
The quotient and residual marking are outputs, suitable for the scalar-motion
and final-contradiction consumers without any additional model premise. -/
theorem exists_source_wreath_overgroup :
    ∃ H₁ : Subgroup G, L₁ ⊔ T ≤ H₁ ∧ H₁ ≤ H ⊓ M ∧ Group.IsSolvable H₁ ∧
      Nonempty (H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W) ∧
      L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3} ∧
      L₁ = (pResidual 2 H₁).map H₁.subtype ∧
      ∃ hn : H₁ ≤ normalizer (L₁ : Set G),
        (automizerAction L₁ (H ⊓ M)).range = (quotientAction L₁ H₁ hn).range ∧
        Nonempty ((automizerAction L₁ (H ⊓ M)).range ≃* D8) ∧
        Nat.card (L₁ ⧸ pCore 2 L₁) = 9 := by
  have hres := source_overgroup_residual d G₁ M hH hex htheta
  exact ⟨d.parabolicPair.overgroup, d.parabolicPair.base_le_overgroup,
    overgroup_le_overlap d.parabolicPair G₁ M hH hex, d.parabolicPair.overgroup_solvable,
    ⟨d.parabolicPair.overgroupQuotientEquiv⟩, htheta, hres,
    normalizes_embedded_residual L₁ d.parabolicPair.overgroup hres,
    source_overlap_range_eq d G₁ M hH hex htheta,
    ⟨sourceOverlapEquivDihedral d G₁ M hH hex htheta⟩,
    markedQuotient_card L₁ d.parabolicPair.overgroup hres
      d.parabolicPair.overgroupQuotientEquiv⟩

end SourceAssembly

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup
end
