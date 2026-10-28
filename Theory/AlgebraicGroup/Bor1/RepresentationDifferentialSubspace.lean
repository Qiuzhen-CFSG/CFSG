module

public import Theory.AlgebraicGroup.Bor1.ClosedSubgroupPreimageTangent
public import Theory.AlgebraicGroup.Bor1.GeneralLinearSubspaceStabilizerTangent
public import Theory.AlgebraicGroup.Bor1.TangentDimension
public import Theory.AlgebraicGroup.Dimension.Strict

/-!
# Integrating differential-stable subspaces

Over an algebraically closed field of characteristic zero, a subspace of a
rational representation of a connected algebraic group is invariant under the
group when it is preserved by every operator in the identity differential.

The proof forms the reduced closed preimage of the standard general-linear
subspace stabilizer.  Characteristic-zero tangent exactness for reduced closed
preimages, together with the explicit tangent calculation for that stabilizer,
shows that the source stabilizer has every ambient tangent direction.  Thus its
tangent finrank and dimension equal those of the ambient group.  The stabilizer
contains the identity component, and connectedness makes it the whole group.
The preimage theorem supplies the Cartier/separability step, so no derivative
calculation is passed incorrectly through a radical ideal.

This is the representation-theoretic integration consequence of the automatic
characteristic-zero separability principle in Bor1 Chapter 3, 9.1.
-/

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped Cardinal

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [CharZero k] in
private theorem closedSubgroup_eq_top_of_full_identityTangent
    (K : ClosedSubgroup G) (hG : Variety.IsConnected G)
    (hfull : LinearMap.range
      (identityTangentMorphismLinearMap K.inclusion) = ⊤) :
    K = ClosedSubgroup.top := by
  have hfinrank :
      Module.finrank k (IdentityPointDerivation K.carrierVariety) =
        Module.finrank k (IdentityPointDerivation G) := by
    calc
      Module.finrank k (IdentityPointDerivation K.carrierVariety) =
          Module.finrank k
            (LinearMap.range
              (identityTangentMorphismLinearMap K.inclusion)) :=
        (LinearMap.finrank_range_of_inj
          (identityTangentMorphismLinearMap_inclusion_injective K)).symm
      _ = Module.finrank k
          (⊤ : Submodule k (IdentityPointDerivation G)) := by
        rw [hfull]
      _ = Module.finrank k (IdentityPointDerivation G) := by simp
  have htoNat : Cardinal.toNat (Variety.dimension K.carrierVariety) =
      Cardinal.toNat (Variety.dimension G) := by
    simpa only [identityPointDerivation_finrank_eq_dimension] using hfinrank
  have hKfin : Variety.dimension K.carrierVariety < ℵ₀ :=
    variety_dimension_lt_aleph0 K.carrierVariety
  have hGfin : Variety.dimension G < ℵ₀ :=
    variety_dimension_lt_aleph0 G
  have hdim : Variety.dimension K.carrierVariety = Variety.dimension G := by
    apply le_antisymm
    · exact (Cardinal.toNat_le_iff_le_of_lt_aleph0 hKfin hGfin).mp htoNat.le
    · exact (Cardinal.toNat_le_iff_le_of_lt_aleph0 hGfin hKfin).mp htoNat.ge
  have hcomponent : identityComponent G ⊆
      (K.toSubgroup : Set (Variety.Point G)) :=
    (closedSubgroup_dimension_eq_iff_contains_identityComponent G K).mp hdim
  have hcomponentTop : identityComponent G = Set.univ :=
    (identityComponent_eq_univ_iff_isConnected G).mpr hG
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · exact fun _ _ => trivial
  · intro g _
    exact hcomponent (by rw [hcomponentTop]; trivial)

/-- A subspace preserved by every infinitesimal representation operator is
preserved by every point of a connected algebraic group in characteristic
zero. -/
public theorem differential_stable_subspace_invariant
    (rho : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V b (f.onPoints g) = rho.action g)
    (W : Submodule k V) (hG : Variety.IsConnected G)
    (hstable : ∀ D w, w ∈ W →
      rationalRepresentationDifferential rho b f D w ∈ W) :
    IsInvariantSubmodule rho W := by
  let P := generalLinearSubspaceStabilizer b W
  let K := f.closedSubgroupPreimage P
  have hKcarrier (g : Variety.Point G) :
      g ∈ K ↔ Submodule.map (rho.action g : Module.End k V) W = W := by
    change f.onPoints g ∈ P ↔ _
    rw [mem_generalLinearSubspaceStabilizer_iff]
    rw [hf]
  have hfull : LinearMap.range
      (identityTangentMorphismLinearMap K.inclusion) = ⊤ := by
    rw [identityTangent_closedSubgroupPreimage_range_eq_comap_charZero]
    apply top_unique
    intro D _
    change identityTangentMorphismLinearMap f D ∈
      LinearMap.range (identityTangentMorphismLinearMap P.inclusion)
    rw [identityTangent_generalLinearSubspaceStabilizer_range_iff]
    intro w hw
    have hdiff := LinearMap.congr_fun
      (rationalRepresentationDifferential_eq_generalLinear_comp rho b f) D
    exact hdiff ▸ hstable D w hw
  have hKtop : K = ClosedSubgroup.top :=
    closedSubgroup_eq_top_of_full_identityTangent K hG hfull
  intro g w hw
  have hgK : g ∈ K := by rw [hKtop]; trivial
  have hmap := (hKcarrier g).mp hgK
  have hwmap : (rho.action g : Module.End k V) w ∈
      Submodule.map (rho.action g : Module.End k V) W := ⟨w, hw, rfl⟩
  rwa [hmap] at hwmap

end Theory.AlgebraicGroup.Bor1
