module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.Construction
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedSylowCenter

/-!
# The G₂(2)′ omega-center exclusion

For the actual commutator subgroup of the split-octonion G₂(2) carrier,
every Sylow two-subgroup has omega-center of order two. The coordinate
calculation first identifies the omega-center of `derivedSylowAmbient` with
the distinguished long-root subgroup. An actual Sylow witness has this
ambient image, so Sylow conjugacy gives the assertion for any Sylow subgroup.

Consequently an overlap with omega-center of order four cannot be isomorphic
to a Sylow subgroup of this concrete model. This discharges the model check
for F.1.12(8) in 15.4.15; the universal amalgam classification and the other
cases belong to the single-overgroup assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.1.12(8), printed p.263, and 15.4.15, printed p.1161.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair

/-- The actual derived overlap has precisely the distinguished omega-center. -/
theorem g2_derived_omega_center :
    Stellmacher.omegaOneCenterAmbient derivedSylowAmbient = distinguished := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgS, hsq, hcent⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hg
    exact derivedSylowAmbient_central_involution_mem hgS hsq hcent
  · apply Subgroup.zpowers_le.mpr
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨⟨core_le_unipotent (elementary_le_core z_mem_elementary),
      rootA_one_mem_commutator⟩, ?_, ?_⟩
    · rw [z, ← embedding_involution, ← map_pow, involution_sq, map_one]
    · intro g hg
      exact firstParabolic_centralizes_z g (unipotent_le_firstParabolic hg.1)

/-- The root-defined overlap in G₂(2)′ has omega-center of order two. -/
theorem g2_derived_omega_center_card :
    Nat.card (Stellmacher.omegaOneCenterAmbient derivedSylowAmbient) = 2 := by
  rw [g2_derived_omega_center, card_distinguished]

/-- Every Sylow two-subgroup of the actual derived group has omega-center
of order two. -/
theorem g2_derived_sylow_omega_center_card (P : Sylow 2 DerivedModel) :
    Nat.card (Stellmacher.omegaOneCenterAmbient (P : Subgroup DerivedModel)) = 2 := by
  let e : (derivedSylow : Subgroup DerivedModel) ≃* derivedSylowAmbient :=
    ((derivedSylow : Subgroup DerivedModel).equivMapOfInjective
      DerivedModel.subtype DerivedModel.subtype_injective).trans
        (MulEquiv.subgroupCongr derivedSylow_map_subtype)
  exact (omega_center_card_eq_of_equiv (P : Subgroup DerivedModel)
    derivedSylowAmbient ((P.equiv derivedSylow).trans e)).trans
      g2_derived_omega_center_card

/-- F.1.12(8)'s actual Sylow overlap cannot have the source omega-center
order four. -/
theorem not_g2_derived_sylow {G : Type*} [Group G] (T : Subgroup G)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient T) = 4)
    (P : Sylow 2 DerivedModel) : ¬ Nonempty (T ≃* P) := by
  rintro ⟨e⟩
  have he := omega_center_card_eq_of_equiv T (P : Subgroup DerivedModel) e
  have hb := g2_derived_sylow_omega_center_card P
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
