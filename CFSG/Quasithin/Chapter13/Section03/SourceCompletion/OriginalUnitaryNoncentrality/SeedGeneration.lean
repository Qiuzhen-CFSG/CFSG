module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.CoreMovement
public import Theory.Representation.G2BinaryPointSeedGeneration

/-!
# Generation of the original unitary seed

The literal point centralizer surjects onto the derived second parabolic.
Residual functoriality lifts its native seed-spanning displacements to
commutators with the original subgroup. Thus [V₃,L₁]=V₃, with no change to
the chosen marking or residual convention. The containing-component branch
of 13.3.14(g) uses this to place V₃ in the selected moved module.
Source: Aschbacher--Smith 13.3.14, printed pp.891--893.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.BinaryParabolicPair Atlas.G2.BinaryCore
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal point residual generates the original seed by commutators. -/
theorem unitary_point_residual_generates_seed
    (L Z U : Subgroup G) (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hz : pointCoordinateSubspace E Z = pointLine) (hs : pointCoordinateSubspace E U = seed)
    (hZV : Z ≤ V) (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (hres : pResidual 2 L = ⊤)
    (hd : commutator (Atlas.G2.Model F) ≤ (inducedAutomizer V L).map rho) :
    let R := (pResidual 2 (L ⊓ centralizer (Z : Set G) : Subgroup G)).map
      (L ⊓ centralizer (Z : Set G)).subtype
    ⁅U,R⁆ = U := by
  let K := L ⊓ centralizer (Z : Set G)
  let R := (pResidual 2 K).map K.subtype
  have hRU : R ≤ normalizer (U : Set G) :=
    point_centralizer_normalizes_marked_seed U Z R rho E he hs hz hUV
      ((map_subtype_le _).trans (inf_le_left.trans hLN)) ((map_subtype_le _).trans inf_le_right)
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hRU)
  obtain ⟨f,hf,_,hfe⟩ := unitary_point_centralizer_map L Z rho E he hz hZV hLN hfaith hres hd
  have hseed : seed ≤ pointCoordinateSubspace E ⁅U,R⁆ := by
    apply seed_le_of_residual_displacements
    intro a ha v hv
    rw [←map_pResidual_of_surjective 2 f hf] at ha
    obtain ⟨k,hk,rfl⟩ := ha
    obtain ⟨v,rfl⟩ := E.surjective v
    have hvU : v.toMul.val ∈ U := (mem_pointCoordinateSubspace E U v).mp (hs.symm ▸ hv)
    rw [hfe,←he,←map_sub]
    apply (mem_pointCoordinateSubspace E ⁅U,R⁆ _).mpr
    simp only [toMul_sub,div_eq_mul_inv]
    change k.val*v.toMul.val*k.val⁻¹*v.toMul.val⁻¹ ∈ ⁅U,R⁆
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_map_of_mem K.subtype hk) hvU
  intro u hu
  let v : Additive V := Additive.ofMul ⟨u,hUV hu⟩
  exact (mem_pointCoordinateSubspace E ⁅U,R⁆ v).mp
    (hseed (hs ▸ (mem_pointCoordinateSubspace E U v).mpr hu))
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
