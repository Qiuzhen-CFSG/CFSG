module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ParabolicLifts
public import Theory.Representation.G2BinaryPointImage
/-!
# The original unitary point radical in the natural action

L₁ remains the two-residual of the point centralizer in L. Its product
with the actual Sylow covers the derived point parabolic. The resulting
image is normal in the full point parabolic, since it contains that
parabolic's commutator subgroup. Relative two-core monotonicity therefore
puts the image of O₂(L₁T) in the genuine second five-root radical.

Source: Aschbacher–Smith C.1.37 and 13.3.10(2), pp.141–143,887–888.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem point_intermediate_normal (S : Subgroup (Atlas.G2.Model F))
    (hS : S ≤ Atlas.G2.BinaryCore.secondParabolic)
    (hd : Atlas.G2.BinaryParabolicPair.derivedSecondAmbient ≤ S) :
    Atlas.G2.BinaryCore.secondParabolic ≤ normalizer (S : Set _) := by
  let P := Atlas.G2.BinaryCore.secondParabolic
  have hc : commutator P ≤ S.subgroupOf P := by
    intro x hx
    apply hd
    refine ⟨x.property,?_⟩
    have hm := mem_map_of_mem P.subtype hx
    rw [P.map_subtype_commutator] at hm
    exact commutator_mono le_top le_top hm
  let : (S.subgroupOf P).Normal := Subgroup.Normal.of_commutator_le _ hc
  exact (normal_subgroupOf_iff_le_normalizer hS).mp inferInstance

/-- The two-core of the original L₁T has image in the genuine second
parabolic radical. The first, quaternion radical is not substituted. -/
theorem unitary_original_point_radical_image
    (T : Sylow 2 G) (L Z : Subgroup G)
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hz : pointCoordinateSubspace E Z = pointLine) (hZV : Z ≤ V)
    (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLN : L ≤ normalizer (V : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hd : commutator (Atlas.G2.Model F) ≤ (inducedAutomizer V L).map rho) :
    let P := (pResidual 2 (L ⊓ centralizer (Z : Set G) : Subgroup G)).map
      (L ⊓ centralizer (Z : Set G)).subtype ⊔ (T : Subgroup G)
    (inducedAutomizer V (P.pCoreIn 2)).map rho ≤ Atlas.G2.LieParabolicSetup.radical₂ := by
  intro P
  let N := normalizer (V : Set G)
  let f : N →* Atlas.G2.Model F := rho.comp V.normalizerMonoidHom.rangeRestrict
  let S := (P.subgroupOf N).map f
  let R := P.pCoreIn 2
  let A := (R.subgroupOf N).map f
  have hPN : P ≤ N := sup_le ((map_subtype_le _).trans (inf_le_left.trans hLN)) hTN
  have hPC : P ≤ centralizer (Z : Set G) :=
    sup_le ((map_subtype_le _).trans inf_le_right) hTC
  have hRS : A ≤ S := map_mono (subgroupOf_mono N (pCoreIn_le 2 P))
  have hdS : Atlas.G2.BinaryParabolicPair.derivedSecondAmbient ≤ S := by
    have hh := source_point_parabolic_covered T L Z rho E he hz hZV hTC hTL hd
    simpa only [inducedAutomizer,Subgroup.map_map] using hh
  have hSP : S ≤ Atlas.G2.BinaryCore.secondParabolic := by
    rintro _ ⟨n,hn,rfl⟩
    apply fixes_first_mem_parabolic
    obtain ⟨v,hv⟩ := E.surjective (Pi.single 0 1)
    have hvZ : (v.toMul : G) ∈ Z := (mem_pointCoordinateSubspace E Z v).mp (by
      rw [hz,hv,mem_pointLine]; intro i hi; simp [hi])
    change Atlas.G2.Restricted.NaturalCoordinates.action F
      (rho (V.normalizerMonoidHom.rangeRestrict n)) (Pi.single 0 1) = _
    rw [←hv,←he]
    apply congrArg E
    apply Additive.toMul.injective
    apply Subtype.ext
    change n.val * (v.toMul : G) * n.val⁻¹ = v.toMul
    exact mul_inv_eq_iff_eq_mul.mpr (hPC hn _ hvZ).symm
  have hSA : S ≤ normalizer (A : Set _) := by
    have hPR : P ≤ normalizer (R : Set G) :=
      P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
    have hn : P.subgroupOf N ≤ normalizer (R.subgroupOf N : Set N) := by
      intro n hn
      rw [←subgroupOf_normalizer_eq ((pCoreIn_le 2 P).trans hPN)]
      exact hPR hn
    exact (map_mono hn).trans (le_normalizer_map f)
  have hp : IsPGroup 2 A := (isPGroup_pCoreIn 2 P).comap_subtype.map f
  have hcore := le_pCoreIn_of_normalizes hp hRS hSA
  have hmono := pCoreIn_mono_of_normalizes (p := 2) hSP (point_intermediate_normal S hSP hdS)
  have hfinal : A ≤ Atlas.G2.LieParabolicSetup.radical₂ := by
    have hh := hcore.trans hmono
    rw [←Atlas.G2.LieParabolicSetup.local₂_binary,
      Atlas.G2.LieParabolicSetup.local₂_pCoreIn] at hh
    exact hh
  simpa only [inducedAutomizer,Subgroup.map_map] using hfinal
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
