module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedEdges
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCommonFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallSeeds

/-!
# Retaining the compatible cube marking

The paired-edge selector rotates the original three-pair cube to place its
critical transposition. Retaining that actual marking identifies its chosen
second cube as the twist needed by the elementary-cube generation certificate.
An equality of original cubes does not identify their twisted cubes, so the
rotation witness remains explicit.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)(a), printed p.917.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubePairedEdges
local notation "S" => Equiv.Perm (Fin 6)
open CubeCommonFixer

/- The fixed compatible conjugator used by the elementary-cube generation
   certificate.  Keeping this six-letter constant at the selector layer avoids
   a dependency cycle with the terminal generation module. -/
def cubeGenerationConjugator : S := Equiv.swap 1 2 * Equiv.swap 3 4

private theorem marked_edge_pair_aux (u a : S)
    (haD : a ∈ (D 6).map (MulAut.conj u).toMonoidHom) (ha : a.IsSwap) :
    ∃ c v x : S, v = c * cubeGenerationConjugator ∧
      (D 6).map (MulAut.conj c).toMonoidHom =
        (D 6).map (MulAut.conj u).toMonoidHom ∧
      x ∈ alternatingGroup (Fin 6) ∧ orderOf x = 3 ∧
      x ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) ∧
      ((D 6).map (MulAut.conj u).toMonoidHom) ⊔
        ((D 6).map (MulAut.conj v).toMonoidHom) = ⊤ ∧
      ((D 6).map (MulAut.conj v).toMonoidHom) ⊔ zpowers a ⊔
        zpowers ((MulAut.conj x) a) = ⊤ ∧
      ((D 6).map (MulAut.conj v).toMonoidHom) ⊔
        ((D 6).map (MulAut.conj v).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  obtain ⟨a₀,ha₀,rfl⟩ := haD
  have hs : a₀.IsSwap := by
    apply Equiv.Perm.isSwap_iff_cycleType.mpr
    have hi : (MulAut.conj u a₀).cycleType = a₀.cycleType :=
      Equiv.Perm.cycleType_conj
    simpa only [MulEquiv.coe_toMonoidHom,hi] using Equiv.Perm.isSwap_iff_cycleType.mp ha
  obtain ⟨i,rfl⟩ := CubeSmallKernel.swaps_in_cube a₀ ha₀ hs
  let c := u*r^i.val
  let x := (MulAut.conj c) r
  have hct : (MulAut.conj c).toMonoidHom t = (MulAut.conj u) (pairSwap 6 i) := by
    have hi : ∀ i : Fin 3, (MulAut.conj (r^i.val)) t = pairSwap 6 i := by decide +kernel
    change (u*r^i.val)*t*(u*r^i.val)⁻¹=u*(pairSwap 6 i)*u⁻¹
    rw [←hi i]
    simp only [MulAut.conj_apply,mul_inv_rev,mul_assoc]
  have hrN : r ∈ normalizer (D 6 : Set S) := CubeSmallSeeds.rotation_normalizes
  have hD : (D 6).map (MulAut.conj c).toMonoidHom =
      (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [show c=u*r^i.val from rfl,←conjugate_twice]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp ((normalizer (D 6 : Set S)).pow_mem hrN i.val)
  have hx : x ∈ alternatingGroup (Fin 6) :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem r (by decide +kernel) c
  have hxo : orderOf x = 3 := ((MulAut.conj c).orderOf_eq r).trans
    (orderOf_eq_prime (by decide +kernel) (by decide +kernel))
  have hxN : x ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) := by
    rw [←hD]
    exact le_normalizer_map (MulAut.conj c).toMonoidHom (mem_map_of_mem _ hrN)
  have hD' : D'.map (MulAut.conj c).toMonoidHom = (D 6).map (MulAut.conj (c*k)).toMonoidHom :=
    conjugate_twice _ _ _
  have hrt : (MulAut.conj c).toMonoidHom ((MulAut.conj r) t) =
      (MulAut.conj x) ((MulAut.conj u) (pairSwap 6 i)) := by
    rw [←hct]
    change c*(r*t*r⁻¹)*c⁻¹=(c*r*c⁻¹)*(c*t*c⁻¹)*(c*r*c⁻¹)⁻¹
    group
  have hDx : (D'.map (MulAut.conj r).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      (D'.map (MulAut.conj c).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    rw [conjugate_twice D' r c,conjugate_twice D' c x]
    have he : c*r=x*c := by change c*r=(c*r*c⁻¹)*c; group
    rw [he]
  refine ⟨c,c*k,x,?_,?_,hx,hxo,hxN,?_,?_,?_⟩
  · rfl
  · exact hD
  · have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) original_kernels_generate
    simpa only [Subgroup.map_sup,hD,hD',map_top_of_surjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).surjective] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) pair_generates
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hct,hrt,hD',MulEquiv.coe_toMonoidHom,
      map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective] using hh
  · apply inverse_pair
    have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) kernels_generate
    simpa only [Subgroup.map_sup,hDx,hD',
      map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective] using hh

/-- The selector's chosen cube is the compatible elementary-cube twist of its
    actual marking.  This orientation is the bridge used by the literal
    quotient lift in the elementary-image terminal branch. -/
theorem marked_edge_pair_with_cube (u a : S)
    (haD : a ∈ (D 6).map (MulAut.conj u).toMonoidHom) (ha : a.IsSwap) :
    ∃ v x : S, x ∈ alternatingGroup (Fin 6) ∧ orderOf x = 3 ∧
      x ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) ∧
      ((D 6).map (MulAut.conj u).toMonoidHom) ⊔
        ((D 6).map (MulAut.conj v).toMonoidHom) = ⊤ ∧
      ((D 6).map (MulAut.conj v).toMonoidHom) ⊔ zpowers a ⊔
        zpowers ((MulAut.conj x) a) = ⊤ ∧
      ((D 6).map (MulAut.conj v).toMonoidHom) ⊔
        ((D 6).map (MulAut.conj v).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ ∧
      ∃ c : S, (D 6).map (MulAut.conj c).toMonoidHom =
        (D 6).map (MulAut.conj u).toMonoidHom ∧
        (D 6).map (MulAut.conj v).toMonoidHom =
          (D 6).map (MulAut.conj (c * cubeGenerationConjugator)).toMonoidHom := by
  obtain ⟨c,v,x,hv,hc,hx,hxo,hxN,hgen,hpair,hinv⟩ :=
    marked_edge_pair_aux u a haD ha
  exact ⟨v,x,hx,hxo,hxN,hgen,hpair,hinv,c,hc,by rw [hv]⟩

end CubePairedEdges
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
