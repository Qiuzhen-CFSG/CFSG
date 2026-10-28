module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedPairOrbit

/-!
# The marked paired conjugator lies in the alternating residual

The explicit pair rotation has order three. Retaining the same construction
through both conjugations therefore supplies an alternating conjugator of
order three for the marked paired source choice. Private imports continue
the internal finite construction without changing its previous public API.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
local notation "S" => Equiv.Perm (Fin 6)

/-- The same marked paired choice can be made inside A6, with exact order
three. Both joins and the full cube normalizer are retained. -/
theorem mixed_marked_residual_pair (u v a : S) (ha : a.IsSwap)
    (hmem : a ∈ plus.map (MulAut.conj v).toMonoidHom)
    (hgen : plus.map (MulAut.conj u).toMonoidHom ⊔
      plus.map (MulAut.conj v).toMonoidHom = ⊤) :
    ∃ k : S,
      plus.map (MulAut.conj u).toMonoidHom ⊔
        (plus.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k).toMonoidHom = ⊤ ∧
      plus.map (MulAut.conj u).toMonoidHom ⊔ zpowers a ⊔
        zpowers ((MulAut.conj k⁻¹) a) = ⊤ ∧
      k ∈ normalizer (((D 6).map (MulAut.conj v).toMonoidHom) : Set S) ∧
      k ∈ alternatingGroup (Fin 6) ∧ orderOf k = 3 := by
  have haeq : a = (MulAut.conj v) swap45 := by
    obtain ⟨b,hb,rfl⟩ := hmem
    obtain ⟨i,rfl⟩ := (mem_plus_iff b).mp hb
    have hc := Equiv.Perm.isSwap_iff_cycleType.mp ha
    change (v * planeWords 0 i * v⁻¹).cycleType = {2} at hc
    rw [Equiv.Perm.cycleType_conj] at hc
    have cert : ∀ i : Fin 4, (planeWords 0 i).cycleType = {2} → planeWords 0 i = swap45 := by decide +kernel
    rw [cert i hc]
    rfl
  have hmap : (plus.map (MulAut.conj (v⁻¹*u)).toMonoidHom).map (MulAut.conj v).toMonoidHom =
      plus.map (MulAut.conj u).toMonoidHom := by
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change v*((v⁻¹*u)*x*(v⁻¹*u)⁻¹)*v⁻¹=u*x*u⁻¹
    group
  have hbase : plus ⊔ plus.map (MulAut.conj (v⁻¹*u)).toMonoidHom = ⊤ := by
    apply map_injective (f := (MulAut.conj v).toMonoidHom) (MulAut.conj v).injective
    rw [Subgroup.map_sup,hmap,map_top_of_surjective _ (MulAut.conj v).surjective,sup_comm]
    exact hgen
  obtain ⟨r,hr,he⟩ := canonical_plane_orbit (v⁻¹*u) hbase
  have hb := choice_transport (plus.map (MulAut.conj cross).toMonoidHom) (D 6)
    swap45 rotate r canonical_choice
  have hD : (D 6).map (MulAut.conj r).toMonoidHom = D 6 :=
    mem_normalizer_iff_map_conj_eq.mp (normalWords_mem_normalizer r hr)
  have hs : (MulAut.conj r) swap45 = swap45 := by
    have hc := normalWords_centralize r hr 2
    change r*swap45=swap45*r at hc
    change r*swap45*r⁻¹=swap45
    rw [hc,mul_inv_cancel_right]
  dsimp only at hb
  rw [←he,hD,hs] at hb
  have hh := choice_transport (plus.map (MulAut.conj (v⁻¹*u)).toMonoidHom) (D 6)
    swap45 ((MulAut.conj r) rotate) v hb
  dsimp only at hh
  rw [hmap,←haeq] at hh
  refine ⟨(MulAut.conj v) ((MulAut.conj r) rotate),hh.1,hh.2.1,hh.2.2,?_,?_⟩
  · have hrot : rotate ∈ alternatingGroup (Fin 6) := by decide +kernel
    exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _
      ((inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ hrot r) v
  · have hrot : orderOf rotate = 3 :=
      orderOf_eq_prime (by decide +kernel : rotate^3=1) (by decide +kernel : rotate≠1)
    exact (orderOf_injective (MulAut.conj v).toMonoidHom (MulAut.conj v).injective _).trans
      ((orderOf_injective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective _).trans hrot)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
