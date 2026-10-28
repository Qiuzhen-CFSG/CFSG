module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.PointImage.Models
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.BinaryPermutationSixCover.SeedPreimage

/-!
# Elementary displacement on a transposition-fixed whole cover

On the six-letter augmentation module, commuting involutions centralizing a
transposition fix their displacements on its fixed hyperplane. A small Sylow
certificate proves the coordinate calculation; conjugation transfers it to
any elementary two-image. Fixed vectors lift from the natural quotient to
the augmentation module, so the statement holds for both possible whole
moved covers, of orders sixteen and thirty-two.

Geometry.Intersection.Source transports this calculation through the original
replacement maps. Source: MS93 (3.3)(ii), (3.6), printed pp.866--871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Intersection

private def fixedTest (t a b : Six.Perm) : Prop :=
  ∀ v : Fin 6 → ZMod 2, (∑ i, v i) = 0 → representation (Fin 6) t v = v →
    representation (Fin 6) b (representation (Fin 6) a v-v) =
      representation (Fin 6) a v-v
private instance (t a b : Six.Perm) : Decidable (fixedTest t a b) := by
  unfold fixedTest; infer_instance
private instance (t : Six.Perm) : Decidable t.IsSwap := by
  unfold Equiv.Perm.IsSwap; infer_instance
private theorem fixed_table : ∀ i j k : Fin 16,
    (Six.sylowWords i).IsSwap →
    Six.sylowWords j ^ 2 = 1 → Six.sylowWords k ^ 2 = 1 →
    Six.sylowWords j * Six.sylowWords k = Six.sylowWords k * Six.sylowWords j →
    Six.sylowWords j * Six.sylowWords i = Six.sylowWords i * Six.sylowWords j →
    Six.sylowWords k * Six.sylowWords i = Six.sylowWords i * Six.sylowWords k →
    fixedTest (Six.sylowWords i) (Six.sylowWords j) (Six.sylowWords k) := by
  decide +kernel

/-- On the whole augmentation cover, an elementary edge image fixes its
movement on the fixed hyperplane of any transposition in that image. -/
theorem elementary_core_fixed_displacement
    (B : Subgroup Six.Perm) [IsElementaryAbelian 2 B]
    (t : Six.Perm) (ht : t.IsSwap) (htB : t ∈ B)
    (a : Six.Perm) (ha : a ∈ B) (b : Six.Perm) (hb : b ∈ B)
    (v : core (Fin 6)) (hv : coreRepresentation (Fin 6) t v = v) :
    coreRepresentation (Fin 6) b (coreRepresentation (Fin 6) a v-v) =
      coreRepresentation (Fin 6) a v-v := by
  have hp : IsPGroup 2 B := IsElementaryAbelian.isPGroup 2 B
  obtain ⟨P,hBP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Six.Perm P Six.sylow
  let c := (MulAut.conj g).toMonoidHom
  have hBs {x : Six.Perm} (hx : x ∈ B) : c x ∈ Six.sylowCarrier := by
    change (MulAut.conj g) x ∈ (Six.sylow : Subgroup Six.Perm)
    rw [←hg]
    exact mem_map_of_mem _ (hBP hx)
  obtain ⟨i,hi⟩ := (Six.mem_sylowCarrier_iff _).mp (hBs htB)
  obtain ⟨j,hj⟩ := (Six.mem_sylowCarrier_iff _).mp (hBs ha)
  obtain ⟨k,hk⟩ := (Six.mem_sylowCarrier_iff _).mp (hBs hb)
  have hs : (c t).IsSwap := by
    obtain ⟨x,y,hxy,rfl⟩ := ht
    change (g * Equiv.swap x y * g⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨g x,g y,g.injective.ne hxy,rfl⟩
  have hc {x y : Six.Perm} (hx : x ∈ B) (hy : y ∈ B) : c x*c y=c y*c x := by
    rw [←map_mul,←map_mul]
    exact congrArg c (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : B) ⟨y,hy⟩))
  have h2 {x : Six.Perm} (hx : x ∈ B) : c x ^ 2 = 1 := by
    rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx,map_one]
  have he (x : Six.Perm) (w : core (Fin 6)) :
      coreRepresentation (Fin 6) (c x) (coreRepresentation (Fin 6) g w) =
        coreRepresentation (Fin 6) g (coreRepresentation (Fin 6) x w) := by
    change coreRepresentation (Fin 6) (g*x*g⁻¹) (coreRepresentation (Fin 6) g w) = _
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  have hh := fixed_table i j k
  rw [hi,hj,hk] at hh
  have hf : coreRepresentation (Fin 6) (c t) (coreRepresentation (Fin 6) g v) =
      coreRepresentation (Fin 6) g v := by rw [he,hv]
  have hmove : coreRepresentation (Fin 6) (c b)
      (coreRepresentation (Fin 6) (c a) (coreRepresentation (Fin 6) g v) -
        coreRepresentation (Fin 6) g v) =
      coreRepresentation (Fin 6) (c a) (coreRepresentation (Fin 6) g v) -
        coreRepresentation (Fin 6) g v :=
    Subtype.ext (hh hs (h2 ha) (h2 hb) (hc ha hb) (hc ha htB) (hc hb htB)
      (coreRepresentation (Fin 6) g v).val (coreRepresentation (Fin 6) g v).property
      (congrArg Subtype.val hf))
  rw [he,←map_sub,he] at hmove
  have hh' := congrArg (coreRepresentation (Fin 6) g⁻¹) hmove
  simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,inv_mul_cancel_left,map_one,Module.End.one_apply]
    using hh'

/-- The same calculation holds on either genuine whole-cover model. -/
theorem elementary_cover_fixed_displacement
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Six.Perm V)
    (hm : SixCover.IsNaturalOrCore ρ (MonoidHom.id _))
    (B : Subgroup Six.Perm) [IsElementaryAbelian 2 B]
    (t : Six.Perm) (ht : t.IsSwap) (htB : t ∈ B)
    (a : Six.Perm) (ha : a ∈ B) (b : Six.Perm) (hb : b ∈ B)
    (v : V) (hv : ρ t v = v) : ρ b (ρ a v-v) = ρ a v-v := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩ <;> simp only [MonoidHom.id_apply] at hE
  · obtain ⟨w,hw⟩ := coreToNatural_surjective (E v)
    have hwt : coreRepresentation (Fin 6) t w = w := by
      apply SixCover.six_core_fixed_of_natural_fixed
      rw [hw,←hE,hv]
    have hh := congrArg (coreToNatural (Fin 6))
      (elementary_core_fixed_displacement B t ht htB a ha b hb w hwt)
    simp only [coreToNatural_equivariant,map_sub,hw] at hh
    apply E.injective
    simpa only [hE,map_sub] using hh
  · apply E.injective
    simp only [hE,map_sub]
    exact elementary_core_fixed_displacement B t ht htB a ha b hb (E v)
      ((hE t v).symm.trans (congrArg E hv))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Intersection
