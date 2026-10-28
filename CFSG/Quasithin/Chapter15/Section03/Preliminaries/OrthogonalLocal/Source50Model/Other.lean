module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source50Model.Fixed

/-!
The other elementary four-group in the orthogonal Sylow actor.

An elementary abelian normal subgroup escaping the definite-plane stabilizer
is the other Klein four-group in D₈. We identify it in the actual wreath action,
retaining its order and its fixed line. This supplies the image-group and
centralizer assertions used in original 15.3.51–53 and the local-core consumer.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.OrthogonalGeometry.Source50Model
open Subgroup
open scoped IsMulCommutative Pointwise
set_option synthInstance.maxSize 4096
set_option maxRecDepth 10000
attribute [local instance] FourGroupMatrixCoordinates.naturalAction orthogonalAction
/-- The second elementary four-group in the standard dihedral Sylow actor. -/
@[expose] def otherDihedral : Subgroup (DihedralGroup 4) where
  carrier x := x = 1 ∨ x = DihedralGroup.r 2 ∨
    x = DihedralGroup.sr 0 ∨ x = DihedralGroup.sr 2
  one_mem' := Or.inl rfl
  mul_mem' := by
    change ∀ a b : DihedralGroup 4,
      (a = 1 ∨ a = DihedralGroup.r 2 ∨ a = DihedralGroup.sr 0 ∨ a = DihedralGroup.sr 2) →
      (b = 1 ∨ b = DihedralGroup.r 2 ∨ b = DihedralGroup.sr 0 ∨ b = DihedralGroup.sr 2) →
      (a*b = 1 ∨ a*b = DihedralGroup.r 2 ∨ a*b = DihedralGroup.sr 0 ∨ a*b = DihedralGroup.sr 2)
    decide +kernel
  inv_mem' := by
    change ∀ a : DihedralGroup 4,
      (a = 1 ∨ a = DihedralGroup.r 2 ∨ a = DihedralGroup.sr 0 ∨ a = DihedralGroup.sr 2) →
      (a⁻¹ = 1 ∨ a⁻¹ = DihedralGroup.r 2 ∨ a⁻¹ = DihedralGroup.sr 0 ∨ a⁻¹ = DihedralGroup.sr 2)
    decide +kernel

instance (a : DihedralGroup 4) : Decidable (a ∈ otherDihedral) :=
  inferInstanceAs (Decidable (a = 1 ∨ a = DihedralGroup.r 2 ∨
    a = DihedralGroup.sr 0 ∨ a = DihedralGroup.sr 2))

abbrev otherActor : Subgroup OrthogonalActor := otherDihedral.map wreathTwoDihedralHom

private theorem standard_other_eq (R : Subgroup OrthogonalActor)
    (hle : R ≤ wreathTwoDihedralHom.range)
    (hn : wreathTwoDihedralHom.range ≤ normalizer (R : Set OrthogonalActor))
    (hout : ¬ R ≤ planePart wreathTwoDihedralHom.range)
    (hpow : ∀ x ∈ R, x ^ 2 = 1)
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, x*y = y*x) : R = otherActor := by
  have hne : R ≠ ⊥ := fun he => hout (he ▸ bot_le)
  have hz := standard_center_mem R hle hn hne
  obtain ⟨x, hx, hxo⟩ := Set.not_subset.mp hout
  obtain ⟨a, rfl⟩ := hle hx
  have ha2 : a ^ 2 = 1 := wreathTwoDihedralHom_injective (by
    simpa only [map_pow, map_one] using hpow _ hx)
  have har : (wreathTwoDihedralHom a).right ≠ 1 :=
    fun hr => hxo ⟨⟨a, rfl⟩, hr⟩
  have cert : ∀ a : DihedralGroup 4, a ^ 2 = 1 →
      (wreathTwoDihedralHom a).right ≠ 1 →
      (∀ b : DihedralGroup 4, a*b = b*a ↔ b ∈ otherDihedral) ∧
      (∀ b ∈ otherDihedral, b = 1 ∨ b = DihedralGroup.r 2 ∨
        b = a ∨ b = DihedralGroup.r 2 * a) := by decide +kernel
  obtain ⟨hc, hg⟩ := cert a ha2 har
  apply le_antisymm
  · intro y hy
    obtain ⟨b, rfl⟩ := hle hy
    refine ⟨b, (hc b).mp ?_, rfl⟩
    apply wreathTwoDihedralHom_injective
    simpa only [map_mul] using hcomm _ hx _ hy
  · rintro _ ⟨b, hb, rfl⟩
    rcases hg b hb with rfl | rfl | rfl | rfl
    · exact R.one_mem
    · exact hz
    · exact hx
    · simpa only [map_mul] using R.mul_mem hz hx

/-- Every normal elementary actor escaping the definite-plane stabilizer is
conjugate, in the literal action, to the second standard Klein four-group. -/
theorem exists_other_conjugate (P : Sylow 2 OrthogonalActor)
    (R : Subgroup OrthogonalActor) [IsElementaryAbelian 2 R]
    (hle : R ≤ P)
    (hn : (P : Subgroup OrthogonalActor) ≤ normalizer (R : Set OrthogonalActor))
    (hout : ¬ R ≤ planePart P) :
    ∃ g : OrthogonalActor,
      (P : Subgroup OrthogonalActor).map (MulAut.conj g).toMonoidHom =
        wreathTwoDihedralHom.range ∧
      R.map (MulAut.conj g).toMonoidHom = otherActor := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq OrthogonalActor P wreathTwoSylow
  let e := (MulAut.conj g).toMonoidHom
  have hP : (P : Subgroup OrthogonalActor).map e = wreathTwoDihedralHom.range := by
    have he := congrArg (fun Q : Sylow 2 OrthogonalActor => (Q : Subgroup OrthogonalActor)) hg
    rw [Sylow.coe_subgroup_smul, wreathTwoSylow_coe] at he
    exact he
  refine ⟨g, hP, standard_other_eq (R.map e) (hP ▸ map_mono hle)
    (hP ▸ (map_mono hn).trans (le_normalizer_map _)) ?_ ?_ ?_⟩
  · intro he
    apply hout
    rw [← hP, planePart_conj] at he
    exact (map_le_map_iff_of_injective (MulAut.conj g).injective).mp he
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hh : x*y = y*x := congrArg Subtype.val (mul_comm (⟨x,hx⟩ : R) ⟨y,hy⟩)
    change e x * e y = e y * e x
    rw [← map_mul, ← map_mul, hh]

/-- The actual image has order four; this makes no assertion about U/Z. -/
theorem other_card_four (P : Sylow 2 OrthogonalActor)
    (R : Subgroup OrthogonalActor) [IsElementaryAbelian 2 R]
    (hle : R ≤ P)
    (hn : (P : Subgroup OrthogonalActor) ≤ normalizer (R : Set OrthogonalActor))
    (hout : ¬ R ≤ planePart P) : Nat.card R = 4 := by
  obtain ⟨g, _, he⟩ := exists_other_conjugate P R hle hn hout
  have hc : Nat.card otherDihedral = 4 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [← card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
    he, card_map_of_injective wreathTwoDihedralHom_injective, hc]


private theorem standard_other_fixed :
    fixedVectors otherActor = fixedVectors wreathTwoDihedralHom.range := by
  have hc : ∀ v : OrthogonalVector,
      (∀ a : DihedralGroup 4, a ∈ otherDihedral → wreathTwoDihedralHom a • v = v) ↔
        (∀ a : DihedralGroup 4, wreathTwoDihedralHom a • v = v) := by decide +kernel
  ext v
  constructor
  · intro hv x hx
    obtain ⟨a,rfl⟩ := hx
    exact (hc v).mp (fun b hb => hv _ ⟨b,hb,rfl⟩) a
  · intro hv x hx
    obtain ⟨a,_,rfl⟩ := hx
    exact hv _ ⟨a,rfl⟩

/-- The other elementary Sylow image has exactly the Sylow fixed line. This
is the centralizer equality used by the final local-core source consumer. -/
theorem fixedVectors_other_eq (P : Sylow 2 OrthogonalActor)
    (R : Subgroup OrthogonalActor) [IsElementaryAbelian 2 R]
    (hle : R ≤ P)
    (hn : (P : Subgroup OrthogonalActor) ≤ normalizer (R : Set OrthogonalActor))
    (hout : ¬ R ≤ planePart P) : fixedVectors R = fixedVectors P := by
  obtain ⟨g,hP,he⟩ := exists_other_conjugate P R hle hn hout
  ext v
  rw [← fixed_conj R g v, he, standard_other_fixed, ← hP, fixed_conj]

end CFSG.Quasithin.Chapter15.Section03.OrthogonalGeometry.Source50Model
