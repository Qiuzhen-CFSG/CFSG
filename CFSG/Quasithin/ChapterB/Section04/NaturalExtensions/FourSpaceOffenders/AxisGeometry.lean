module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.CenterGeometry
public import Theory.LinearAlgebra.BinaryFourFixedSpace

/-!
# The common-axis four-groups in binary SL₃

The full pointwise stabilizer of a plane has order four and exponent two.
Its fixed space is that plane. Conversely, an elementary four-group fixing
a plane has the same order as its pointwise stabilizer and therefore equals it.
These facts identify the precise axis family used by the natural-submodule
branch of B.4.8(3), printed p.91, Aschbacher–Smith (1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender BinaryLinearThree
open CFSG.Quasithin.ChapterB.QuasisimpleSource BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.FourSpaceOffenders
noncomputable def axisGroup (P : Submodule (ZMod 2) BinaryLinearThree.Vector) :
    Subgroup BinaryLinearThree.Group :=
  (BinaryFourFixedSpace.pointwiseFixer P).comap (slEquivLinear 3).toMonoidHom

theorem axisGroup_full (P : Submodule (ZMod 2) BinaryLinearThree.Vector)
    (hP : Module.finrank (ZMod 2) (BinaryLinearThree.Vector ⧸ P) = 1) :
    IsFullAxisGroup BinaryField.two 3 (axisGroup P) := ⟨P, hP, fun _ => Iff.rfl⟩

theorem axisGroup_card (P : Submodule (ZMod 2) BinaryLinearThree.Vector)
    (hP : Module.finrank (ZMod 2) (BinaryLinearThree.Vector ⧸ P) = 1) :
    Nat.card (axisGroup P) = 4 := by
  let e := slEquivLinear 3
  let Q := BinaryFourFixedSpace.pointwiseFixer P
  let f : axisGroup P →* Q := e.toMonoidHom.subgroupComap Q
  have hi : Function.Injective f := fun a b h => Subtype.ext
    (e.injective (congrArg Subtype.val h))
  have hs : Function.Surjective f :=
    e.toMonoidHom.subgroupComap_surjective_of_surjective Q e.surjective
  rw [Nat.card_congr (MulEquiv.ofBijective f ⟨hi, hs⟩).toEquiv]
  have hd := P.finrank_quotient_add_finrank
  have hp : Module.finrank (ZMod 2) P = 2 := by
    rw [hP, Module.finrank_fin_fun] at hd
    omega
  have hindex : Q.index = 42 := by
    change (BinaryFourFixedSpace.pointwiseFixer P).index = 42
    rw [BinaryFourFixedSpace.index_pointwiseFixer P, hp]
    norm_num [Fin.prod_univ_succ]
  have hsize : Nat.card (LinearGroup 3) = 168 :=
    (Nat.card_congr e.symm.toEquiv).trans Matrix.PSL3Two.card_SL
  have h := Q.card_mul_index
  rw [hindex, hsize] at h
  omega

theorem axisGroup_elementary_rank (P : Submodule (ZMod 2) BinaryLinearThree.Vector)
    (hP : Module.finrank (ZMod 2) (BinaryLinearThree.Vector ⧸ P) = 1) :
    IsElementaryTwo (axisGroup P) ∧ rank (axisGroup P) = 2 := by
  have hc := axisGroup_card P hP
  have hsq (g : axisGroup P) : g ^ 2 = 1 := by
    apply Subtype.ext
    apply (slEquivLinear 3).injective
    change (slEquivLinear 3) ((g : BinaryLinearThree.Group) ^ 2) = (slEquivLinear 3) 1
    rw [map_pow, map_one]
    exact congrArg Subtype.val (BinaryFourFixedSpace.pointwiseFixer_sq P hP.le
      ⟨slEquivLinear 3 g, g.property⟩)
  have he : IsElementaryAbelian 2 (axisGroup P) :=
    { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
        (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) a b).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  refine ⟨⟨?_, he⟩, ?_⟩
  · intro hb; simp [hb] at hc
  · rw [rank, hc]; decide

theorem axisGroup_fixed (P : Submodule (ZMod 2) BinaryLinearThree.Vector)
    (hP : Module.finrank (ZMod 2) (BinaryLinearThree.Vector ⧸ P) = 1) :
    fixedSpace W (axisGroup P) = P := by
  have hE := (axisGroup_elementary_rank P hP).1
  let _ : IsElementaryAbelian 2 (axisGroup P) := hE.2
  obtain ⟨a, ha, hne⟩ := (axisGroup P).bot_or_exists_ne_one.resolve_left hE.1
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have hd := P.finrank_quotient_add_finrank
  have hp : Module.finrank (ZMod 2) P = 2 := by
    rw [hP, Module.finrank_fin_fun] at hd
    omega
  have hfix : Module.finrank (ZMod 2) (fixedSpace W (zpowers a)) = 2 := by
    have hn := natural_involution_range_finrank a ho
    rw [← fixedCodim_zpowers_eq_displacement_rank] at hn
    have hf := fixedCodim_add_finrank W (zpowers a)
    rw [Module.finrank_fin_fun] at hf
    omega
  have hle : P ≤ fixedSpace W (axisGroup P) := fun v hv a => a.property v hv
  apply (Submodule.eq_of_le_of_finrank_eq hle _).symm
  have hlow := Submodule.finrank_mono hle
  have hhigh := Submodule.finrank_mono (fixedSpace_antitone W (zpowers_le.mpr ha))
  omega

theorem fullAxis_iff_fixed_plane (A : Subgroup BinaryLinearThree.Group) :
    IsFullAxisGroup BinaryField.two 3 A ↔ IsElementaryTwo A ∧ rank A = 2 ∧
      Module.finrank (ZMod 2) (fixedSpace W A) = 2 := by
  constructor
  · rintro ⟨P, hP, hmem⟩
    have he : A = axisGroup P := by ext a; exact hmem a
    rw [he]
    refine ⟨(axisGroup_elementary_rank P hP).1, (axisGroup_elementary_rank P hP).2, ?_⟩
    rw [axisGroup_fixed P hP]
    have h := P.finrank_quotient_add_finrank
    change Module.finrank (ZMod 2) (BinaryLinearThree.Vector ⧸ P) +
      Module.finrank (ZMod 2) P = Module.finrank (ZMod 2) BinaryLinearThree.Vector at h
    change Module.finrank (ZMod 2) (BinaryLinearThree.Vector ⧸ P) = 1 at hP
    rw [hP, Module.finrank_fin_fun] at h
    change Module.finrank (ZMod 2) P = 2
    omega
  · rintro ⟨hA, hr, hf⟩
    let P := fixedSpace W A
    have hP : Module.finrank (ZMod 2) (BinaryLinearThree.Vector ⧸ P) = 1 := by
      have h := fixedCodim_add_finrank W A
      rw [hf, Module.finrank_fin_fun] at h
      change fixedCodim W A = 1
      omega
    have hle : A ≤ axisGroup P := by intro a ha v hv; exact hv ⟨a, ha⟩
    have hc := hA.card_eq_two_pow_rank
    rw [hr] at hc
    have he : A = axisGroup P := eq_of_le_of_card_ge hle (by rw [axisGroup_card P hP, hc]; decide)
    exact he ▸ axisGroup_full P hP
end CFSG.Quasithin.ChapterB.NaturalExtensions.FourSpaceOffenders
