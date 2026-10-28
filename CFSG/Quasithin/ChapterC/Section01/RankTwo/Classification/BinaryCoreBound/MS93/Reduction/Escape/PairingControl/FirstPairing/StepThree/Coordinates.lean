module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Source
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Restricting the opposite moving coordinates to Vcirc

Local generation G = Ltilde Q identifies the moving preimage of V/Z with
Z[V,Q] Vcirc. Its coordinates vanish on Z[V,Q], so restriction to Vcirc
is still surjective. The restriction has kernel Vcirc intersect Z[V,Q]
and retains the original inverse-transpose action and the marking on U.

Consequently a bound of that intersection by U constructs the actual
OppositeSectionAt. The reverse inclusion follows from U = [Z,Ltilde].
The intersection bound is a remaining mathematical premise, not a consequence
asserted here of opposite orientation or of the order of its quotient.

In the quotient by the radical, Q centralizes the image of V. The
centralizing-supplement theorem therefore replaces the full stabilizer by
Ltilde in the commutator, proving the generation identity used above.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(3), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree

private theorem movingPreimage_eq_of_generation {A : Type*} [Group A]
    {π : A →* SL} {Q L V Z : Subgroup A}
    (s : SingleNaturalSection π Q L V Z) (hgen : L ⊔ Q = ⊤) :
    movingPreimage Q V Z = radicalPreimage Q V Z ⊔ ⁅V, L⁆ := by
  let := s.normal_group
  let := s.radical_normal
  let D := radicalPreimage Q V Z
  let q := QuotientGroup.mk' D
  have hqtop : (⊤ : Subgroup A).map q = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective D)
  have hcomm : ⁅V.map q, Q.map q⁆ = ⊥ := by
    rw [← map_commutator, Subgroup.map_eq_bot_iff]
    rw [show q.ker = D from QuotientGroup.ker_mk' D]
    change ⁅V, Q⁆ ≤ Z ⊔ ⁅V, Q⁆
    exact le_sup_right
  have hgenq : Q.map q ⊔ L.map q = ⊤ := by
    rw [← Subgroup.map_sup, sup_comm, hgen, hqtop]
  have he := commutator_eq_of_centralizing_sup hgenq
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
    (show L.map q ≤ normalizer (V.map q : Set (A ⧸ D)) from le_normalizer_of_normal)
  have heq : ⁅V, L⁆.map q = ⁅V, (⊤ : Subgroup A)⁆.map q := by
    rw [map_commutator, map_commutator, hqtop]
    exact he
  have hh := congrArg (Subgroup.comap q) heq
  rw [comap_map_eq, comap_map_eq] at hh
  change D ⊔ ⁅V, (⊤ : Subgroup A)⁆ = D ⊔ ⁅V, L⁆
  simpa only [q, QuotientGroup.ker_mk', sup_comm] using hh.symm

private def restrictDual {A : Type*} [Group A]
    {π : A →* SL} {L V Z C U : Subgroup A} [Z.Normal]
    {n : RankOnePairing.NaturalFactor π L U ⊥}
    (d : RankOnePairing.DualFactor π L V Z U n)
    (hcover : V = Z ⊔ C) (hnorm : L ≤ normalizer (C : Set A))
    (hkernel : C ⊓ Z = U) : RankOnePairing.DualFactor π L C U U n := by
  have hCV : C ≤ V := hcover ▸ le_sup_right
  have hZV : Z ≤ V := hcover ▸ le_sup_left
  let f := d.coordinates.comp (inclusion hCV)
  refine {
    coordinates := f
    surjective := ?_
    kernel := ?_
    normalized := hnorm
    action := ?_ }
  · intro v
    obtain ⟨x, hx⟩ := d.surjective v
    obtain ⟨z, hz, c, hc, hzc⟩ := mem_sup_of_normal_left.mp
      (show (x : A) ∈ Z ⊔ C from hcover ▸ x.property)
    let z' : V := ⟨z, hZV hz⟩
    let c' : C := ⟨c, hc⟩
    have hz' : d.coordinates z' = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [d.kernel]
      exact hz
    have hprod : z' * inclusion hCV c' = x := Subtype.ext hzc
    refine ⟨c', ?_⟩
    change d.coordinates (inclusion hCV c') = v
    rw [← hx, ← hprod, map_mul, hz', one_mul]
  · ext x
    change d.coordinates (inclusion hCV x) = 1 ↔ (x : A) ∈ U
    rw [← MonoidHom.mem_ker, d.kernel]
    change (x : A) ∈ Z ↔ (x : A) ∈ U
    rw [← hkernel]
    exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
  · intro l hl x y heq
    exact d.action l hl (inclusion hCV x) (inclusion hCV y) heq

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {geometry : Geometry R}

theorem movingPreimage_eq_radical_sup_Vcirc (source : LocalSource L R)
    (hb : 2 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (o : MovingOrientationAt a) :
    movingPreimage ((Q R a).subgroupOf (stabilizer R a))
      ((V R a).subgroupOf (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)) =
    radicalPreimage ((Q R a).subgroupOf (stabilizer R a))
      ((V R a).subgroupOf (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)) ⊔
      (Vcirc R a).subgroupOf (stabilizer R a) := by
  let S := stabilizer R a
  have hV : V R a ≤ S := (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hC : Vcirc R a ≤ S :=
    (le_normalizer_iff_commutator_le_left.mp
      ((show Ltilde R a ≤ S from map_subtype_le _).trans (V_normalized a))).trans hV
  have hgen : pResidual 2 S ⊔ (Q R a).subgroupOf S = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      ← MonoidHom.range_eq_map, range_subtype]
    exact source.local_generation a ha
  rw [movingPreimage_eq_of_generation o.natural_section hgen]
  congr 1
  apply map_injective S.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hV, map_subgroupOf_eq_of_le hC]
  rfl

noncomputable def opposite_of_radical_intersection (source : LocalSource L R)
    (hb : 2 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (o : MovingOrientationAt a)
    (hkernel : (Vcirc R a).subgroupOf (stabilizer R a) ⊓
      radicalPreimage ((Q R a).subgroupOf (stabilizer R a))
        ((V R a).subgroupOf (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)) ≤
      (U R a).subgroupOf (stabilizer R a)) : OppositeSectionAt a := by
  let := o.natural_section.radical_normal
  let : ((Vcirc R a).subgroupOf (stabilizer R a)).Normal :=
    normal_subgroupOf_of_le_normalizer (Vcirc_normalized a)
  exact {
    projection := o.projection
    surjective := o.natural_section.projection_surjective
    kernel := o.natural_section.projection_kernel
    naturalU := o.naturalU
    dual := restrictDual o.dual (movingPreimage_eq_radical_sup_Vcirc source hb a ha o)
      le_normalizer_of_normal (le_antisymm hkernel (by
        intro u hu
        exact ⟨commutator_mono (Z_le_VBall R a 2) le_rfl hu,
          mem_sup_left (show u ∈ (Z R a).subgroupOf (stabilizer R a) from U_le_Z a hu)⟩)) }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
