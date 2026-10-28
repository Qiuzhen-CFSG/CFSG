module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.CoreSections

/-!
# The Fano-line law for the original point-core sections

For two distinct nonzero points t,u of Z, the extraspecial core Q_t has
an element conjugating u to tu. That element fixes its entire section in
R/Z and carries the u-section to the tu-section. Their pair intersection
therefore lies in all three sections on the Fano line, and the pair
intersection is independent of which two of these points are chosen.
Pulling back through the same quotient also gives Q_t ∩ Q_u ≤ Q_{tu}.

These identities connect the original additive law on Z with the geometry
of the radical module, as needed for its dual-natural tensor factor.
Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), the tensor argument in (4.4), pp.597–598,
DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

/-- The original pair section annihilates the third point on the same Fano line. -/
theorem coreSection_inf_le_product (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    d.coreSection t ⊓ d.coreSection u ≤ d.coreSection (t*u) := by
  obtain ⟨q,hq,he⟩ := exists_core_flip (d.point_type h ht ht1)
    (d.contained_in_cores t ht ht1 hu) hu1 htu.symm
  let n : normalizer (d.space : Set G) := inclusion (d.cores_normalize t ht ht1) ⟨q,hq⟩
  intro v hv
  have hf : d.radicalAction n v = v := d.pointCore_fixes_coreSection h ht ht1 ⟨q,hq⟩ hv.1
  have hm : d.radicalAction n v ∈ (d.coreSection u).map (d.radicalAction n).toMonoidHom :=
    mem_map_of_mem _ hv.2
  rw [d.coreSection_conjugate] at hm
  change d.radicalAction n v ∈ d.coreSection (q*u*q⁻¹) at hm
  rwa [he,hf] at hm

/-- The pair section depends on the original Fano line, not its chosen two points. -/
theorem coreSection_inf_product (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    d.coreSection t ⊓ d.coreSection (t*u) = d.coreSection t ⊓ d.coreSection u := by
  have htuZ : t*u ∈ d.space := d.space.mul_mem ht hu
  have ht2 : t^2=1 := (d.point_type h ht ht1).involution ▸ pow_orderOf_eq_one t
  have htu1 : t*u ≠ 1 := by
    intro he
    have hi : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
    have hh := congrArg (t⁻¹ * ·) he
    rw [inv_mul_cancel_left,mul_one] at hh
    exact htu (hh.trans hi).symm
  have ht_tu : t ≠ t*u := by
    intro he
    exact hu1 ((mul_left_cancel (he.symm.trans (mul_one t).symm)))
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    have he : t*(t*u)=u := by rw [←mul_assoc,←pow_two,ht2,one_mul]
    have hh := d.coreSection_inf_le_product h ht htuZ ht1 htu1 ht_tu
    rwa [he] at hh
  · exact le_inf inf_le_left (d.coreSection_inf_le_product h ht hu ht1 hu1 htu)

/-- A vector in two point sections lies in all three point sections on their line. -/
theorem coreSection_line_inf (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    d.coreSection t ⊓ d.coreSection u ⊓ d.coreSection (t*u) =
      d.coreSection t ⊓ d.coreSection u :=
  inf_eq_left.mpr (d.coreSection_inf_le_product h ht hu ht1 hu1 htu)

/-- The source pair-core intersection lies in the third core on its Fano line. -/
theorem point_pair_le_product_core (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    ambientCore t ⊓ ambientCore u ≤ ambientCore (t*u) := by
  have ht2 : t^2=1 := (d.point_type h ht ht1).involution ▸ pow_orderOf_eq_one t
  have htu1 : t*u ≠ 1 := by
    intro he
    have hi : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
    have hh := congrArg (t⁻¹ * ·) he
    rw [inv_mul_cancel_left,mul_one] at hh
    exact htu (hh.trans hi).symm
  intro r hr
  let rR : d.R := ⟨r,d.point_pair_le_R h ht hu ht1 hu1 htu hr⟩
  have hq : QuotientGroup.mk' (center d.R) rR ∈ d.coreSection (t*u) :=
    d.coreSection_inf_le_product h ht hu ht1 hu1 htu
      ⟨mem_map_of_mem _ hr.1,mem_map_of_mem _ hr.2⟩
  have hh : rR ∈ (d.coreSection (t*u)).comap (QuotientGroup.mk' (center d.R)) := hq
  rw [d.coreSection_comap h (d.space.mul_mem ht hu) htu1] at hh
  exact hh

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
end
