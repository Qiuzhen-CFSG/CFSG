module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Coordinates
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Stellmacher.OmegaOneCenterMap

/-!
# Splitting the Sylow omega-center along an exceptional A₇ block

Subnormal residual commutators put [Z,L] inside U. Vanishing H¹ corrects
each z by u in U to centralize L. The correction is unique because
C_U(L)=1; Sylow conjugation therefore fixes u. This proves the literal
identity Z=(U∩Z)C_Z(L) and its centralizer consequence, without assuming
a fixed-space splitting certificate.

Source: Aschbacher–Smith C.1.23(2), printed p.130. This proves directly
the instance of B.5.1(2) used in that paragraph.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

open scoped commutatorElement

theorem fixed_correction (hL : IsBlock L) (hm : IsExceptionalA7Block L)
    (Q : Subgroup G) (hQ : Q ≤ pCore 2 G)
    (hc : Q ≤ centralizer (pCore 2 G : Set G)) (x : Q) :
    ∃ u : (blockU L).map L.subtype,
      (u : G)⁻¹ * x ∈ centralizer (L : Set G) := by
  let := hm.1.elementary
  let := u_H1_subsingleton hm
  let π := QuotientGroup.mk' (pCore 2 L)
  have hcomm : ⁅L, Q⁆ ≤ (blockU L).map L.subtype := by
    rw [commutator_comm]
    exact (commutator_mono hQ le_rfl).trans
      (commutator_le_core_commutator_of_isSubnormal L (pCore 2 G)
        hL.subnormal hL.short.twoPerfect pCore_isPGroup le_normalizer_of_normal)
  have hker : ∀ l ∈ π.ker, ∀ y ∈ Q, ⁅(l : G), y⁆ ∈ (⊥ : Subgroup G) := by
    intro l hl y hy
    have hl' : l ∈ pCore 2 L := by simpa only [π, QuotientGroup.ker_mk'] using hl
    have hc' := hc hy (l : G)
      (pCoreIn_le_of_subnormal 2 hL.subnormal (mem_map_of_mem L.subtype hl'))
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc'
  obtain ⟨u, hu⟩ := (blockSection L hm.1).exists_fixed_mod_kernel
    π (QuotientGroup.mk'_surjective _) Q hcomm hker x
  refine ⟨u, fun l hl => ?_⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp (hu ⟨l,hl⟩)

omit [Finite G] in
theorem fixed_layer_trivial (hm : IsExceptionalA7Block L)
    (x : G) (hx : x ∈ (blockU L).map L.subtype)
    (hc : x ∈ centralizer (L : Set G)) : x = 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hz : (⟨u, hu⟩ : blockU L) ∈ blockFixed L := by
    change u ∈ center L
    exact mem_center_iff.mpr fun l => Subtype.ext (hc l l.property)
  rw [hm.fixed_eq_bot] at hz
  exact congrArg (fun v : blockU L => ((v : L) : G)) hz

theorem central_correction (hL : IsBlock L) (hm : IsExceptionalA7Block L)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (z : G) (hz : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) :
    ∃ u ∈ ((blockU L).map L.subtype ⊓
      Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Subgroup G),
      u⁻¹ * z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
        centralizer (L : Set G) := by
  let U := (blockU L).map L.subtype
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hQT : pCore 2 G ≤ (T : Subgroup G) := pCore_isPGroup.le_sylow_of_normal T
  have hUT : U ≤ (T : Subgroup G) :=
    ((map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hL.subnormal)).trans hQT
  obtain ⟨hzT, hz2, hzC⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzQ : z ∈ pCore 2 G := hchar fun q hq => hzC q (hQT hq)
  have hzCQ : z ∈ centralizer (pCore 2 G : Set G) := fun q hq => hzC q (hQT hq)
  obtain ⟨u, hu⟩ := fixed_correction L hL hm
    (pCore 2 G ⊓ centralizer (pCore 2 G : Set G)) inf_le_left inf_le_right
    ⟨z, hzQ, hzCQ⟩
  let c : G := (u : G)⁻¹ * z
  have hc : c ∈ centralizer (L : Set G) := hu
  have huc : (u : G) * c = z := by simp [c]
  have huZ : (u : G) ∈ Z := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hUT u.property, ?_, ?_⟩
    · let : IsElementaryAbelian 2 U := hm.1.elementary.map L.subtype
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) u.property
    · intro t ht
      let u' : G := t * (u : G) * t⁻¹
      let c' : G := t * c * t⁻¹
      have hu' : u' ∈ U := (mem_normalizer_iff.mp
        ((hTL.trans (normalizer_le_normalizer_characteristic_image L (blockU L))) ht) _).mp u.property
      have hc' : c' ∈ centralizer (L : Set G) := (mem_normalizer_iff.mp
        ((hTL.trans (normalizer_le_normalizer_centralizer L)) ht) _).mp hc
      have hprod : u' * c' = (u : G) * c := by
        calc
          u' * c' = t * ((u : G) * c) * t⁻¹ := by dsimp [u', c']; group
          _ = t * z * t⁻¹ := by rw [huc]
          _ = z := by rw [hzC t ht, mul_inv_cancel_right]
          _ = (u : G) * c := huc.symm
      have hd : (u : G)⁻¹ * u' = c * c'⁻¹ := by
        calc
          (u : G)⁻¹ * u' = (u : G)⁻¹ * (u' * c') * c'⁻¹ := by group
          _ = (u : G)⁻¹ * ((u : G) * c) * c'⁻¹ := by rw [hprod]
          _ = c * c'⁻¹ := by group
      have hone := fixed_layer_trivial L hm ((u : G)⁻¹ * u')
        (U.mul_mem (U.inv_mem u.property) hu')
        (hd ▸ (centralizer (L : Set G)).mul_mem hc ((centralizer (L : Set G)).inv_mem hc'))
      have he : u' = (u : G) := (inv_mul_eq_one.mp hone).symm
      exact mul_inv_eq_iff_eq_mul.mp he
  refine ⟨u, ⟨u.property, huZ⟩, ⟨?_, hc⟩⟩
  exact Z.mul_mem (Z.inv_mem huZ) hz


theorem omegaCenter_split (hL : IsBlock L) (hm : IsExceptionalA7Block L)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) =
      ((blockU L).map L.subtype ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊔
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  apply le_antisymm ?_ (sup_le inf_le_right inf_le_left)
  intro z hz
  obtain ⟨u, hu, hc⟩ := central_correction L hL hm T hTL hchar z hz
  have hh := (((blockU L).map L.subtype ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊔
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G))).mul_mem
      (mem_sup_left hu) (mem_sup_right hc)
  simpa only [mul_inv_cancel_left] using hh

theorem fixed_line_centralizer_le (hL : IsBlock L) (hm : IsExceptionalA7Block L)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    L ⊓ centralizer (((blockU L).map L.subtype ⊓
      Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) : Set G) ≤
      centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  intro l hl
  apply mem_centralizer_iff.mpr
  intro z hz
  obtain ⟨u, hu, hc⟩ := central_correction L hL hm T hTL hchar z hz
  have he : u * (u⁻¹ * z) = z := mul_inv_cancel_left u z
  calc
    z * l = (u * (u⁻¹ * z)) * l := by rw [he]
    _ = u * ((u⁻¹ * z) * l) := mul_assoc _ _ _
    _ = u * (l * (u⁻¹ * z)) := by rw [(hc.2 l hl.1).symm]
    _ = (u * l) * (u⁻¹ * z) := (mul_assoc _ _ _).symm
    _ = (l * u) * (u⁻¹ * z) := by rw [hl.2 u hu]
    _ = l * z := by rw [mul_assoc, he]

end CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
