module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallImages

/-!
# Full root images from small critical indices

A surjective natural quotient transports quadraticity of the actual critical
actor directly, without choosing a splitting of the central attachment.
The reciprocal comparison makes both indices q when one is smaller than q².
The natural fixed-index bound then forces one-dimensional displacement for
the full actor image, which is consequently an actual full long root.

The following NoncentralPair module uses its two-subgroup normalizer to
exclude these small images in a noncentral mixed triple.
Source: MS93 (3.3), printed p.867, and (5.2)(ii), printed p.914.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

section Local
variable {M E : Type*} [Group M] [Field E]
variable {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}

/-- The literal surjective natural quotient inherits the critical quadratic action. -/
theorem critical_quotient_actor_quadratic
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (π : U R z →* Multiplicative (Vector E)) (hπ : Function.Surjective π)
    (δ : Z R a →* Sp E)
    (hact : ∀ (x : Z R a) (u : U R z),
      π ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path x.property) u.val).mp u.property⟩ =
        Multiplicative.ofAdd (δ x • (π u).toAdd)) :
    ∀ x ∈ δ.range, ∀ y ∈ δ.range, ∀ v : Vector E,
      x • (y • v-v)=y • v-v := by
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a path.start_color
  rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ v
  obtain ⟨u,hu⟩ := hπ (Multiplicative.ofAdd v)
  let w : U R z := ⟨⁅y.val,u.val⁆,
    le_normalizer_iff_commutator_le_right.mp (critical_actor_normalizes_moving path)
      (commutator_mem_commutator y.property u.property)⟩
  have hwZ : w.val ∈ Z R a := critical_commutator_le_start_seed path
    (commutator_mem_commutator y.property (U_le_Z z u.property))
  have hw : π w = Multiplicative.ofAdd (δ y • v-v) := by
    let yu : U R z := ⟨y.val*u.val*y.val⁻¹,
      (mem_normalizer_iff.mp (critical_actor_normalizes_moving path y.property) u.val).mp u.property⟩
    have he : w = yu*u⁻¹ := by apply Subtype.ext; rfl
    rw [he,map_mul,map_inv,hact,hu]
    simp only [toAdd_ofAdd,ofAdd_sub,div_eq_mul_inv]
  have hxw : x.val*w.val*x.val⁻¹=w.val := by
    have hc := (Z R a).le_centralizer hwZ x.val x.property
    rw [hc,mul_inv_cancel_right]
  have hh := hact x w
  have he : (⟨x.val*w.val*x.val⁻¹,
      (mem_normalizer_iff.mp (critical_actor_normalizes_moving path x.property) w.val).mp w.property⟩ : U R z)=w :=
    Subtype.ext hxw
  rw [he,hw] at hh
  exact (congrArg Multiplicative.toAdd hh).symm
end Local

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A small critical image has field-sized order and a quadratic displacement line
under any compatible natural quotient marking. -/
theorem Input.replacement_small_critical_root_image
    {E : Type*} [Field E] [Finite E]
    (hEF : Nat.card E = Nat.card F)
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (π : U d.radical z →* Multiplicative (Vector E)) (hπ : Function.Surjective π)
    (δ : Z d.radical a →* Sp E)
    (hcard : Nat.card δ.range = (Q d.radical z).relIndex (Z d.radical a))
    (hact : ∀ (x : Z d.radical a) (u : U d.radical z),
      π ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path x.property) u.val).mp u.property⟩ =
        Multiplicative.ofAdd (δ x • (π u).toAdd))
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F ^ 2) :
    Nat.card δ.range = Nat.card E ∧
      Module.finrank E (displacementSpace δ.range) = 1 ∧
      (∀ x ∈ δ.range, ∀ y ∈ δ.range, ∀ v : Vector E,
        x • (y • v-v)=y • v-v) := by
  have hi := h.replacement_small_critical_indices_eq_field d path hb hsmall
  have hc : Nat.card δ.range = Nat.card E := hcard.trans (hi.1.trans hEF.symm)
  have hzS : Z d.radical z ≤ stabilizer d.radical a := path.endpoint_Z_le_start_stabilizer hb
  have hC : C d.radical a = Q d.radical a := MSCentralOrbit.C_eq_Q _
    (h.replacement_two_group d) (h.replacement_core_le d)
    (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hidx : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z) = (Q d.radical a).relIndex (Z d.radical z) := by
    rw [←hC]
    change _ = ((stabilizer d.radical a) ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex _
    change ((centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).subgroupOf (Z d.radical z)).index =
      ((stabilizer d.radical a ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).subgroupOf (Z d.radical z)).index
    congr 1
    ext x
    exact ⟨fun hx => ⟨hzS x.property,hx⟩,fun hx => hx.2⟩
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hfix : Nat.card (Vector E ⧸ TwoLocalCover.fixedSpace δ.range) ≤ Nat.card E := by
    apply (fixed_quotient_card_le_centralizer_index (U d.radical z) (Z d.radical a)
      (critical_actor_normalizes_moving path) π hπ δ hact).trans
    apply (relIndex_le_of_le_right (U_le_Z z) index_ne_zero_of_finite).trans
    rw [hidx,hi.2,hEF]
  have hE : 1 < Nat.card E := by
    rw [hEF,h.field_card]
    exact lt_of_lt_of_le (by decide : 1 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hdle : Module.finrank E (displacementSpace δ.range) ≤ 1 := by
    rw [fixed_quotient_card] at hfix
    by_contra hn
    have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ Nat.card E)
      (show 2 ≤ Module.finrank E (displacementSpace δ.range) by omega)
    nlinarith
  have hdne : Module.finrank E (displacementSpace δ.range) ≠ 0 := by
    intro hz
    have hh := card_actor_le_displacement_dimension δ.range
    rw [hz,hc] at hh
    norm_num at hh
    omega
  exact ⟨hc,by omega,critical_quotient_actor_quadratic path hb π hπ δ hact⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
