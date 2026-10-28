module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.FourMovementCenter
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral

/-!
# The center bound for an actual A₆ source action

A two-group of automorphisms containing the inner image of a specified
Sylow D₈ lies in a full automorphism Sylow subgroup. Its inner intersection
is that exact D₈, by the two Sylow orders. The genuine movement of a
specified four-group then invokes the marked center-line theorem.
This is the action-image form of Aschbacher--Smith 2.5.8(4), pp.556--557;
the source producer retains responsibility for the movement witness.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal

/-- Four-group movement makes the center of the actual two-group action inner
by the originally specified Sylow subgroup of A₆. -/
theorem center_inner_of_four_movement (P : Sylow 2 A6)
    (A : Subgroup AutA6) (hA : IsPGroup 2 A)
    (hPA : (P : Subgroup A6).map MulAut.conj ≤ A)
    (F : Subgroup A6) [IsKleinFour F] (hFP : F ≤ P)
    (hmove : ∃ a ∈ A, F.map a.toMonoidHom ≠ F) :
    (center A).map A.subtype ≤ (P : Subgroup A6).map MulAut.conj := by
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  let J := (P : Subgroup A6).map (MulAut.conj : A6 →* AutA6)
  let D := (Q : Subgroup AutA6) ⊓ inner
  have hDmap : (sylowInner Q).map (Q : Subgroup AutA6).subtype = D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hDcard : Nat.card D = 8 := by
    rw [← hDmap, card_map_of_injective (Q : Subgroup AutA6).subtype_injective,
      sylowInner_card]
  have hJcard : Nat.card J = 8 := by
    rw [card_map_of_injective inner_injective, alternatingSylow_card]
  have hJD : J = D := eq_of_le_of_card_ge
    (le_inf (hPA.trans hAQ) (map_le_range _ _)) (by rw [hDcard, hJcard])
  let Aq := A.subgroupOf (Q : Subgroup AutA6)
  let E := F.map (MulAut.conj : A6 →* AutA6)
  have hEQ : E ≤ Q := (map_mono hFP).trans (hPA.trans hAQ)
  let Eq := E.subgroupOf (Q : Subgroup AutA6)
  let eF := F.equivMapOfInjective (MulAut.conj : A6 →* AutA6) inner_injective
  let : IsKleinFour E := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  let eE := subgroupOfEquivOfLe hEQ
  let : IsKleinFour Eq := {
    card_four := (Nat.card_congr eE.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).trans IsKleinFour.exponent_two }
  have hDA : sylowInner Q ≤ Aq := by
    intro d hd
    have hh : (d : AutA6) ∈ D := ⟨d.property, hd⟩
    rw [← hJD] at hh
    exact hPA hh
  have hED : Eq ≤ sylowInner Q := by
    rintro d ⟨f, _, hf⟩
    exact ⟨f, hf⟩
  have hEmove : ∃ g ∈ Aq, Eq.map (MulAut.conj g).toMonoidHom ≠ Eq := by
    obtain ⟨a, ha, hmove⟩ := hmove
    let g : Q := ⟨a, hAQ ha⟩
    refine ⟨g, ha, ?_⟩
    intro h
    have hh := congrArg (Subgroup.map (Q : Subgroup AutA6).subtype) h
    have hcomp : (Q : Subgroup AutA6).subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp (Q : Subgroup AutA6).subtype := by
      ext x
      rfl
    rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le hEQ] at hh
    change E.map (MulAut.conj a).toMonoidHom = E at hh
    rw [FourNormalizers.inner_map_transport F a] at hh
    exact hmove ((map_injective inner_injective) hh)
  have hcenter := center_image_le_inner_of_four_movement Q Aq Eq hDA hED hEmove
  rintro _ ⟨z, hz, rfl⟩
  let zq : Aq := ⟨⟨z.val, hAQ z.property⟩, z.property⟩
  have hzq : zq ∈ center Aq := by
    apply mem_center_iff.mpr
    intro x
    have hh : x.val.val * z.val = z.val * x.val.val :=
      congrArg Subtype.val (mem_center_iff.mp hz (⟨x.val.val, x.property⟩ : A))
    exact Subtype.ext (Subtype.ext hh)
  have hzD : (z : AutA6) ∈ D :=
    ⟨hAQ z.property, hcenter (mem_map_of_mem Aq.subtype hzq)⟩
  change (z : AutA6) ∈ J
  rwa [hJD]

/-- Carrier transport of the exact source-action center bound. -/
theorem center_inner_of_four_movement_of_equiv {K : Type*} [Group K] [Finite K]
    (e : K ≃* A6) (P : Sylow 2 K) (A : Subgroup (MulAut K)) (hA : IsPGroup 2 A)
    (hPA : (P : Subgroup K).map MulAut.conj ≤ A)
    (F : Subgroup K) [IsKleinFour F] (hFP : F ≤ P)
    (hmove : ∃ a ∈ A, F.map a.toMonoidHom ≠ F) :
    (center A).map A.subtype ≤ (P : Subgroup K).map MulAut.conj := by
  let c := MulAut.congr e
  let B := A.map c.toMonoidHom
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let E := F.map e.toMonoidHom
  let eF := F.equivMapOfInjective e.toMonoidHom e.injective
  let : IsKleinFour E := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  have hconj (x : K) : c (MulAut.conj x) = MulAut.conj (e x) := by
    ext y
    simp [c, MulAut.congr_apply]
  have hQB : (Q : Subgroup A6).map MulAut.conj ≤ B := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hconj x ▸ mem_map_of_mem c.toMonoidHom (hPA (mem_map_of_mem MulAut.conj hx))
  have hEB : E ≤ Q := map_mono hFP
  have hEmove : ∃ b ∈ B, E.map b.toMonoidHom ≠ E := by
    obtain ⟨a, ha, hm⟩ := hmove
    refine ⟨c a, mem_map_of_mem c.toMonoidHom ha, ?_⟩
    intro h
    apply hm
    apply map_injective (f := e.toMonoidHom) e.injective
    have hc : e.toMonoidHom.comp a.toMonoidHom =
        (c a).toMonoidHom.comp e.toMonoidHom := by
      ext x
      simp [c, MulAut.congr_apply]
    rw [map_map, hc, ← map_map]
    exact h
  have hcenter := center_inner_of_four_movement Q B (hA.map c.toMonoidHom) hQB E hEB hEmove
  rintro _ ⟨z, hz, rfl⟩
  have hzB : c z ∈ B := mem_map_of_mem c.toMonoidHom z.property
  have hzC : (⟨c z, hzB⟩ : B) ∈ center B := by
    apply mem_center_iff.mpr
    intro b
    obtain ⟨a, ha, he⟩ := b.property
    apply Subtype.ext
    change (b : AutA6) * c z = c z * (b : AutA6)
    rw [← he]
    change c a * c z = c z * c a
    rw [← map_mul, ← map_mul]
    exact congrArg c (congrArg Subtype.val (mem_center_iff.mp hz (⟨a, ha⟩ : A)))
  have hzQ := hcenter (mem_map_of_mem B.subtype hzC)
  obtain ⟨g, hg, he⟩ := hzQ
  obtain ⟨x, hx, rfl⟩ := hg
  refine ⟨x, hx, ?_⟩
  apply c.injective
  exact (hconj x).trans he

end AlternatingSix.ShadowLocal
