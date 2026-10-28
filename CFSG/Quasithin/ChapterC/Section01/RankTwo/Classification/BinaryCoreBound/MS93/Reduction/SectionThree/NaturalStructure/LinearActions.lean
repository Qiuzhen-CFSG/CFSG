module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.SourceOffenders
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Faithful binary FF-actions on the actual local layers

Conjugation on Z and X descends to the genuine vertex quotient G_a/Q_a.
The exact local centralizer proves faithfulness. Linearization uses the
canonical binary vector space on the same elementary abelian group.

An offender preimage embeds its actual quotient into G_a/Q_a. The fixed
vectors of the image are identified with the native fixed subgroup of its
conjugation action; the proved index inequality then gives the binary
fixed-codimension inequality. No irreducible constituent, natural model,
splitting, or equality X = Z is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), 2.2(vi) and the start of 3.2,
pp.856--857, 863. The SL₃ marking and module-alternative exclusion remain
subsequent obligations.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Offenders
variable {G H Y : Type*} [Group G] [Group H] [Group Y] [IsElementaryAbelian 2 Y]

/-- The canonical binary linear action on the same elementary group. -/
noncomputable def linearize (f : G →* MulAut Y) :
    Representation (ZMod 2) G (Additive Y) where
  toFun g := (f g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (f 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (f (g * h) v.toMul) = _
    rw [map_mul]
    rfl

/-- Faithfulness is unchanged by binary linearization. -/
theorem linearize_injective (f : G →* MulAut Y) (hf : Function.Injective f) :
    Function.Injective (linearize f) := by
  intro g h he
  apply hf
  apply MulEquiv.ext
  intro y
  exact congrArg Additive.toMul (LinearMap.congr_fun he (Additive.ofMul y))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Offenders

open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem quotientConjugation_injective {F : Type*} [Group F]
    (S N Y : Subgroup F) (hn : (N.subgroupOf S).Normal)
    (hSY : S ≤ normalizer (Y : Set F)) (hNY : N ≤ centralizer (Y : Set F))
    (hC : S ⊓ centralizer (Y : Set F) = N) :
    Function.Injective (Offenders.quotientConjugation S N Y hn hSY hNY) := by
  let := hn
  apply (Offenders.quotientConjugation S N Y hn hSY hNY).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H x =>
    apply (QuotientGroup.eq_one_iff x).mpr
    change (x : F) ∈ N
    rw [← hC]
    refine ⟨x.property, ?_⟩
    intro y hy
    have he := congrArg (fun f : MulAut Y => (f ⟨y, hy⟩ : F)) hq
    change (x : F) * y * (x : F)⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The source centralizer identifies the exact kernel of the Z action. -/
theorem LocalSource.Z_quotientConjugation_injective (source : LocalSource L R)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false) :
    Function.Injective (Z_quotientConjugation R a ha) := by
  apply quotientConjugation_injective
  exact source.C_eq_Q geometry.radical_ne_bot a ha

/-- The X action is faithful on the same vertex quotient, without X = Z. -/
theorem LocalSource.X_quotientConjugation_injective (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) :
    Function.Injective (X_quotientConjugation R a) := by
  apply quotientConjugation_injective
  apply le_antisymm
  · have hZX := geometry.omega_bound a ha (by rw [geometry.distance_constant a ha]; exact hb)
    calc
      _ ≤ C R a := inf_le_inf_left _ (centralizer_le hZX)
      _ = _ := source.C_eq_Q geometry.radical_ne_bot a ha
  · exact le_inf (fun _ hx => hx.1) (Q_le_centralizer_X R a)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Offenders
variable {F G H : Type*} [Group F] [Group G] [Group H]
  (Y : Subgroup F) [IsElementaryAbelian 2 Y]


/-- An injective actor map transports the native fixed-index bound to an offender. -/
theorem linearize_isOffender [Finite Y] [Finite H] [Nontrivial H]
    [IsElementaryAbelian 2 H] (f : G →* MulAut Y)
    (i : H →* G) (hi : Function.Injective i)
    (hb : (fixedSubgroup Y (f.comp i)).index ≤ Nat.card H) :
    IsOffender (linearize f) i.range := by
  let : IsElementaryAbelian 2 i.range :=
    IsElementaryAbelian.of_surjective i.rangeRestrict i.rangeRestrict_surjective
  let : Finite i.range := Finite.of_surjective i.rangeRestrict i.rangeRestrict_surjective
  have hc : Nat.card i.range = Nat.card H :=
    (Nat.card_congr (Equiv.ofInjective i hi)).symm
  have hne : i.range ≠ ⊥ := by
    intro he
    obtain ⟨h, hh⟩ := exists_ne (1 : H)
    apply hh
    apply hi
    have hm : i h ∈ i.range := ⟨h, rfl⟩
    rw [he] at hm
    simpa using hm
  let e : fixedSpace (linearize f) i.range ≃ fixedSubgroup Y (f.comp i) := {
    toFun := fun v => ⟨v.val.toMul, fun h =>
      congrArg Additive.toMul (v.property ⟨i h, ⟨h, rfl⟩⟩)⟩
    invFun := fun y => ⟨Additive.ofMul y.val, by
      intro a
      obtain ⟨h, he⟩ := a.property
      change Additive.ofMul (f a.val y.val) = Additive.ofMul y.val
      rw [← he]
      exact congrArg Additive.ofMul (y.property h)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card Y ≤ Nat.card (fixedSubgroup Y (f.comp i)) * Nat.card H := by
    rw [← (fixedSubgroup Y (f.comp i)).card_mul_index]
    exact Nat.mul_le_mul_left _ hb
  rw [← Nat.card_congr e, ← hc] at hcard
  have hVcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Y)
  have hFcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace (linearize f) i.range)
  rw [Nat.card_zmod] at hVcard hFcard
  have hAcard : Nat.card i.range = 2 ^ rank i.range := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 i.range).exists_card_eq
    unfold rank
    rw [hn, Nat.log_pow (by decide : 1 < 2)]
  change Nat.card (Additive Y) ≤ _ at hcard
  rw [hVcard, hFcard, hAcard, ← pow_add] at hcard
  have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  have hr := fixedCodim_add_finrank (linearize f) i.range
  exact ⟨⟨hne, inferInstance⟩, by omega⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Offenders

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Offenders
variable {F : Type*} [Group F] {N T Y : Subgroup F}
  [IsElementaryAbelian 2 Y] [Finite Y]

/-- The source offender quotient embeds in the overgroup quotient and remains an offender. -/
theorem Witness.linear_offender (w : Witness N T Y) [Finite w.A]
    (S : Subgroup F) (hAS : w.A ≤ S) (hnS : (N.subgroupOf S).Normal)
    (hSY : S ≤ normalizer (Y : Set F)) (hNY : N ≤ centralizer (Y : Set F)) :
    letI := w.normal
    letI := hnS
    IsOffender (linearize (quotientConjugation S N Y hnS hSY hNY))
      (quotientInclusion w.A S N hAS w.normal hnS).range := by
  let := w.normal
  let := hnS
  let := w.quotient_nontrivial
  let := w.elementary
  apply linearize_isOffender Y _ _
    (quotientInclusion_injective w.A S N hAS w.normal hnS)
  rw [quotientConjugation_restrict]
  exact w.fixed_index_le_card

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Offenders

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Source 2.2(vi) on Z in the binary representation API, with all source premises discharged. -/
theorem LocalSource.Z_quotient_isFFModule (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) :
    letI := Q_normal R a
    letI := Z_elementary_of_positive R geometry a ha
      (by rw [geometry.distance_constant a ha]; exact hb)
    IsFFModule (Offenders.linearize (Z_quotientConjugation R a ha)) := by
  let := Q_normal R a
  let := Z_elementary_of_positive R geometry a ha
    (by rw [geometry.distance_constant a ha]; exact hb)
  let := finite_Z R a
  obtain ⟨t, hat, ⟨w⟩, _⟩ := source.exists_layer_offenders geometry hb a ha
  let := w.finite
  have hAS : w.A ≤ stabilizer R a :=
    w.le_edge.trans (fun _ hx => hx.2 a (adjacent_symm R hat))
  exact ⟨_, w.linear_offender (stabilizer R a) hAS (Q_normal R a)
    (Z_normalized R a) (le_centralizer_iff.mpr
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)))⟩

/-- Independently, X is an FF-module for the actual vertex quotient. -/
theorem LocalSource.X_quotient_isFFModule (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) :
    letI := Q_normal R a
    letI := X_elementary R a
    IsFFModule (Offenders.linearize (X_quotientConjugation R a)) := by
  let := Q_normal R a
  let := X_elementary R a
  let := finite_X R a
  obtain ⟨t, hat, _, ⟨w⟩⟩ := source.exists_layer_offenders geometry hb a ha
  let := w.finite
  have hAS : w.A ≤ stabilizer R a :=
    w.le_edge.trans (fun _ hx => hx.2 a (adjacent_symm R hat))
  exact ⟨_, w.linear_offender (stabilizer R a) hAS (Q_normal R a)
    (X_normalized R a) (Q_le_centralizer_X R a)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
