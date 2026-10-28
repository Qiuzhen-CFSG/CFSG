module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterInvolution
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Transfer
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow

/-!
# Triality involution centralizer lower bounds in the original completion

On the genuine arms radical, commutation with the marked highest short root
is the kernel of the surjective character Tr(c F(1)). Its index is q in the
radical of order q^9, so its kernel has order q^8. This uses the actual
cubic trace and faithful descended root coordinates, including field two.

The original right-parabolic comparison transports this subgroup into S.
The same comparison sends the highest long root to an element centralizing
all of S, of order q^12. The checked two-class reduction, using both local
maps and cyclic quotient transfer, then puts a conjugate of one of these
two-groups inside every ambient involution centralizer. Thus every Sylow
two-subgroup of every such centralizer has order at least q^8.

This is the lower-bound half of the triality F.4.38 contradiction, without
assuming S=T, an odd exponent or an ambient model isomorphism. The outer
involution fixed-root upper bound and its Sylow placement from F.4.37
remain necessary. Original uniqueness, exhaustive compatible comparison
and final recognition remain with the generic-global assembly. The
Chapter 12 companion supplies the literal chosen-module applications.

Source: Aschbacher–Smith F.4.35, F.4.37–38, pp.292–294, and 5.3.3,
p.659 (`refs/quasithin.pdf`); GLS3 2.4.5(b), for the cubic trace pairing.
The internal imports reuse the general injective centralizer transport
and Sylow comparison proofs within this source family, preserving their
existing public boundaries.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCentralizerBounds

private def shortParameters (P : Parameters) : ArmsParameters P := (![0,1],![0,0,0])

private theorem short_parameters_val (P : Parameters) (hp : P.prime=2) :
    (armsEquiv P hp (shortParameters P)).val = short P hp 2 1 := by
  have hh := armsCoordinates_factorization P hp (shortParameters P)
  change (armsCoordinates P hp (shortParameters P)).val = _
  simpa [shortParameters] using hh

private theorem short_commutator (P : Parameters) (v : ArmsParameters P) :
    armsCommutator P v (shortParameters P) = armsPairing P (v.1 0) 1 := by
  simp [armsCommutator,armsCocycle,shortParameters]

private def shortCharacter (P : Parameters) (hp : P.prime=2) :
    armsSubgroup P →* Multiplicative (fixedField P) where
  toFun x := .ofAdd (armsPairing P (((armsEquiv P hp).symm x).1 0) 1)
  map_one' := by
    have hz : (armsEquiv P hp).symm 1 = centralParameters P 0 := by
      apply (armsEquiv P hp).injective
      rw [Equiv.apply_symm_apply]
      exact ((armsEquiv_central_eq_one_iff P hp 0).mpr rfl).symm
    simp [hz,centralParameters]
  map_mul' x y := by
    obtain ⟨v,rfl⟩ := (armsEquiv P hp).surjective x
    obtain ⟨w,rfl⟩ := (armsEquiv P hp).surjective y
    rw [←armsEquiv_multiply]
    simp only [Equiv.symm_apply_apply,armsMultiply,Pi.add_apply,armsPairing_add_left]
    rfl

private theorem shortCharacter_surjective (P : Parameters) (hp : P.prime=2) :
    Function.Surjective (shortCharacter P hp) := by
  intro z
  obtain ⟨c,hc⟩ := armsPairing_surjective_left P hp 1 one_ne_zero z.toAdd
  refine ⟨armsEquiv P hp (![c,0],![0,0,0]),?_⟩
  change Multiplicative.ofAdd (armsPairing P (((armsEquiv P hp).symm
    (armsEquiv P hp (![c,0],![0,0,0]))).1 0) 1) = z
  simp only [Equiv.symm_apply_apply,Matrix.cons_val_zero,hc]
  rfl

private theorem shortCharacter_kernel (P : Parameters) (hp : P.prime=2) :
    (shortCharacter P hp).ker =
      centralizer ({armsEquiv P hp (shortParameters P)} : Set (armsSubgroup P)) := by
  ext x
  obtain ⟨v,rfl⟩ := (armsEquiv P hp).surjective x
  rw [mem_centralizer_singleton_iff,←commutatorElement_eq_one_iff_mul_comm,
    armsEquiv_commutator,armsEquiv_central_eq_one_iff,short_commutator]
  change Multiplicative.ofAdd (armsPairing P (((armsEquiv P hp).symm (armsEquiv P hp v)).1 0) 1) = 1 ↔ _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The marked short root has a q^8 centralizer already in the genuine arms radical. -/
theorem short_arms_centralizer_card (P : Parameters) (hp : P.prime=2) :
    Nat.card (radical P .arms ⊓ centralizer ({short P hp 2 1} : Set (Carrier P)) : Subgroup (Carrier P)) = P.q^8 := by
  let f := shortCharacter P hp
  have hmul : Nat.card f.ker * P.q = P.q^9 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr (shortCharacter_surjective P hp),
      Subgroup.card_top,Nat.card_congr Multiplicative.toAdd,card_fixedField] at hh
    exact hh.trans (card_descendedRootSubgroup P hp .arms)
  have hc : Nat.card f.ker = P.q^8 := by
    apply Nat.eq_of_mul_eq_mul_right (by have := P.q_ge_two; omega : 0<P.q)
    simpa only [pow_succ] using hmul
  have hm := G2ShortSylow.centralizer_image (armsSubgroup P).subtype
    (armsSubgroup P).subtype_injective ⊤ (armsEquiv P hp (shortParameters P))
  rw [top_inf_eq,←MonoidHom.range_eq_map,range_subtype] at hm
  change _ = armsSubgroup P ⊓ centralizer ({(armsEquiv P hp (shortParameters P)).val} : Set (Carrier P)) at hm
  rw [short_parameters_val] at hm
  rw [radical_eq_descendedRootSubgroup P hp .arms,←hm,
    card_map_of_injective (armsSubgroup P).subtype_injective,←shortCharacter_kernel]
  exact hc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCentralizerBounds

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem triality_centralizer_card_transport
    (P : Parameters) (f : parabolic P .arms →* G) (hf : Function.Injective f)
    (S : Subgroup G) (hS : ((unipotent P).subgroupOf (parabolic P .arms)).map f=S)
    (x : parabolic P .arms) :
    Nat.card (S ⊓ centralizer ({f x} : Set G) : Subgroup G) =
      Nat.card (unipotent P ⊓ centralizer ({x.val} : Set (Carrier P)) : Subgroup (Carrier P)) := by
  have hm := G2ShortSylow.centralizer_image f hf ((unipotent P).subgroupOf (parabolic P .arms)) x
  rw [hS] at hm
  have hn := G2ShortSylow.centralizer_image (parabolic P .arms).subtype Subtype.val_injective
    ((unipotent P).subgroupOf (parabolic P .arms)) x
  rw [map_subgroupOf_eq_of_le ((unipotent_le_borel P).trans (borel_le_parabolic P .arms))] at hn
  change _ = unipotent P ⊓ centralizer ({x.val} : Set (Carrier P)) at hn
  rw [←hm,←hn,card_map_of_injective hf,card_map_of_injective Subtype.val_injective]

/-- In the original S the marked long root has centralizer of order q^12,
and the marked short root centralizes at least q^8 elements. Both markings
use the same right map of the whole-overlap comparison. -/
theorem Preparation.triality_marked_source_centralizer_bounds
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let z : G := (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val
    let v : G := (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).val
    Nat.card (sourceS L H ⊓ centralizer ({z} : Set G) : Subgroup G)=P.q^12 ∧
      P.q^8 ≤ Nat.card (sourceS L H ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  have hS := d.triality_right_unipotent_image h hTH P rfl e
  have hz := triality_centralizer_card_transport P f hf _ hS (TrialityCompletionFusion.longElement P rfl)
  have hv := triality_centralizer_card_transport P f hf _ hS (TrialityCompletionFusion.shortElement P rfl)
  constructor
  · apply hz.trans
    have hUC : unipotent P ≤ centralizer ({(TrialityCompletionFusion.longElement P rfl).val} : Set (Carrier P)) := by
      intro u hu
      apply mem_centralizer_singleton_iff.mpr
      have hh := highestRoot_le_center_unipotent P rfl (show
          highestHom P rfl (Multiplicative.ofAdd 1) ∈ highestRoot P from by
        rw [←highestHom_range P rfl]
        exact ⟨_,rfl⟩)
      obtain ⟨z,hz,he⟩ := hh
      change u * highestHom P rfl (Multiplicative.ofAdd 1) =
        highestHom P rfl (Multiplicative.ofAdd 1) * u
      rw [←he]
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨u,hu⟩)
    rw [inf_eq_left.mpr hUC]
    exact ConcreteBruhat.FixedCellCount.card_unipotent m hm
  · change P.q^8 ≤ Nat.card (sourceS L H ⊓ centralizer ({f (TrialityCompletionFusion.shortElement P rfl)} : Set G) : Subgroup G)
    rw [hv]
    change P.q^8 ≤ Nat.card (unipotent P ⊓ centralizer ({short P rfl 2 1} : Set (Carrier P)) : Subgroup (Carrier P))
    rw [←TrialityCentralizerBounds.short_arms_centralizer_card P rfl]
    apply card_le_of_le
    apply inf_le_inf_right
    rw [radical_eq_descendedRootSubgroup P rfl .arms]
    exact descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P rfl .arms)

/-- Every ambient involution centralizer has Sylow two-subgroups of order at
least q^8. Cyclic quotient transfer and both actual local maps supply the
two-class reduction, so this holds without S=T or an odd exponent. -/
theorem Preparation.triality_involution_centralizer_sylow_lower_bound
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse))
    (x : G) (hx : orderOf x=2) (R : Sylow 2 (centralizer ({x} : Set G))) :
    (binaryParameters m hm).q^8 ≤ Nat.card R := by
  obtain ⟨e,z,v,hz,hv,_,_,_,_,_,hc⟩ := d.triality_ambient_involution_classes h hH hp m hm he
  obtain ⟨hzcard,hvcard⟩ := d.triality_marked_source_centralizer_bounds h hH.1.1.2 m hm e
  rw [←hz] at hzcard
  rw [←hv] at hvcard
  rcases hc x hx with hzx | hvx
  · have hb := centralizer_sylow_card_lower (sourceS L H) (pCore_isPGroup.map _) x z.val hzx R
    rw [hzcard] at hb
    exact (Nat.pow_le_pow_right (by have := (binaryParameters m hm).q_ge_two; omega)
      (by decide : 8≤12)).trans hb
  · exact hvcard.trans (centralizer_sylow_card_lower (sourceS L H) (pCore_isPGroup.map _) x v.val hvx R)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
