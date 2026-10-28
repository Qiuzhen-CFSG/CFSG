module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.OuterIntersection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.OuterAction.Plane
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.OuterGroup
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Transport

/-!
# Excluding the outer branch on the actual marked star action

The original normal solvable X is the recovered cubic factor. Its moved
plane gives a three-point action of the whole star group, compatible with
the second coordinate on the offender subgroup. The marked nonzero
commutator of 13.6.11 proves that the actual Lᵥ* moves this plane.

The intersection argument applies the parity restriction to O²(Lᵥ* ∩ I)
using the literal Sylow intersection, and proves Lᵥ* = X. Thus Lᵥ* is normal
and its moved space has order four. The genuine earlier splitting of Vᵥ
then contradicts its relative nonnormality in Gᵥ from 13.6.8.

The recovered-action premise is discharged by the five-input source
application in `Outer`. There is no ambient parity isomorphism, assumed
subnormality of Lᵥ*, or splitting with the global fixed space.
Source: Aschbacher–Smith, 13.6.11–13, printed pp.928–929, and B.5.7, p.106.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
open ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
open SourceAction ChapterB.QuasisimpleSource

variable {G : Type*} [Group G] [Finite G]

/-- In the outer branch, the actual Sylow-normalized Lᵥ* is the original X.
The recovered action and its literal coordinates are those on the offender
restriction; no ambient actor equivalence or factor decomposition is assumed. -/
theorem minimalSolvable_outer_starLv_eq
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (c : ChapterB.OuterSixThreeShape
      (FFFactors.offenderActor (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))))
    (d : RecoveredAction
      (D := FFFactors.offenderActor (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))
      (W := Additive (Uv (A5Module.markedZ s) (A5Module.markedV s)))
      c (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))) :
    starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)) = X := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  let ρ := starRepresentation z v
  let I := FFFactors.offenderActor ρ
  let R := starImage z v (Lv L v)
  let C := starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))
  let : X.Normal := hX.1.2
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  have hXI := XFamily_le_star_offender L T z v (A5Module.markedZ_mem_Gv s) S hS hX.1
  have hsecond := minimalSolvable_outer_eq_second L T z v (A5Module.markedZ_mem_Gv s) S hS hX c
  have hXcard := minimalSolvable_outer_card L T z v (A5Module.markedZ_mem_Gv s) S hS hX c
  obtain ⟨f, hfixf, hker⟩ := OuterAction.extend_plane ρ I X hXI c d hsecond
  have hfX : X.map f ≠ ⊥ := by
    intro he
    let : Nontrivial X := (nontrivial_iff_ne_bot X).mpr hX.1.1.2.2.1
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    have hf : f x = 1 := (map_eq_bot_iff X).mp he x.property
    have hfaith := odd_moved_faithful ρ (starRepresentation_injective z v) X
      (by rw [hXcard]; decide)
    apply hx
    apply hfaith
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ρ (x : Gstar z v) (w : Additive (Uv z v)) = ρ 1 (w : Additive (Uv z v))
    rw [map_one, Module.End.one_apply]
    exact (hfixf x).mp hf w w.property
  have hfR : R.map f ≠ ⊥ := by
    intro he
    have hc : Lv L v ≤ centralizer (movedSubgroup z v X : Set G) := by
      intro l hl u hu
      let l' : Gv v := ⟨l, Lv_le_Gv L v hl⟩
      let u' : Uv z v := ⟨u, movedSubgroup_le_Uv z v X hu⟩
      have hw : Additive.ofMul u' ∈ moved ρ X := by
        apply (mem_ambientSpace z v _ u').mp
        rwa [moved_ambientSpace]
      have hf : f (starMk z v l') = 1 := (map_eq_bot_iff R).mp he ⟨l', hl, rfl⟩
      have ha := (hfixf (starMk z v l')).mp hf (Additive.ofMul u') hw
      have ha' := congrArg (fun w : Additive (Uv z v) => (w.toMul : G)) ha
      change ((starRepresentation z v (starMk z v l') (Additive.ofMul u')).toMul : G) = u at ha'
      rw [starRepresentation_mk_apply] at ha'
      exact (mul_inv_eq_iff_eq_mul.mp ha').symm
    apply (marked_Xz_commutators_ne_bot s T S hS hfix (XFamily_subset_Xz L T z v hX.1)).2
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (UX_le_moved L z v X).trans (le_centralizer_iff.mp hc)
  obtain ⟨P, hP⟩ := FactorArgument.exists_starSylow T z v S hS
  obtain ⟨n, hn⟩ := FactorArgument.starLv_card_dvd L z v hcard
  have hmark : (X.subgroupOf I).map d.ambient.actorEquiv.toMonoidHom = SixPoint.cubic := by
    ext y
    obtain ⟨i, rfl⟩ := d.ambient.actorEquiv.surjective y
    rw [mem_map_equiv, d.ambient.actorEquiv.symm_apply_apply, hsecond]
    change i ∈ c.second ↔ i ∈ (SixPoint.firstProjection.comp d.ambient.actorEquiv.toMonoidHom).ker
    rw [d.ambient.first_kernel]
  apply OuterIntersection.eq_cubic_of_plane_action I d.ambient.actorEquiv X R C hXI hXcard
    (XFamily_isPPerfect L T z v hX.1) hmark P
    (by rw [hP]; exact FactorArgument.starTv_normalizes_starLv L T z v hL)
    (thompson_le_star_offender T z v (A5Module.markedZ_mem_Gv s) S hS)
    (by rw [hP]; exact map_mono (comap_mono (sSup_le fun _ hA => hA.1)))
    hX.1.1.2.2.2 (FactorArgument.starLv_twoPerfect L z v) hn f hker hfX hfR

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
open SourceAction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
variable [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({(A5Module.markedZ s)} : Set G))
    (hT : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hV : IsPGroup 2 V) (hL : Lv L (A5Module.markedV s) ≤ normalizer (V : Set G))
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    (hsplit : Vv L (A5Module.markedZ s) (A5Module.markedV s) = zpowers (A5Module.markedV s) ⊔ ⁅V, Lv L (A5Module.markedV s)⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L (A5Module.markedV s)⁆ : Subgroup G) = 4)
    (hnormal : ¬ ((Vv L (A5Module.markedZ s) (A5Module.markedV s)).subgroupOf (Gv (A5Module.markedV s))).Normal)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))} (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)

include S hS hfix hT hV hL hcard hsplit hsmall hnormal hX

/-- The recovered outer action contradicts the genuine relative nonnormality
of 13.6.8. The two-plane bound and normality of Lᵥ* are proved internally.
Only the actual earlier local module data remain explicit. -/
theorem minimalSolvable_outer_excluded_of_recovered
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))))
    (d : RecoveredAction c (FFFactors.offenderRepresentation (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))) : False := by
  have heq := minimalSolvable_outer_starLv_eq s T S hS hfix hT hcard hX c d
  have hXI := XFamily_le_star_offender L T (A5Module.markedZ s) (A5Module.markedV s) (A5Module.markedZ_mem_Gv s) S hS hX.1
  have hsecond := minimalSolvable_outer_eq_second L T (A5Module.markedZ s) (A5Module.markedV s)
    (A5Module.markedZ_mem_Gv s) S hS hX c
  have hdim : Module.finrank (ZMod 2)
      (moved (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)) X) = 2 := by
    change Module.finrank (ZMod 2)
      (subspaceCommutator (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)) ⊤ X) = 2
    rw [← FFFactors.marked_commutator (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)) X hXI ⊤,
      hsecond]
    exact d.recovered.plane
  have hlarge : Nat.card ↥(⁅Uv (A5Module.markedZ s) (A5Module.markedV s), Lv L (A5Module.markedV s)⁆ : Subgroup G) = 4 := by
    rw [← Subnormal.commutator_starPreimage_starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)) (Lv_le_Gv L (A5Module.markedV s)), heq]
    change Nat.card (movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) X) = 4
    rw [← moved_ambientSpace, ambientSpace_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    rfl
  have hn : (starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s))).Normal := heq.symm ▸ hX.1.2
  have hm := Subnormal.moved_eq_of_card_le_four L V (A5Module.markedZ s) (A5Module.markedV s) hV hL hsplit hsmall hlarge.le
  exact hnormal (normal_subgroupOf_of_le_normalizer
    (Subnormal.Vv_normalized_of_star_normal_of_moved_eq L V (A5Module.markedZ s) (A5Module.markedV s) hn hm hsplit))


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional
