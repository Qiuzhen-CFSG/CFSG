module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity.Images
public import CFSG.Quasithin.ChapterC.Section01.BlockCentralQuotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceFixedSpace
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.CheckedPoint
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Checked Borel fixation forces fixation of the field-four block

The central two-group quotient preserves the actual block module model.
Its Sylow and relative Borel are the literal checked images, since the
kernel lies in S. The model's own coordinates can be conjugated to mark
this Borel, so natural-layer rigidity makes the checked component fix the
checked involution. Two-perfectness then lifts fixation through ⟨v⟩.

The final theorem applies to the actual `FlagSource.checkedPoint` and
`markedA`. Its only fixation premise is the checked Borel fixation proved
by `BorelGeometry.source_geometry`; all membership, involution, quotient
model and coordinate conditions are discharged here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
last paragraph of 13.6.18, printed p.931 (PDF p.948).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity
open Subgroup ChapterC A5Module
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The natural model descends through the literal checked quotient. -/
theorem checked_model (K : Subgroup G) (v : G) (hK : K ≤ Gv v)
    (hv : v ^ 2 = 1) (hp : IsPPerfect 2 K)
    {A W : Type*} [Group A] [Group W]
    (ρ : A →* MulAut W) (m : BlockModuleModel K ρ) :
    Nonempty (BlockModuleModel (checkedImage v K) ρ) := by
  let f : K →* checkedImage v K :=
    ((checkedQuotientMap v).subgroupMap (K.subgroupOf (Gv v))).comp
      (subgroupOfEquivOfLe hK).symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((checkedQuotientMap v).subgroupMap_surjective _).comp
      (subgroupOfEquivOfLe hK).symm.surjective
  have hk : f.ker = (checkedQuotientMap v).ker.comap (inclusion hK) := by
    ext k
    change f k = 1 ↔ checkedQuotientMap v (inclusion hK k) = 1
    exact Subtype.ext_iff
  have hpq : IsPGroup 2 (checkedQuotientMap v).ker := by
    rw [checkedQuotientMap_kernel]
    apply IsPGroup.of_card_dvd_pow (n := 1)
    change Nat.card (zpowers (centralElement v)) ∣ 2 ^ 1
    rw [Nat.card_zpowers]
    simpa only [pow_one] using orderOf_dvd_of_pow_eq_one
      (show centralElement v ^ 2 = 1 from Subtype.ext hv)
  have hpk : IsPGroup 2 f.ker := by
    rw [hk]
    exact hpq.comap_of_injective (inclusion hK) (inclusion_injective hK)
  have hck : f.ker ≤ center K := by
    intro k hfk
    have hc : inclusion hK k ∈ center (Gv v) := by
      apply vLine_le_center v
      rw [← checkedQuotientMap_kernel]
      change k ∈ (checkedQuotientMap v).ker.comap (inclusion hK)
      rwa [← hk]
    apply mem_center_iff.mpr
    intro l
    apply Subtype.ext
    exact congrArg (fun x : Gv v => (x : G)) (mem_center_iff.mp hc (inclusion hK l))
  let : Finite (checkedImage v K) := Finite.of_surjective f hf
  exact ChapterC.BlockModuleModel.exists_of_central_two_quotient f hf hp hpk hck ρ m

/-- Checked fixation of the actual Borel forces fixation of the field-four block.
All coordinates and quotient comparisons are derived from the actual block. -/
theorem centralizes_of_checked_borel_fixation (K S : Subgroup G) (v : G)
    (hv : v ^ 2 = 1) (hvS : v ∈ S) (hK : K ≤ Gv v) (hS : S ≤ Gv v)
    (hSK : S ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 S (K ⊔ S)) (hb : IsL2EvenBlock K 2)
    (a : Gv v) (haS : (a : G) ∈ S) (ha2 : a ^ 2 = 1)
    (haB : checkedQuotientMap v a ∈ centralizer (checkedImage v (borel K S) : Set (Gcheck v))) :
    K ≤ centralizer ({(a : G)} : Set G) := by
  let : Finite (Gcheck v) := inferInstanceAs (Finite (Gv v ⧸ vLine v))
  obtain ⟨_, hshort, F, hField, hFinite, hF, _, ρ, ⟨m⟩, hρ⟩ := hb
  let := hField
  let := hFinite
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  obtain ⟨m'⟩ := checked_model K v hK hv hshort.twoPerfect ρ m
  apply Source.centralizes_of_checked_centralizes K v a hK hshort.twoPerfect hv
  apply centralizes_of_natural_borel_fixation (checkedImage v K) (checkedImage v S)
    (checked_normalizes K S v hSK) (checked_sylow K S v hK hS hSylow) ρ m'
    hρ (by rw [hF]; norm_num) (checkedQuotientMap v a)
    (by rw [← map_pow, ha2, map_one]) (mem_map_of_mem _ haS)
  rwa [← checkedImage_borel K S v hK hS hSK hvS]

/-- Apply checked rigidity to the source's specified a and literal checked point.
The sole fixation premise is exactly the checked conclusion of source_geometry. -/
theorem source_marked_centralizes {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (K : Subgroup G)
    (hK : K ≤ Gv (markedV d.module))
    (hSK : Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.module))
      (K ⊔ Tv (T : Subgroup G) (markedV d.module)))
    (hb : IsL2EvenBlock K 2)
    (hfix : checkedSylowMap (T : Subgroup G) (markedV d.module) d.checkedPoint ∈
      centralizer (checkedImage (markedV d.module)
        (borel K (Tv (T : Subgroup G) (markedV d.module))) : Set (Gcheck (markedV d.module)))) :
    K ≤ centralizer ({markedA d.module} : Set G) := by
  have hv2 : markedV d.module ^ 2 = 1 := by
    change d.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
    rw [← map_pow, show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1 by
      rw [pow_two]
      change Multiplicative.ofAdd (BinaryPermutation.FiveCentralizerGeometry.v +
        BinaryPermutation.FiveCentralizerGeometry.v) = 1
      rw [show BinaryPermutation.FiveCentralizerGeometry.v + BinaryPermutation.FiveCentralizerGeometry.v = 0 by
        apply Subtype.ext; ext i; fin_cases i <;> decide]
      rfl, map_one]
  have hvS : markedV d.module ∈ Tv (T : Subgroup G) (markedV d.module) :=
    ⟨d.V_le_T (map_mem d.module _), mem_centralizer_singleton_iff.mpr rfl⟩
  let a : Gv (markedV d.module) := inclusion inf_le_right d.checkedPoint
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    change markedA d.module ^ 2 = 1
    obtain ⟨c, _, hc⟩ := exists_a_conjugator d.module
    rw [← hc, ← map_pow, d.module.markedZ_pow_two, map_one]
  exact centralizes_of_checked_borel_fixation K _ _ hv2 hvS hK inf_le_right hSK
    hSylow hb a d.checkedPoint.property ha2 hfix
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity
