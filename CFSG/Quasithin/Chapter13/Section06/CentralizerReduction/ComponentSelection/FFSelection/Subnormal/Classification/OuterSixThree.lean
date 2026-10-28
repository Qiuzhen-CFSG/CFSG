module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Setup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore
/-!
# Cubic bounds in the outer A₆ × C₃ alternative

The full commutator condition A = [A,C] puts the restricted cubic in J′.
The quotient of J by its two factors is cyclic, so J′ lies in their product.
The projection of O₃(J) intersected with that product onto the A₆ factor
is a normal three-subgroup and hence trivial. Thus O₃(J) ∩ J′ lies in the
specified C₃ factor, and the cubic order forces A to be that factor.

In fact A = O₃(J) ∩ J′ is characteristic in the normal offender subgroup J,
so A is normal in the original ambient group. Its moved space is exactly
the supplied two-dimensional moved space of the second factor. The literal
marked application supplies all cubic hypotheses through Setup.

The argument does not assume that the outer generator is an involution,
that the extension splits, or that O₃(J) equals the second factor. It uses
neither the fixed-space splitting nor the first-factor dimension fields of
the outer alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(4),
printed p.105, and its application in 13.6.10, printed p.928.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
variable {D : Type*} [Group D] [Finite D]
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W)

private theorem six_threeCore : pCore 3 (alternatingGroup (Fin 6)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (pCore 3 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top
    with hb | ht
  · exact hb
  · have hp := pCore_isPGroup (p := 3) (G := alternatingGroup (Fin 6))
    rw [ht] at hp
    have hp' : IsPGroup 3 (alternatingGroup (Fin 6)) := hp.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp'
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup]
      norm_num
    have htwo : 2 ∣ 3 ^ n := hn ▸ (by rw [hc]; norm_num)
    have := Nat.prime_two.dvd_of_dvd_pow htwo
    norm_num at this

omit [Finite D] in
private theorem core_derived_le_second (c : OuterSixThreeCase ρ) :
    pCore 3 D ⊓ _root_.commutator D ≤ c.second := by
  have hfirst : pCore 3 c.first = ⊥ := by
    apply map_injective (f := c.firstEquiv.toMonoidHom) c.firstEquiv.injective
    rw [pCore_map_iso, Subgroup.map_bot, six_threeCore]
  let f : (c.first × c.second) →* D :=
    (c.first ⊔ c.second).subtype.comp c.product.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp c.product.injective
  let R := (pCore 3 D).comap f
  have hp : IsPGroup 3 R := pCore_isPGroup.comap_of_injective f hf
  have hmap : R.map (MonoidHom.fst c.first c.second) ≤ pCore 3 c.first :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ Prod.fst_surjective, hp.map _⟩
  rw [hfirst] at hmap
  have hk : R ≤ (MonoidHom.fst c.first c.second).ker :=
    (map_eq_bot_iff R).mp (le_bot_iff.mp hmap)
  let := c.product_normal ρ
  let := c.quotient_isCyclic ρ
  have hd : _root_.commutator D ≤ c.first ⊔ c.second :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rintro x ⟨hx, hxd⟩
  let y := c.product.symm ⟨x, hd hxd⟩
  have he : (c.product y : D) = x := congrArg Subtype.val (c.product.apply_symm_apply _)
  have hy : y ∈ R := by
    change (c.product y : D) ∈ pCore 3 D
    rwa [he]
  have hy1 : y.1 = 1 := hk hy
  have he' : x = (y.2 : D) := by
    calc
      x = (c.product (y.1, y.2) : D) := he.symm
      _ = (y.1 : D) * (y.2 : D) := c.product_apply _ _
      _ = (y.2 : D) := by simp [hy1]
  rw [he']
  exact y.2.property

variable {ρ} {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
omit [Finite D] in
private theorem internal_le_derived (h : CubicHypothesis ρ A S C) :
    A.subgroupOf (offenderSubgroup ρ) ≤ _root_.commutator (offenderSubgroup ρ) := by
  rw [h.internal_full]
  exact commutator_mono le_top le_top

/-- The actual restricted cubic is the specified C₃ factor, using its
subnormality and full commutator condition, with no factor placement assumed. -/
theorem outerSixThree_internal_eq_second (h : CubicHypothesis ρ A S C)
    (c : OuterSixThreeCase (offenderRepresentation ρ)) :
    A.subgroupOf (offenderSubgroup ρ) = c.second := by
  apply eq_of_le_of_card_ge
    ((le_inf h.internal_le_threeCore (internal_le_derived h)).trans
      (core_derived_le_second (offenderRepresentation ρ) c))
  rw [h.internal_card, Nat.card_congr c.secondEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- An intrinsic characteristic description of the cubic inside J.
The three-core itself need not be identified. -/
theorem outerSixThree_internal_eq_core_derived (h : CubicHypothesis ρ A S C)
    (c : OuterSixThreeCase (offenderRepresentation ρ)) :
    A.subgroupOf (offenderSubgroup ρ) =
      pCore 3 (offenderSubgroup ρ) ⊓ _root_.commutator (offenderSubgroup ρ) := by
  apply le_antisymm (le_inf h.internal_le_threeCore (internal_le_derived h))
  rw [outerSixThree_internal_eq_second h c]
  exact core_derived_le_second (offenderRepresentation ρ) c

/-- The cubic in the outer alternative is normal in the original ambient D. -/
theorem outerSixThree_normal (h : CubicHypothesis ρ A S C)
    (c : OuterSixThreeCase (offenderRepresentation ρ)) : A.Normal := by
  have hchar : (A.subgroupOf (offenderSubgroup ρ)).Characteristic := by
    rw [outerSixThree_internal_eq_core_derived h c]
    infer_instance
  let := hchar
  have hn : ((A.subgroupOf (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  simpa only [map_subgroupOf_eq_of_le h.le_offender] using hn

/-- Both bounds required in 13.6.10, for the original action and the
normalizer in the original ambient group. This discharges the outer premise
of `bounds_of_remaining_cases` in the classification assembly. -/
theorem outerSixThree_bounds [FiniteDimensional (ZMod 2) W]
    (h : CubicHypothesis ρ A S C)
    (c : OuterSixThreeCase (offenderRepresentation ρ)) : CubicBounds ρ A := by
  have he : moved ρ A = moved (offenderRepresentation ρ) c.second := by
    change subspaceCommutator ρ ⊤ A =
      subspaceCommutator (offenderRepresentation ρ) ⊤ c.second
    rw [← marked_commutator ρ A h.le_offender ⊤, outerSixThree_internal_eq_second h c]
  refine ⟨?_, ?_⟩
  · rw [he]
    exact c.secondDimension
  · rw [normalizer_eq_top_iff.mpr (outerSixThree_normal h c), index_top]
    decide

section Application
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
local notation "z₀" => A5Module.markedZ s
local notation "v₀" => A5Module.markedV s
local notation "ρ₀" => uvRepresentation z₀ v₀ (A5Module.markedZ_mem_Gv s)
local notation "A₀" => starImage z₀ v₀ (Lv L v₀)

/-- The literal marked Chapter 13 application of the proved outer branch.
The Sylow, quotient, subnormality and commutator premises are passed to
`marked_cubic_hypothesis` without replacing their actual maps or subgroups. -/
theorem marked_outerSixThree_bounds (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    (hc : OuterSixThreeCase (offenderRepresentation ρ₀)) : CubicBounds ρ₀ A₀ :=
  outerSixThree_bounds (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs) hc

end Application
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
