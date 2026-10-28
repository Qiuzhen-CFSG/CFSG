module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergThreeCore

public import Theory.Representation.ExtraspecialBinarySixCubicRank
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.GroupTheory.PResidual.AutomorphismCentralizer

/-!
# Nonsolvability of the original point normalizer

Retain the proper local Heisenberg residual inside the full point quotient.
Its literal center is the original point cubic and its centralizer is that
cubic. The critical involution argument therefore gives a faithful binary
six-space without identifying the local residual with the full residual.

Under original solvability the full residual has order 648 and centralizes
the point cubic. Its faithful image in GL₃(4) forces three-rank at least
three, contradicting strong quasithinness. This excludes solvability of the
full original point normalizer; it does not assert nonsolvability of all
members of the local family.

Source: Aschbacher–Smith 14.7.15(3), 14.7.16(1), printed pp.1047–1048,
refs/quasithin.pdf, used in the solvable reduction 14.7.27–29.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Theory.GroupTheory
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem heisenberg_actor_faithful
    {D : Type*} [Group D] [Finite D]
    (R : Subgroup D) [R.Normal] (hodd : Odd (Nat.card R))
    (hcR : centralizer (R : Set D) ≤ R)
    (A : Subgroup D) (hA : IsPGroup 2 A) :
    Function.Injective ((MulAut.conjNormal : D →* MulAut (R)).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : (a : D) ∈ centralizer (R : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact ha
  have hp := hcR hc
  have hdis : Disjoint A (R) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  have hz := hdis.le_bot ⟨a.property,hp⟩
  exact Subtype.ext (mem_bot.mp hz)

private theorem point_core_rank_one_of_normal_heisenberg_subgroup
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (P : Subgroup (HStar F.H)) [P.Normal] (e : P ≃* HeisenbergPrime 3)
    (hZ : star F (F.Li L 1) = (center P).map P.subtype)
    (hcP : centralizer (P : Set (HStar F.H)) ≤ P) :
    primeRank 2 (star F (F.Ri L 1)) ≤ 1 := by
  let R := star F (F.Ri L 1)
  let : IsExtraspecial 3 P :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hP : Nat.card P = 27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  apply (primeRank_le_iff_elementary_card_le R).mpr
  intro E hE
  let := hE
  let A := E.map R.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map R.subtype
  let f : A →* MulAut P := (MulAut.conjNormal : HStar F.H →* MulAut P).comp A.subtype
  have hf : Function.Injective f := heisenberg_actor_faithful P (by rw [hP]; decide) hcP A (IsElementaryAbelian.isPGroup 2 A)
  have hcenter : ∀ a : A, ∀ z ∈ center P, f a z = z := by
    intro a z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [hZ]
      exact mem_map_of_mem P.subtype hz
    have hc := point_core_star_centralizes_of_normal h structural hn
      (map_subtype_le E a.property)
    change (a : HStar F.H) * (z : HStar F.H) * (a : HStar F.H)⁻¹ = z
    rw [←hc z hz',mul_assoc,mul_inv_cancel,mul_one]
  have hb := MulAut.elementary_two_center_preserving_card_le_two hP f hf hcenter
  simpa only [A,card_map_of_injective R.subtype_injective,pow_one] using hb

variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- A normal, self-centralizing Heisenberg subgroup with the original point
center makes every literal section a faithful star action of binary degree
six, irreducible on that Heisenberg subgroup. -/
theorem normal_heisenberg_subgroup_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (P : Subgroup (HStar F.H)) [P.Normal] (e : P ≃* HeisenbergPrime 3)
    (hZ : star F (F.Li L 1) = (center P).map P.subtype)
    (hcP : centralizer (P : Set (HStar F.H)) ≤ P)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp P.subtype) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let : IsExtraspecial 3 P :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hP : Nat.card P = 27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hescape := h.flag_escape F previous
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) x
    have hk : a ∈ ρ.ker := by
      rw [←hσ]
      exact hx
    rw [section_action_kernel_eq_core_of_escape h structural hescape s] at hk
    exact (QuotientGroup.eq_one_iff _).mpr hk
  have hfix : invariants ((σ.comp P.subtype).comp (center P).subtype) = ⊥ := by
    obtain ⟨z,hz,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
    rw [Submodule.eq_bot_iff]
    intro w hw
    apply hfree w
    have hzm : z ∈ (center P).map P.subtype := by
      rw [←hZ,←hgen]
      exact mem_zpowers z
    obtain ⟨z,hzc,rfl⟩ := hzm
    exact hw ⟨z,hzc⟩
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  have hA := critical_card_two_of_point_core_rank_one h hab structural c hs
    (point_core_rank_one_of_normal_heisenberg_subgroup h structural hn P e hZ hcP)
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  have hx2 : (x : HStar F.H) ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := x)
    rw [hA] at he
    exact congrArg Subtype.val he
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hfaith := heisenberg_actor_faithful P (by rw [hP]; decide) hcP A hA2
  have hne : (MulAut.conjNormal (x : HStar F.H) : MulAut P) ≠ 1 := by
    intro he
    exact hx (hfaith (he.trans (map_one _).symm))
  have hcenter : ∀ z ∈ center P, (MulAut.conjNormal (x : HStar F.H) : MulAut P) z = z := by
    intro z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [hZ]
      exact mem_map_of_mem P.subtype hz
    have hc := critical_actor_star_centralizes_of_point_normal h structural hn c x.property
    change (x : HStar F.H) * (z : HStar F.H) * (x : HStar F.H)⁻¹ = z
    rw [←hc z hz',mul_assoc,mul_inv_cancel,mul_one]
  obtain ⟨a,haA,he⟩ := x.property
  have haQ : a ∉ pCore 2 F.H := by
    intro hq
    apply hx
    apply Subtype.ext
    rw [←he]
    exact (QuotientGroup.eq_one_iff _).mpr hq
  have hdisp := critical_displacement_two_of_normal_card_two
    h hab structural hescape hn s c hs hA a haA haQ
  have hsmall : fixedCodim σ (zpowers (x : HStar F.H)) ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank,←he]
    change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range ≤ 2
    rw [hσ,hdisp]
  exact ⟨σ,hσ,hf,ExtraspecialBinarySix.six_and_irreducible_of_small_involution σ hf P hP hfix x hx2 hne hcenter hsmall⟩

/-- The full original point normalizer is nonsolvable. The proper local
Heisenberg subgroup is retained literally throughout the argument. -/
theorem original_point_not_solvable
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ¬ Group.IsSolvable F.H := by
  intro hs
  obtain ⟨I,hIH,hI,hRn,he,hcore,hlt,hZ,hC,⟨eQ⟩⟩ :=
    original_solvable_full_residual_sl23 d h hab structural previous faithful earlier hs
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  have hn := original_solvable_point_normal h hab structural previous faithful hs
  have hcR : centralizer (R : Set (HStar F.H)) ≤ R := by
    rw [hC,hZ]
    exact map_subtype_le _
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨σ,hσ,hf,hd,hirr⟩ := normal_heisenberg_subgroup_section
    h hab structural previous hn R he.some hZ hcR s
  let K := pResidual 2 (HStar F.H)
  let A := R.subgroupOf K
  let eA : A ≃* R := subgroupOfEquivOfLe hlt.le
  let : IsExtraspecial 3 A :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv (eA.trans he.some).symm
  have hA : Nat.card A = 27 :=
    (Nat.card_congr (eA.trans he.some).toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hQ : Nat.card (K ⧸ A) = 24 :=
    (Nat.card_congr eQ.toEquiv).trans GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hK : Nat.card K = 648 := by
    rw [card_eq_card_quotient_mul_card_subgroup A,hQ,hA]
  let Z := star F (F.Li L 1)
  let : ((F.Li L 1).subgroupOf F.H).Normal := hn
  let : Z.Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZcard : Nat.card Z = 3 := pointResidual_star_card_of_normal h structural hn
  let : IsCyclic Z := isCyclic_of_prime_card hZcard
  have hAut : IsPGroup 2 (MulAut Z) := IsPGroup.of_card (n := 1) (by
    rw [IsCyclic.card_mulAut,hZcard]; decide)
  have hcentral : K ≤ centralizer (Z : Set (HStar F.H)) := by
    have hh := pResidual_le_ker_of_isPGroup 2
      (MulAut.conjNormal : HStar F.H →* MulAut Z) hAut
    rwa [MulAut.conjNormal_ker_eq_centralizer] at hh
  have hcenter : (center A).map A.subtype ≤ center K := by
    rintro a ⟨x,hx,rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hxR : eA x ∈ center R := by
      apply mem_center_iff.mpr
      intro r
      obtain ⟨w,rfl⟩ := eA.surjective r
      exact congrArg eA (mem_center_iff.mp hx w)
    have hxZ : (((x : A) : K) : HStar F.H) ∈ Z := by
      rw [show Z = (center R).map R.subtype from hZ]
      exact mem_map_of_mem R.subtype hxR
    exact (hcentral y.property _ hxZ).symm
  have hthree := Representation.ExtraspecialBinarySixCubicRank.three_le_primeRank
    (σ.comp K.subtype) A (hf.comp K.subtype_injective) hA hd hcenter hK
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hh := F.card 1 (by decide)
    rw [hz,card_bot] at hh
    norm_num at hh
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hrD : primeRank 3 (HStar F.H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 F.H) pCore_isPGroup).trans
      ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 3 (by decide) (by decide))
  have hrK : primeRank 3 K ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 K.subtype K.subtype_injective).trans hrD
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
