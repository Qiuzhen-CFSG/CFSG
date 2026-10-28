module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalPointRankOne
public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Theory.GroupTheory.PGroup.NormalPrimeImage
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialDegree
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The six-dimensional section in the normal extraspecial residual branch

Assume the actual K/O₂(K) is extraspecial of order 27 and L₁ is normal in
H. The canonical residual comparison identifies L₁* with the cubic center
of O²(H/O₂(H)). Each elementary subgroup of R₁* acts faithfully on that
residual and fixes its center, so R₁* has two-rank at most one. This removes
the rank premise of NormalPointRankOne and makes the selected actor's
nonzero displacement exactly two.

On any literal U/V₁ conjugation section, the original kernel theorem gives
a faithful star action and the cubic center has zero fixed space. The
small-involution calculation forces binary dimension six and irreducibility
on the actual residual. The original-group application starts with the
literal Heisenberg isomorphism, constructs its section and selected path,
and proves |U| = 128 together with the earlier exact critical geometry.

Normality from 14.7.15(1) remains an explicit premise to be obtained from
the ambient source hypotheses in this task. This module proves the module
step of 14.7.16 under that premise; it does not assert the extraspecial
exclusion 14.7.14 or the residual classification through 14.7.52.

Source: Aschbacher–Smith, 14.7.15–17, printed pp.1047–1048.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem point_star_le_residual : star F (F.Li L 1) ≤ pResidual 2 (HStar F.H) := by
  have hh : (F.Li L 1).subgroupOf F.H ≤ pResidual 2 F.H := by
    rw [← residual_subgroupOf F]
    exact subgroupOf_mono F.H (pointResidual_le F)
  exact (map_mono hh).trans (map_pResidual_le 2 (starMap F))

/-- The normal point cubic is exactly the embedded center of the actual star residual. -/
theorem point_star_eq_residual_center_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F))) :
    star F (F.Li L 1) = (center (pResidual 2 (HStar F.H))).map
      (pResidual 2 (HStar F.H)).subtype := by
  let P := pResidual 2 (HStar F.H)
  let Z := star F (F.Li L 1)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  let : ((F.Li L 1).subgroupOf F.H).Normal := hn
  let : Z.Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZP : Z ≤ P := point_star_le_residual
  have hc : Nat.card (Z.subgroupOf P) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv]
    exact pointResidual_star_card_of_normal h structural hn
  have he : Z.subgroupOf P = center P := eq_of_le_of_card_ge
    ((IsExtraspecial.isPGroup 3 P).normal_le_center_of_card_dvd_prime _ (by rw [hc]))
    (by rw [hc,IsExtraspecial.center_order_p 3 P])
  have hm := congrArg (Subgroup.map P.subtype) he
  rwa [map_subgroupOf_eq_of_le hZP] at hm

private theorem residual_actor_faithful
    {D : Type*} [Group D] [Finite D]
    (hcore : pCore 2 D = ⊥) (hodd : Odd (Nat.card (pResidual 2 D)))
    (A : Subgroup D) (hA : IsPGroup 2 A) :
    Function.Injective ((MulAut.conjNormal : D →* MulAut (pResidual 2 D)).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : (a : D) ∈ centralizer (pResidual 2 D : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact ha
  have hp := Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot hcore hc
  have hdis : Disjoint A (pResidual 2 D) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  have hz := hdis.le_bot ⟨a.property,hp⟩
  exact Subtype.ext (mem_bot.mp hz)

/-- The normal extraspecial branch supplies the rank bound used by the critical geometry. -/
theorem point_core_rank_one_of_normal_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27) :
    primeRank 2 (star F (F.Ri L 1)) ≤ 1 := by
  let R := star F (F.Ri L 1)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  apply (primeRank_le_iff_elementary_card_le R).mpr
  intro E hE
  let := hE
  let A := E.map R.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map R.subtype
  let f : A →* MulAut P := (MulAut.conjNormal : HStar F.H →* MulAut P).comp A.subtype
  have hf : Function.Injective f := residual_actor_faithful
    (pCore_quotient_pCore_eq_bot 2) (by rw [hP]; decide) A (IsElementaryAbelian.isPGroup 2 A)
  have hcenter : ∀ a : A, ∀ z ∈ center P, f a z = z := by
    intro a z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [point_star_eq_residual_center_of_normal h structural hn hex]
      exact mem_map_of_mem P.subtype hz
    have hc := point_core_star_centralizes_of_normal h structural hn
      (map_subtype_le E a.property)
    change (a : HStar F.H) * (z : HStar F.H) * (a : HStar F.H)⁻¹ = z
    rw [←hc z hz',mul_assoc,mul_inv_cancel,mul_one]
  have hb := MulAut.elementary_two_center_preserving_card_le_two hP f hf hcenter
  simpa only [A,card_map_of_injective R.subtype_injective,pow_one] using hb

/-- The selected critical actor has order two, with no separate rank premise. -/
theorem critical_card_two_of_normal_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    Nat.card (star F c.Uα) = 2 :=
  critical_card_two_of_point_core_rank_one h hab structural c hs
    (point_core_rank_one_of_normal_extraspecial_residual h structural hn hex hcard)


variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- Every literal section has a faithful star action and an irreducible residual action of binary degree six. -/
theorem normal_extraspecial_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
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
      rw [←point_star_eq_residual_center_of_normal h structural hn hex,←hgen]
      exact mem_zpowers z
    obtain ⟨z,hzc,rfl⟩ := hzm
    exact hw ⟨z,hzc⟩
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  have hA := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  have hx2 : (x : HStar F.H) ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := x)
    rw [hA] at he
    exact congrArg Subtype.val he
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hfaith := residual_actor_faithful (pCore_quotient_pCore_eq_bot 2)
    (by rw [hP]; decide) A hA2
  have hne : (MulAut.conjNormal (x : HStar F.H) : MulAut P) ≠ 1 := by
    intro he
    exact hx (hfaith (he.trans (map_one _).symm))
  have hcenter : ∀ z ∈ center P, (MulAut.conjNormal (x : HStar F.H) : MulAut P) z = z := by
    intro z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [point_star_eq_residual_center_of_normal h structural hn hex]
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

/-- Apply the extraspecial module and critical geometry to the original flag.
The residual is identified by an actual isomorphism; only point normality
from 14.7.15(1) remains beyond the earlier source inputs. -/
theorem normal_extraspecial_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    Nat.card F.U = 128 ∧
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
        Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
        ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα ∧
        ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 ∧
        Disjoint (F.Vi 1) c.Zα ∧
        ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ = ⊥ ∧
        Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 ∧
        (F.U ⊓ centralizer (c.Uα : Set G)).relIndex (F.U ⊓ c.Qα) = 2 ∧
        (F.U ⊓ centralizer (c.Uα : Set G)).relIndex F.U = 4 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨σ,_,_,hdim,_⟩ := normal_extraspecial_section h hab structural previous hn hex hcard s
  have hUcard := s.card_section
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)),Nat.card_zmod,hdim,
    show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)] at hUcard
  refine ⟨hUcard,?_⟩
  exact normal_point_rank_one_source_reduction h hab structural previous hn
    (point_core_rank_one_of_normal_extraspecial_residual h structural hn hex hcard)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
