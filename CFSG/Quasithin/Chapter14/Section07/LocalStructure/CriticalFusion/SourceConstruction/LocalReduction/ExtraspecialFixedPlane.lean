module
public import Theory.Representation.CubicSixSpaceNilpotence
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointCoreRoots
/-!
# The original fixed plane and critical commutator

The square root of a selected critical involution lies in the literal Q.
Its star action commutes with the fixed-free cubic and has a two-dimensional
fixed space, equal to its square's displacement. Q centralizes the natural
seed V, so that fixed plane is precisely V/V₁. The known point containment
then lifts the image equality to [U,Uα] = V in the original group.

This proves 14.7.16(3)'s commutator identity in the actual Heisenberg residual
branch, using only the stated earlier source implications. Both the original
section coordinates and star-map representatives are retained.
Source: Aschbacher–Smith, printed pp.1047–1048, refs/quasithin.pdf.
-/
public noncomputable section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem extraspecial_critical_root_fixed_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (a b : F.H) (ha : (a : G) ∈ c.Uα) (hane : starMap F a ≠ 1)
    (hb : (b : G) ∈ Q T L) (hba : (starMap F b)^2 = starMap F a)
    (hfour : (starMap F b)^4 = 1) :
    (ρ b-1).ker = s.imageSpace V ∧ (ρ a-1).range = s.imageSpace V := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨σ,hσ,_,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  obtain ⟨z,hz,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
  have hZ : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hz)
  have hfixed : invariants (σ.comp (zpowers z).subtype) = ⊥ := by
    apply bot_unique
    intro v hv
    exact hfree v (hv ⟨z,mem_zpowers z⟩)
  have hbR : starMap F b ∈ star F (F.Ri L 1) := by
    rw [←(core_product_of_point_normal h hab structural hn).2]
    exact mem_map_of_mem (starMap F) hb
  have hcomm : ∀ z' : zpowers z, Commute (σ z') (σ (starMap F b)) := by
    intro z'
    have hc := point_core_star_centralizes_of_normal h structural hn hbR
    exact (show Commute (z' : HStar F.H) (starMap F b) from
      hc z' (hgen ▸ z'.property)).map σ
  have haQ : a ∉ pCore 2 F.H := fun hh => hane ((QuotientGroup.eq_one_iff _).mpr hh)
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hr : Module.finrank (ZMod 2) (σ (starMap F a)-1).range = 2 := by
    change Module.finrank (ZMod 2) (σ.comp (starMap F) a-1).range = 2
    rw [hσ]
    exact critical_displacement_two_of_normal_card_two h hab structural
      (h.flag_escape F previous) hn s c hs htwo a ha haQ
  have hsq : (σ (starMap F b))^2=σ (starMap F a) := by rw [←map_pow,hba]
  have h4 : (σ (starMap F b))^4=1 := by
    rw [←map_pow,show (starMap F b)^4=1 from hfour,map_one]
  obtain ⟨heq,hk⟩ := Representation.order_four_fixed_plane_of_commuting_three_group
    σ (zpowers z) hZ hfixed hd _ h4 (by rw [hsq]; exact hr) hcomm
  have hsq' : σ (starMap F a)=ρ a := congrArg (fun f => f a) hσ
  have hb' : σ (starMap F b)=ρ b := congrArg (fun f => f b) hσ
  rw [hsq,hsq',hb'] at heq
  rw [hb'] at hk
  have hQV : Q T L ≤ centralizer (V : Set G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
    rw [←h.centralizer_LT structural]
    exact inf_le_right
  have hle : s.imageSpace V ≤ (ρ b-1).ker := by
    intro v hv
    exact sub_eq_zero.mpr (s.fixed_on_imageSpace_of_commutator_le (Q T L) V
      ((commutator_eq_bot_iff_le_centralizer.mpr hQV).le.trans bot_le) b hb v hv)
  have hdim : Module.finrank (ZMod 2) (s.imageSpace V) = 2 := by
    apply s.imageSpace_finrank_of_index V (le_conjugateSpanBy V F.H) 2
    have hc := relIndex_mul_card_of_le (F.le_seed 1)
    have hV : Nat.card V = 8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    have hP : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hV,hP] at hc
    norm_num at hc ⊢
    omega
  have hker := (Submodule.eq_of_le_of_finrank_eq hle (hdim.trans hk.symm)).symm
  exact ⟨hker,heq.symm.trans hker⟩

/-- The full original critical commutator is the natural seed. -/
theorem extraspecial_critical_commutator_eq_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅F.U,c.Uα⁆ = V := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨a,b,ha,hane,_,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful he c hs
  have hr := (extraspecial_critical_root_fixed_plane h hab structural previous he s c hs
    a b ha hane hb hba (hbo ▸ pow_orderOf_eq_one _)).2
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hp : F.Vi 1 ≤ ⁅F.U,c.Uα⁆ := by
    rw [←critical_reverse_intersection_commutator_of_normal_card_two h hab structural
      (h.flag_escape F previous) hn s c hs htwo,commutator_comm]
    exact commutator_mono le_rfl inf_le_left
  have him : s.imageSpace V ≤ s.imageSpace ⁅F.U,c.Uα⁆ := by
    rw [←hr]
    exact s.displacement_range_le_imageSpace_of_commutator_le c.Uα ⁅F.U,c.Uα⁆
      (commutator_comm _ _).le a ha
  have hVC : V ≤ ⁅F.U,c.Uα⁆ := by
    intro v hv
    let vU : F.U := ⟨v,le_conjugateSpanBy V F.H hv⟩
    apply (s.coordinates_mem_imageSpace_iff_of_kernel_le _ hp vU).mp
    exact him ((s.mem_imageSpace_iff V _).mpr ⟨vU,hv,rfl⟩)
  apply (eq_of_le_of_card_ge hVC ?_).symm
  rw [critical_commutator_card_of_normal_card_two h hab structural
    (h.flag_escape F previous) hn s c hs htwo,h.seed_card]
  decide

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
