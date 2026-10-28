module
public import Theory.GroupTheory.NoncentralChiefRefinement.NormalPerfectMovement
public import Theory.GroupTheory.PGroup.ExtraspecialThreeActorGeneration
public import Theory.Representation.ExtraspecialCentralQuotientDegree
public import Theory.Representation.ExtraspecialCenterKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralizerFactors
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryConjugationSection.ActionKernel

/-!
# Chief factors in the original extraspecial centralizer section

A selected reciprocal involution fixes the center of the extraspecial
star residual and inverts its Frattini quotient. Its normal closure
contains that residual; two-perfectness removes the original two-core
when lifting back to H. Thus any H-invariant section centralized by the
reciprocal span is centralized by the actual K.

For an irreducible binary section B/N of C_H(U)/U moved by the point
residual L₁, the point image is the extraspecial center. Detecting this
center makes the whole H/O₂(H)-action faithful. The displacement bound
then forces degree six and irreducibility on the residual. Saturation
makes K centralize both C_H(U)/B and N/U, proving uniqueness among
noncentral factors along that series.

When L₁ moves C_H(U)/U, a maximal-normal-subgroup argument constructs
the actual chief interval, its binary action, order 64, and the exact
action kernel O₂(H). The final application starts with the original
Heisenberg residual isomorphism and requires no chief or module witness.
In the point-central branch, any K-moved chief section now has degree
two or four. Its literal residual action quotient is elementary abelian
of order dividing nine; the center is contained in its kernel.
The point-central branch is retained explicitly: proving K-centrality
there, the rest of the extraspecial exclusion, and the residual
classification through 14.7.52 remain obligations of the local reduction.

Source: Aschbacher–Smith 14.7.20(2), printed p.1049, using 14.7.15–18,
printed pp.1047–1048. Numerators B and denominators N are kept in the
order N ≤ B; relative normality is always inside the original H.
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
private theorem section_commutator_iff_kernel
    {B N A : Subgroup G} (hA : A ≤ F.H)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H B N ρ) :
    ⁅A,B⁆ ≤ N ↔ A.subgroupOf F.H ≤ ρ.ker := by
  constructor
  · intro hc a ha
    exact (s.action_mem_ker_iff a).mpr fun b hb => commutator_le.mp hc a ha b hb
  · intro hk
    exact commutator_le.mpr fun a ha b hb =>
      (s.action_mem_ker_iff ⟨a,hA ha⟩).mp (hk ha) b hb


/-- A selected reciprocal span contains a nontrivial star involution fixing
the extraspecial center. Its actual representative is retained in H. -/
theorem exists_extraspecial_critical_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ∃ a : F.H, (a : G) ∈ c.Uα ∧ starMap F a ≠ 1 ∧ (starMap F a)^2 = 1 ∧
      (MulAut.conjNormal (starMap F a) : MulAut (pResidual 2 (HStar F.H))) ≠ 1 ∧
      ∀ z ∈ center (pResidual 2 (HStar F.H)),
        (MulAut.conjNormal (starMap F a) : MulAut (pResidual 2 (HStar F.H))) z = z := by
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hA := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  have hxne : (x : HStar F.H) ≠ 1 := fun he => hx (Subtype.ext he)
  have hx2 : (x : HStar F.H)^2 = 1 := by
    have he := pow_card_eq_one' (x := x)
    rw [hA] at he
    exact congrArg Subtype.val he
  have hne : (MulAut.conjNormal (x : HStar F.H) : MulAut P) ≠ 1 := by
    intro he
    have hc : (x : HStar F.H) ∈ centralizer (P : Set (HStar F.H)) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer]
      exact he
    have hp := Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) hc
    have hx27 : (x : HStar F.H)^27=1 := by
      have hh := pow_card_eq_one' (x := (⟨x,hp⟩ : P))
      rw [hP] at hh
      exact congrArg Subtype.val hh
    exact hxne (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (by decide : Nat.Coprime 2 27)
      (orderOf_dvd_of_pow_eq_one hx2) (orderOf_dvd_of_pow_eq_one hx27)))
  have hcenter : ∀ z ∈ center P, (MulAut.conjNormal (x : HStar F.H) : MulAut P) z = z := by
    intro z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [point_star_eq_residual_center_of_normal h structural hn hex]
      exact mem_map_of_mem P.subtype hz
    have hc := critical_actor_star_centralizes_of_point_normal h structural hn c x.property
    change (x : HStar F.H)*(z : HStar F.H)*(x : HStar F.H)⁻¹ = z
    rw [←hc z hz',mul_inv_cancel_right]
  obtain ⟨a,ha,he⟩ := x.property
  exact ⟨a,ha,he ▸ hxne,he ▸ hx2,he ▸ hne,he ▸ hcenter⟩

/-- The selected reciprocal span normally generates the whole original
residual. Containment in an H-normal subgroup is checked before quotienting. -/
theorem extraspecial_residual_le_of_critical_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (X : Subgroup G) (hXH : X ≤ F.H) (hX : F.H ≤ normalizer (X : Set G))
    (hcX : c.Uα ≤ X) : K F ≤ X := by
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  let N := X.subgroupOf F.H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hXH).mpr hX
  let M := N.map (starMap F)
  let : M.Normal := (inferInstance : N.Normal).map (starMap F) (QuotientGroup.mk'_surjective _)
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hPM : P ≤ M := IsExtraspecial.le_normal_of_center_fixing_involution
    P hP (starMap F a) ht hne hcenter M (mem_map_of_mem _ (hcX ha))
  have hres : (pResidual 2 F.H).map (starMap F) = P :=
    map_pResidual_of_surjective 2 (starMap F) (QuotientGroup.mk'_surjective _)
  have hsup : pResidual 2 F.H ≤ N ⊔ pCore 2 F.H := by
    have he := (le_comap_map (starMap F) (pResidual 2 F.H)).trans
      (comap_mono (hres.le.trans hPM))
    simpa only [M,comap_map_eq,starMap,QuotientGroup.ker_mk'] using he
  have hn : pResidual 2 F.H ≤ N := le_of_isPPerfect_of_le_sup_of_normalizes
    (pResidual 2 F.H) N (pCore 2 F.H) (isPPerfect_pResidual 2)
    pCore_isPGroup le_normalizer_of_normal hsup
  intro k hk
  have hk' : (⟨k,(map_subtype_le _ : K F ≤ F.H) hk⟩ : F.H) ∈ (K F).subgroupOf F.H := hk
  exact hn ((residual_subgroupOf F).le hk')

/-- The actual chief action descends faithfully to H/O₂(H) and has degree
six when its point cubic acts nontrivially. Neither faithfulness nor degree
is assumed in the section hypotheses. -/
theorem extraspecial_point_noncentral_chief
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype) := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk : pCore 2 F.H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let σ := quotientOfLEKer ρ (pCore 2 F.H) hk
  have hσ : σ.comp (starMap F) = ρ := rfl
  let : σ.IsIrreducible := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hZm : ¬ (center P).map P.subtype ≤ σ.ker := by
    intro hz
    apply hm
    apply (section_commutator_iff_kernel ((F.Li_le L 1).trans inf_le_right) s).mpr
    intro a ha
    have he : starMap F a ∈ (center P).map P.subtype := by
      rw [←point_star_eq_residual_center_of_normal h structural hn hex]
      exact mem_map_of_mem _ ha
    exact hz he
  obtain ⟨hf,hfix⟩ := faithful_of_extraspecial_center_not_le_kernel σ P
    (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)) hZm
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hsmall : fixedCodim σ (zpowers (starMap F a)) ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact extraspecial_centralizer_section_displacement
      h hab structural previous hex hcard hexp c hs hB hUN s a ha
  exact ⟨σ,hσ,hf,ExtraspecialBinarySix.six_and_irreducible_of_small_involution
    σ hf P hP hfix (starMap F a) ht hne hcenter hsmall⟩


/-- Every H-invariant section centralized by the reciprocal span is
centralized by the original residual K. The two-core is removed using
K = O²(K), so no star-triviality premise is silently substituted. -/
theorem extraspecial_residual_commutator_of_critical_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (X Y : Subgroup G) (hX : F.H ≤ normalizer (X : Set G))
    (hY : F.H ≤ normalizer (Y : Set G)) (hc : ⁅X,c.Uα⁆ ≤ Y) :
    ⁅X,K F⁆ ≤ Y := by
  let D := commutatorPreimage F.H X Y
  have hn : F.H ≤ normalizer (D : Set G) :=
    commutatorPreimage_normalized F.H X Y F.H hY F.H.le_normalizer hX hY
  have ha : c.Uα ≤ D := le_commutatorPreimage
    ((critical_le_Q h structural c).trans (Q_le_H F)) (by rw [commutator_comm]; exact hc)
  have hK := extraspecial_residual_le_of_critical_normal
    h hab structural previous hex hcard hexp c hs D (commutatorPreimage_le _ _ _) hn ha
  rw [commutator_comm]
  exact (commutator_mono hK le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hY)

omit [Finite G] in
private theorem section_kernel_normalized
    {B N : Subgroup G} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H B N ρ) : F.H ≤ normalizer (N : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx n hn
  have hnB := s.kernel_le hn
  apply (s.coordinates_eq_one_iff ⟨x*n*x⁻¹,
    (mem_normalizer_iff.mp (s.normalized hx) n).mp hnB⟩).mp
  apply Multiplicative.toAdd.injective
  rw [s.equivariant ⟨x,hx⟩ ⟨n,hnB⟩,(s.coordinates_eq_one_iff _).mpr hn]
  exact map_zero _

/-- A point-noncentral chief factor exhausts the reciprocal displacement.
The full original residual centralizes the centralizer series above and
below that factor. Its full star action and exact quotient kernel remain
part of the conclusion. -/
theorem extraspecial_point_noncentral_chief_localization
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N) :
    (∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype)) ∧
      ⁅centralizer (F.U : Set G),K F⁆ ≤ B ∧ ⁅N,K F⁆ ≤ F.U := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hf,hd,hi⟩ := extraspecial_point_noncentral_chief
    h hab structural previous hex hcard hexp hB hUN s hm
  refine ⟨⟨σ,hσ,hf,hd,hi⟩,?_⟩
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hExp : Monoid.exponent P = 3 := by
    rw [←Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F),hexp]
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,hane,ht,_,_⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hr : 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) := by
    by_contra hh
    have hsmall : fixedCodim σ (zpowers (starMap F a)) ≤ 1 := by
      rw [fixedCodim_zpowers_eq_displacement_rank]
      change Module.finrank (ZMod 2) (σ.comp (starMap F) a - 1).range ≤ 1
      rw [hσ]
      omega
    exact hane (ExtraspecialBinarySix.rank_one_actor_trivial σ hf P hP hExp
      (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
      (starMap F a) ht hsmall)
  obtain ⟨_,_,hupper,hlower⟩ := extraspecial_centralizer_section_saturation
    h hab structural previous hex hcard hexp c hs hB hUN s a ha hr
  have hU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  exact ⟨extraspecial_residual_commutator_of_critical_commutator
    h hab structural previous hex hcard hexp c hs _ _
      (hU.trans (normalizer_le_normalizer_centralizer _)) s.normalized hupper,
    extraspecial_residual_commutator_of_critical_commutator
      h hab structural previous hex hcard hexp c hs _ _ (section_kernel_normalized s) hU hlower⟩


/-- Once a point-noncentral chief factor occurs, no residual-noncentral
section can lie above or below it in a chief series. This is the uniqueness
step on the literal numerators and denominators. -/
theorem extraspecial_noncentral_sections_not_separated
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N)
    {B' N' : Subgroup G} (hB' : B' ≤ centralizer (F.U : Set G))
    (hUN' : F.U ≤ N') (hm' : ¬ ⁅B',K F⁆ ≤ N') :
    ¬ B ≤ N' ∧ ¬ B' ≤ N := by
  obtain ⟨_,hupper,hlower⟩ := extraspecial_point_noncentral_chief_localization
    h hab structural previous hex hcard hexp hB hUN s hm
  exact ⟨fun hBN' => hm' ((commutator_mono hB' le_rfl).trans (hupper.trans hBN')),
    fun hB'N => hm' ((commutator_mono hB'N le_rfl).trans (hlower.trans hUN'))⟩

/-- Original Heisenberg-residual application. Every literal irreducible
centralizer section either centralizes the point residual, or has the
faithful six-dimensional full star action and is the only possible
residual-noncentral factor along its series. The first branch is retained
explicitly; it is not silently identified with K-centrality. -/
theorem extraspecial_chief_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      (∀ X : Subgroup G, X ≤ F.H → F.H ≤ normalizer (X : Set G) →
        c.Uα ≤ X → K F ≤ X) ∧
      ∀ (B N : Subgroup G), B ≤ centralizer (F.U : Set G) → F.U ≤ N →
      ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
        (ρ : Representation (ZMod 2) F.H W),
      ρ.IsIrreducible → BinaryConjugationSection F.H B N ρ →
      ⁅F.Li L 1,B⁆ ≤ N ∨
        ((∃ σ : Representation (ZMod 2) (HStar F.H) W,
          σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
          Module.finrank (ZMod 2) W = 6 ∧
          IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype)) ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B ∧ ⁅N,K F⁆ ≤ F.U) := by
  classical
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,hplace,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  refine ⟨c,hs,hplace,fun X hXH hX hcX =>
    extraspecial_residual_le_of_critical_normal h hab structural previous hex hcard hexp c hs X hXH hX hcX,?_⟩
  intro B N hB hUN W aW mW ρ hi s
  let := hi
  by_cases hm : ⁅F.Li L 1,B⁆ ≤ N
  · exact Or.inl hm
  · exact Or.inr (extraspecial_point_noncentral_chief_localization
      h hab structural previous hex hcard hexp hB hUN s hm)


open NoncentralChiefRefinement in
/-- If the point residual moves the full centralizer modulo U, a genuine
chief interval has order 64 and exactly O₂(H) as its full action kernel.
Its endpoints are normal in the original H and bound all K-movement. -/
theorem extraspecial_exists_point_moved_chief
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hm : ¬ ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U) :
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
      Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
      ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
      ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hUH := sU.section_le
  have hCH : centralizer (F.U : Set G) ≤ F.H :=
    (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU).trans
      (pCoreIn_le 2 F.H)
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hUn := sU.normalized
  let Z : NormalNode F.H := ⟨F.U.subgroupOf F.H,
    (normal_subgroupOf_iff_le_normalizer hUH).mpr hUn⟩
  let Q : NormalNode F.H := ⟨(centralizer (F.U : Set G)).subgroupOf F.H,
    (normal_subgroupOf_iff_le_normalizer hCH).mpr
      (hUn.trans (normalizer_le_normalizer_centralizer _))⟩
  let R : NormalNode F.H := ⟨(F.Li L 1).subgroupOf F.H,
    pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp⟩
  have hQ : IsPGroup 2 Q.val :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU)).comap_subtype
  have hR : IsPPerfect 2 R.val := by
    have hp : IsPPerfect 2 (F.Li L 1) := by
      change IsPPerfect 2 ((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype)
      exact isPPerfect_embedded_pResidual 2 _
    let e := (subgroupOfEquivOfLe hLH).symm
    exact hp.of_surjective e.toMonoidHom e.surjective
  have hm' : ¬ ⁅Q.val,R.val⁆ ≤ Z.val := by
    intro hc
    apply hm
    have hh := map_mono (f := F.H.subtype) hc
    change (⁅(centralizer (F.U : Set G)).subgroupOf F.H,
      (F.Li L 1).subgroupOf F.H⁆).map F.H.subtype ≤
        (F.U.subgroupOf F.H).map F.H.subtype at hh
    rwa [map_commutator,map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le hUH] at hh
  obtain ⟨N,B,hZN,hNB,hBQ,hmove⟩ := exists_moved_chief_of_normal_twoPerfect
    Z Q R (subgroupOf_mono F.H F.U.le_centralizer) hQ hR hm'
  have hUN : F.U ≤ N.val.map F.H.subtype := by
    have hh := map_mono (f := F.H.subtype) hZN
    change (F.U.subgroupOf F.H).map F.H.subtype ≤ _ at hh
    rwa [map_subgroupOf_eq_of_le hUH] at hh
  have hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G) := by
    have hh := map_mono (f := F.H.subtype) hBQ
    change _ ≤ ((centralizer (F.U : Set G)).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hCH] at hh
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hQ.to_le hBQ)
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hpoint : ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype := by
    intro hc
    apply hmove
    intro x hx
    have hh := mem_map_of_mem F.H.subtype hx
    change (x : G) ∈ (⁅B.val,(F.Li L 1).subgroupOf F.H⁆).map F.H.subtype at hh
    rw [map_commutator,map_subgroupOf_eq_of_le hLH,commutator_comm] at hh
    exact (mem_map_iff_mem F.H.subtype_injective).mp (hc hh)
  obtain ⟨⟨σ,hσ,hf,hd,_⟩,hupper,hlower⟩ := extraspecial_point_noncentral_chief_localization
    h hab structural previous hex hcard hexp hBC hUN s hpoint
  have hk : ρ.ker = pCore 2 F.H := by
    change (binarySectionRepresentation N B).ker = pCore 2 F.H
    rw [←hσ,MonoidHom.ker_comp_of_injective _ _ hf,starMap,QuotientGroup.ker_mk']
  have hact : (sectionAction N B).ker = ρ.ker := by
    ext a
    change sectionAction N B a = 1 ↔ ρ a = 1
    constructor
    · intro ha
      ext w
      exact congrArg (fun f : MulAut (Section N B) => f w.toMul) ha
    · intro ha
      ext w
      exact congrArg Additive.toMul
        (congrArg (fun f : Module.End (ZMod 2) (Additive (Section N B)) => f (Additive.ofMul w)) ha)
  refine ⟨N,B,hNB,hUN,hBC,hpoint,?_,hact.trans hk,hupper,hlower⟩
  change Nat.card (Additive (Section N B)) = 64
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
  norm_num

open NoncentralChiefRefinement in
/-- The actual Heisenberg residual supplies the chief interval and all its
coordinates whenever the point residual moves C_H(U)/U. The remaining
point-central branch is stated on that same original quotient. -/
theorem extraspecial_centralizer_chief_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∨
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
        Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
        ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U := by
  classical
  by_cases hm : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U
  · exact Or.inl hm
  obtain ⟨e⟩ := he
  apply Or.inr
  exact extraspecial_exists_point_moved_chief h hab structural previous
    ((HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))) hm

/-- A point-central chief section moved by K has degree two or four.
Its literal star action kills the extraspecial center, and the actual residual
action quotient is elementary abelian with order dividing nine. -/
theorem extraspecial_point_central_chief_degree
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧
      (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ≤ σ.ker ∧
      ¬ pResidual 2 (HStar F.H) ≤ σ.ker ∧
      IsElementaryAbelian 3 ((pResidual 2 (HStar F.H)) ⧸
        (σ.comp (pResidual 2 (HStar F.H)).subtype).ker) ∧
      Nat.card ((pResidual 2 (HStar F.H)) ⧸
        (σ.comp (pResidual 2 (HStar F.H)).subtype).ker) ∣ 9 ∧
      (Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 4) := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk : pCore 2 F.H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let σ := quotientOfLEKer ρ (pCore 2 F.H) hk
  have hσ : σ.comp (starMap F) = ρ := rfl
  let : σ.IsIrreducible := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hZ : (center P).map P.subtype ≤ σ.ker := by
    rw [←point_star_eq_residual_center_of_normal h structural hn hex]
    rintro _ ⟨a,ha,rfl⟩
    change a ∈ ρ.ker
    apply (s.action_mem_ker_iff a).mpr
    intro b hb
    exact commutator_le.mp (by rw [commutator_comm]; exact hp) (a : G) ha b hb
  have hmove : ¬ P ≤ σ.ker := by
    intro hPker
    apply hm
    rw [commutator_comm]
    apply commutator_le.mpr
    intro k hk b hb
    let a : F.H := ⟨k,(map_subtype_le _ : K F ≤ F.H) hk⟩
    have hkres : a ∈ pResidual 2 F.H := by
      rw [←residual_subgroupOf F]
      exact hk
    have haker : a ∈ ρ.ker := hPker
      (map_pResidual_le 2 (starMap F) (mem_map_of_mem (starMap F) hkres))
    exact (s.action_mem_ker_iff a).mp haker b hb
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  obtain ⟨hel,hquot⟩ := extraspecial_center_kernel_quotient σ P hP hZ
  refine ⟨σ,hσ,hZ,hmove,hel,hquot,?_⟩
  exact extraspecial_center_kernel_small_involution_degree σ P hP hZ hmove
    (starMap F a) ht hne hcenter
    (extraspecial_centralizer_section_displacement h hab structural previous
      hex hcard hexp c hs hB hUN s a ha)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
