module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Sylow
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortRoot
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Nonfusion of the original Ree long and short involutions

The native fourth-root involution centralizes an actual perfect PSL₂
subgroup in the linear parabolic. The original compatible parabolic map
transports this embedding into the full ambient centralizer, whose solvable
residual consequently has order divisible by three. The original long-root
centralizer has three-free solvable residual. Isomorphism invariance of
centralizers and their solvable residuals rules out ambient conjugacy.

The marked theorem retains the literal inverse parabolic map and every
nonzero short-root parameter. The existence theorem keeps both comparison
orientations and supplies actual nonconjugate involutions in the original
factors. This does not assert that the two classes exhaust all ambient
involutions, or bound the full short-root centralizer. The simultaneous
native normalizer extension and the full-extension order comparison remain.
Source: Aschbacher–Smith F.4.35 and 5.3.3, printed pp.292,659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds ReeF4.EvenInvolutionGeometry
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem three_dvd_centralizer_residual_of_embedding
    {X : Type*} [Group X] [Group.IsPerfect X]
    (hX : 3 ∣ Nat.card X) (f : X →* G) (hf : Function.Injective f)
    (v : G) (hc : ∀ x, Commute (f x) v) :
    3 ∣ Nat.card (solvableResidual (centralizer ({v} : Set G))) := by
  let C := centralizer ({v} : Set G)
  let g := f.codRestrict C (fun x => mem_centralizer_singleton_iff.mpr (hc x).eq)
  let : Group.IsPerfect g.range := Group.IsPerfect.range g
  have hle : g.range ≤ solvableResidual C := le_solvableResidual_of_isPerfect _
  let k := g.codRestrict (solvableResidual C) (fun x => hle ⟨x,rfl⟩)
  have hg : Function.Injective g := (MonoidHom.injective_codRestrict _ _ _).mpr hf
  have hk : Function.Injective k := (MonoidHom.injective_codRestrict _ _ _).mpr hg
  exact hX.trans (card_dvd_of_injective k hk)

/-- Every marked short-root involution is not conjugate to an original long-root center involution. -/
theorem Preparation.ree_short_root_nonfusion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)
    (t : CoefficientField m) (ht : t ≠ 0) :
    let v := (e.left.symm ⟨shortRootElement m t,
      (unipotent_le_localFactor m .linear).trans (localFactor_le_parabolic m .linear)
        (shortRootElement_mem_unipotent m t)⟩).val
    v ∈ L ∧ orderOf v = 2 ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v} : Set G))) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v := by
  have hm := d.ree_parameter_positive h hp m 0 .linear e.left
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let u : parabolic m .linear := ⟨shortRootElement m t,
    (unipotent_le_localFactor m .linear).trans (localFactor_le_parabolic m .linear)
      (shortRootElement_mem_unipotent m t)⟩
  let a : parabolic m .linear →* G := P.subtype.comp e.left.symm.toMonoidHom
  change a u ∈ L ∧ orderOf (a u) = 2 ∧ _
  have ha : Function.Injective a := P.subtype_injective.comp e.left.symm.injective
  have hu2 : orderOf u = 2 := (Subgroup.orderOf_coe u).symm.trans (shortRootElement_orderOf m ht)
  have hv2 : orderOf (a u) = 2 := (orderOf_injective a ha u).trans hu2
  have hur : u ∈ solvableResidual (parabolic m .linear) := by
    have hu : u.val ∈ localFactor m .linear :=
      unipotent_le_localFactor m .linear (shortRootElement_mem_unipotent m t)
    rw [←parabolic_solvableResidual_map hm .linear] at hu
    obtain ⟨x,hx,hxu⟩ := hu
    exact (Subtype.ext hxu : x = u) ▸ hx
  have hvr : e.left.symm u ∈ solvableResidual P :=
    map_solvableResidual_le e.left.symm.toMonoidHom (mem_map_of_mem _ hur)
  have hvL : a u ∈ L := by
    have hr := d.parabolic_residuals h hH.1.1.2 hp 0
    change (solvableResidual P).map P.subtype = L at hr
    rw [←hr]
    exact mem_map_of_mem P.subtype hvr
  obtain ⟨f,hf,hcomm⟩ := ReeF4.SourceCompletion.short_root_linear_centralizer_embedding hm t
  let : Group.IsPerfect (LinearQuotient m) := linearQuotient_perfect m hm
  have h3 : 3 ∣ Nat.card (LinearQuotient m) :=
    (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := CoefficientField m) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).trans
      (card_subgroup_dvd_card _)
  have hv3 : 3 ∣ Nat.card (solvableResidual (centralizer ({a u} : Set G))) := by
    apply three_dvd_centralizer_residual_of_embedding h3 (a.comp f) (ha.comp hf) (a u)
    intro x
    have hh : Commute (f x) u := Subtype.ext (hcomm x).eq
    exact hh.map a
  refine ⟨hvL,hv2,hv3,?_⟩
  intro z hz hz2 hconj
  have hfree := d.ree_long_centralizer_residual_three_free h hH hp m (Or.inr ⟨e⟩) z hz hz2
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  change (MulAut.conj g) z = a u at hg
  have heq := Nat.card_congr
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) z).solvableResidualEquiv.toEquiv
  rw [hg] at heq
  exact hfree (heq.symm ▸ hv3)

/-- Both orientations give actual nonconjugate ambient involutions in the original two factors. -/
theorem Preparation.ree_involutions_not_fused
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    ∃ z ∈ (center (residual H)).map (residual H).subtype, ∃ v ∈ L,
      orderOf z = 2 ∧ orderOf v = 2 ∧ ¬ IsConj z v := by
  obtain ⟨z,hz,hz2,_⟩ := d.ree_right_center_involution h hH hp m he
  rcases he with he | he
  · exact (d.not_ree_unreversed h hH.1.1.2 hp m he).elim
  obtain ⟨e⟩ := he
  obtain ⟨hv,hv2,_,hnf⟩ := d.ree_short_root_nonfusion h hH hp m e 1 one_ne_zero
  exact ⟨z,hz,_,hv,hz2,hv2,hnf z hz hz2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
