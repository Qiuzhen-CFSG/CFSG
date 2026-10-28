module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.PairQuadratic
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.RankEightConfinement

/-!
# No-index quadratic confinement for the original quintic pair

The actual factor permutation preserves every quadratic actor's two
four-dimensional summands. Its elementary actors therefore lie in Jhat by
the D10 involution calculation and self-centralization, without equating
Jhat with the full permutation kernel. The product bounds their rank by two.
The selected critical endpoint is then confined to one literal factor.

Source: Aschbacher--Smith 14.6.12--13, printed pp.1031--1032.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
namespace SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs hp w



open OddNormalizer OddCriticalPair.Selection
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter15.Section03.AbelianAmalgam.GenerationOne

omit hs in
/-- Every quadratic actor fixes the actual ratio-factor labels. This conclusion
uses no index or kernel equality for Jhat. -/
theorem source_quintic_quadratic_le_kernel
    (B : Subgroup (J ⧸ pCore 2 J)) (hq : QuadraticMember a.representation B) :
    B ≤ π.ker := by
  classical
  let : IsElementaryAbelian 2 B := hq.1.2
  obtain ⟨i,j,hij,hall,_,_,_,hspace,hdis⟩ := f.two_factor_moved_decomposition d w.two_factors
  let I := (f.ambientFactor d i).space
  let K := (f.ambientFactor d j).space
  have hsp (g : J ⧸ pCore 2 J) (k : d.Index) :
      (f.ambientFactor d k).space.map (a.representation g) =
        (f.ambientFactor d (π g k)).space := by
    rw [(f.ambientFactor d k).space_eq_support,
      (f.ambientFactor d (π g k)).space_eq_support,moved_map_conjugate,hp]
  have hf (g : J ⧸ pCore 2 J) (hfix : ∀ v ∈ I ⊔ K, a.representation g v = v) : g = 1 := by
    apply source_rankTwo_residual_moved_faithful hG T hempty hM hu hmany hcard e hab J hJ.1 a g
    simpa only [I,K,hspace] using hfix
  have hperm (g : J ⧸ pCore 2 J) :
      (I.map (a.representation g) = I ∧ K.map (a.representation g) = K) ∨
      (I.map (a.representation g) = K ∧ K.map (a.representation g) = I) := by
    rcases hall (π g i) with hi | hi
    · have hj : π g j = j := (hall (π g j)).resolve_left
        (fun hj => hij ((π g).injective (hi.trans hj.symm)))
      exact Or.inl ⟨(hsp g i).trans (congrArg (fun k => (f.ambientFactor d k).space) hi),
        (hsp g j).trans (congrArg (fun k => (f.ambientFactor d k).space) hj)⟩
    · have hj : π g j = i := (hall (π g j)).resolve_right
        (fun hj => hij ((π g).injective (hi.trans hj.symm)))
      exact Or.inr ⟨(hsp g i).trans (congrArg (fun k => (f.ambientFactor d k).space) hi),
        (hsp g j).trans (congrArg (fun k => (f.ambientFactor d k).space) hj)⟩
  have hkeep := quadratic_preserves_pair a.representation I K hf hdis
    (w.dimension i) hperm B hq.2.1 hq.2.2
  have hne : I ≠ K := by
    intro he
    have hdis' : Disjoint I K := hdis
    have hz : I = ⊥ := disjoint_self.mp (he ▸ hdis'.symm)
    have hd := w.dimension i
    change Module.finrank (ZMod 2) I = 4 at hd
    rw [hz,finrank_bot] at hd
    omega
  intro g hg
  change π g = 1
  apply Equiv.ext
  intro k
  rcases hall k with hk | hk
  · rw [hk]
    change π g i = i
    apply (hall (π g i)).resolve_right
    intro hi
    exact hne ((hkeep g hg).1.symm.trans ((hsp g i).trans
      (congrArg (fun k => (f.ambientFactor d k).space) hi)))
  · rw [hk]
    change π g j = j
    apply (hall (π g j)).resolve_left
    intro hj
    exact hne (((hsp g j).trans (congrArg (fun k => (f.ambientFactor d k).space) hj)).symm.trans
      (hkeep g hg).2)

/-- Every elementary subgroup of the actual preserving kernel lies in the
actor join. This does not assert equality of those two ambient subgroups. -/
theorem source_quintic_elementary_kernel_le_Jhat
    (B : Subgroup (J ⧸ pCore 2 J)) [IsElementaryAbelian 2 B] (hB : B ≤ π.ker) :
    B ≤ ChapterD.Jhat a.representation := by
  obtain ⟨i,j,_,_,hjoin,_,hcom,_,_⟩ := f.two_factor_moved_decomposition d w.two_factors
  have hPK := source_solvable_minimal_residual_le_Jhat
    hG T hempty hM hu hmany hcard e hab J hJ hs a
  have hcent : centralizer (ChapterD.Jhat a.representation : Set (J ⧸ pCore 2 J)) ≤
      ChapterD.Jhat a.representation :=
    (centralizer_le hPK).trans
      ((centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)).trans hPK)
  have hn (k : d.Index) : B ≤ normalizer ((f.ambientFactor d k).actor : Set _) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (f.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom = _
    simpa only [show π g = 1 from hB hg,Equiv.Perm.one_apply] using hp g k
  rw [←hjoin] at hcent ⊢
  exact elementary_preserving_le_quintic_join _ _ B (w.dihedral i).some (w.dihedral j).some
    hcom hcent (hn i) (hn j)

/-- The selected-endpoint rank bound follows without an index assumption. -/
theorem source_quintic_quadratic_join_rank
    (B : Subgroup (J ⧸ pCore 2 J)) (hq : QuadraticMember a.representation B) :
    B ≤ ChapterD.Jhat a.representation ∧ rank B ≤ 2 := by
  let : IsElementaryAbelian 2 B := hq.1.2
  have hk := source_quintic_quadratic_le_kernel hG T hempty hM hu hmany hcard e hab
    J hJ a f d π hp w B hq
  have hjoin := source_quintic_elementary_kernel_le_Jhat hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w B hk
  obtain ⟨i,j,_,_,hij,hd,hc,_,_⟩ := f.two_factor_moved_decomposition d w.two_factors
  exact ⟨hjoin,elementary_rank_le_two_of_quintic_join _ _ B
    (w.dihedral i).some (w.dihedral j).some hd hc (hij.symm ▸ hjoin)⟩

/-- In the original selected endpoint, all displacements have rank at most
three. The rank-four summands therefore confine its actor to one factor. -/
theorem source_quintic_selected_confinement :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis
      hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ c : SelectedQuadraticEndpoint h a,
      (∃ k, actorImage J (c.endpoint.conjugate D.UH) ≤ (f.ambientFactor d k).actor) ∧
      rank (actorImage J (c.endpoint.conjugate D.UH)) = 1 ∧
      Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
        (c.endpoint.conjugate D.V₁)).relIndex D.UH) = 1 := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  intro c
  let B := actorImage J (c.endpoint.conjugate D.UH)
  let : IsElementaryAbelian 2 B := c.quadratic.1.2
  obtain ⟨hkeep,hr⟩ := source_quintic_quadratic_join_rank hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w B c.quadratic
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ.1
  have hdisp (t : J ⧸ pCore 2 J) (ht : t ∈ B) :
      Module.finrank (ZMod 2) (LinearMap.range (a.representation t - LinearMap.id)) ≤ 3 :=
    (c.displacement_rank_le hb ht).trans (Nat.add_le_add_right (c.comparison.trans hr) 1)
  obtain ⟨i,j,_,_,hjoin,hd,hc,hspace,hdis⟩ := f.two_factor_moved_decomposition d w.two_factors
  have hsupp (k : d.Index) := (f.ambientFactor d k).space_eq_support
  have hfix : ((f.ambientFactor d i).space ⊔ (f.ambientFactor d j).space) ⊔
      fixedSpace a.representation ⊤ = ⊤ := by
    rw [hspace]
    exact source_rankTwo_span_decomposition hG T hempty hM hu hmany hcard e hab J hJ.1 a
  have hfactor : B ≤ (f.ambientFactor d i).actor ∨ B ≤ (f.ambientFactor d j).actor := by
    apply dihedral_actor_le_factor_of_displacement_le_three a.representation (Or.inr rfl)
      _ _ B (hjoin.symm ▸ hkeep) (w.dihedral i).some (w.dihedral j).some hd hc
    · rwa [←hsupp i,←hsupp j]
    · rwa [←hsupp i,←hsupp j]
    · rw [←hsupp i,w.dimension i]
    · rw [←hsupp j,w.dimension j]
    · exact hdisp
  have hr1 : rank B ≤ 1 := hfactor.elim
    (elementary_rank_le_one_of_dihedral (Or.inr rfl) _ B (w.dihedral i).some)
    (elementary_rank_le_one_of_dihedral (Or.inr rfl) _ B (w.dihedral j).some)
  refine ⟨hfactor.elim (fun h => ⟨i,h⟩) (fun h => ⟨j,h⟩),
    le_antisymm hr1 (c.denominator_rank_pos.trans_le c.comparison),
    le_antisymm (c.comparison.trans hr1) c.denominator_rank_pos⟩

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
