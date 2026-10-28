module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalLinearElementaryCenter
public import Theory.GroupTheory.PGroup.SmallFrattiniUniformCenterContainment
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The center in the actual opposite elementary intersection

The singular five- or nine-point Frattini realization puts the entire
center in every elementary subgroup of index at most eight or sixteen.
For the actual opposite intersection U ∩ Uᵍ, the G.2.3 image formula
and the marked PSL₂ quotient actor give precisely this index bound.
The original normal Bender source supplies the field and core equality.

Source: Aschbacher–Smith 14.2.16/F.1.12 and G.2.3, pp.985–986,
262–264 and 332–334. The possible orders 64 and 1024 are retained.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_nonabelian_linear_center_le_opposite
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T.subtype hH.1.2 : Subgroup H) = ⊤)
    (hcore : sourceKernel ((H ⊓ M).subgroupOf H) = pCore 2 H)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : n = 2 ∨ n = 3) (hF : Nat.card F = 2^n)
    (hm : ModelBorelPair ((H ⊓ M).subgroupOf H) K (BenderSuzuki.Converse.PBorel F))
    (g : G) (hg : g ∈ sourceResidual M Mc)
    (hgN : g ∉ normalizer (centralInvolutions T : Set G)) :
    let U := conjugateSpanBy (localModule T M) H
    (center U).map U.subtype ≤ U ⊓ conjugate U g := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h,hphi,hphic,w,hw,hfix,hspan,hzero,hpolar⟩ :=
    source_frattini_seed_orbit hG T hempty hM hu hmany hcard e H hH hne
  obtain ⟨_,⟨b⟩,_⟩ :=
    source_nonabelian_binary_data hG T hempty hM hu hmany hcard e H hH hne
  have hUT := h.U_normal_in_T.1
  have hfr := h.frattini_U_le_point
  have hUQ := h.U_le_core
  have hcomm := h.commutator_U_core_le_point
  obtain ⟨_,helem,_⟩ := ChapterG.Section02.Setup.binary_source_core_intersection_and_index
    h b hUT hfr hUQ hcomm g hg hgN
  obtain ⟨hE,hindex⟩ := ChapterG.Section02.Setup.binary_source_opposite_image
    h b hUT hfr hUQ hcomm g hg hgN
  have hr := hm.linear_actor_two_rank (T.subtype hH.1.2) _ K hgen hcore
    (show 2 ≤ n by omega) hF
  have hEc : Nat.card (((conjugate (D.W g) g).subgroupOf D.H).map
      (QuotientGroup.mk' (pCore 2 D.H))) ≤ 2^n :=
    (primeRank_le_iff_elementary_card_le (H ⧸ pCore 2 H)).mp hr _ hE
  let A := (D.S₂ g).subgroupOf D.U
  let := helem
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.of_injective (p := 2)
      (subgroupOfEquivOfLe (show D.S₂ g ≤ D.U from inf_le_left)).toMonoidHom
      (subgroupOfEquivOfLe (show D.S₂ g ≤ D.U from inf_le_left)).injective
  have hi : A.index ≤ 2^(n+1) := by
    change (D.S₂ g).relIndex D.U ≤ _
    rw [hindex,pow_succ]
    exact (Nat.mul_le_mul_left 2 hEc).trans_eq (Nat.mul_comm _ _)
  let := SmallFrattini.quotientElementary h.U_isPGroup
  let ρ := frattiniRepresentation D h.U_isPGroup
  let B := SmallFrattini.quotientBilinearForm h.U_isPGroup hphic
  let Q := SmallFrattini.quotientQuadraticForm h.U_isPGroup hphic
  have hMN : M ≤ normalizer (D.V : Set G) :=
    (InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1).le
  have hfixed (a : H) (ha : a ∈ (H ⊓ M).subgroupOf H) :
      ρ a (Additive.ofMul w) = Additive.ofMul w := by
    change Additive.ofMul (frattiniActor D a w) = Additive.ofMul w
    exact congrArg Additive.ofMul (hfix a (hMN ha.2))
  have hSM : (T.subtype hH.1.2 : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro t ht
    exact ⟨t.property,hM.1.2 ht⟩
  obtain ⟨f,hf,hpull,hcoord⟩ := hm.linear_quadratic_realization _ K _ hgen hSM n hF
    ρ (Additive.ofMul w) hfixed hspan B
    (SmallFrattini.quotientBilinearForm_isAlt _ _) hpolar
    (fun a x y => SmallFrattini.quotientBilinearForm_invariant
      h.U_isPGroup hphic (closureActor D a) x.toMul y.toMul)
    Q hzero (fun a x => SmallFrattini.quotientQuadraticForm_invariant
      h.U_isPGroup hphic (closureActor D a) x.toMul)
  have hib : (2^n+1 = 5 ∧ A.index ≤ 8) ∨ (2^n+1 = 9 ∧ A.index ≤ 16) := by
    rcases hn with rfl | rfl
    · exact Or.inl ⟨by norm_num,by simpa using hi⟩
    · exact Or.inr ⟨by norm_num,by simpa using hi⟩
  have hcenter : center D.U ≤ A :=
    SmallFrattini.center_le_elementary_of_uniform_quadratic_quotient
      h.U_isPGroup hphic (2^n+1) f hf hpull hcoord A hib
  change (center D.U).map D.U.subtype ≤ D.S₂ g
  rintro x ⟨u,hu,rfl⟩
  exact hcenter hu

/-- The original normal Bender row supplies an actual moving opposite
intersection containing the full center, without an extra index, core,
field or quadratic-realization assumption. -/
theorem source_normal_bender_center_le_opposite
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (f : ℕ) (hm : BenderModel ((H ⊓ M).subgroupOf H) K f) :
    let U := conjugateSpanBy (localModule T M) H
    ∃ g ∈ sourceResidual M Mc, g ∉ normalizer (centralInvolutions T : Set G) ∧
      (center U).map U.subtype ≤ U ⊓ conjugate U g := by
  obtain ⟨hr,F,hfield,hfinite,hchar,hF,hmodel⟩ :=
    source_normal_bender_nonabelian_models hG T hempty hM hu hmany hcard e
      H hH hnH hne K hK hqK hgen f hm
  let := hfield
  let := hfinite
  let := hchar
  obtain ⟨_,hP,hN,_,_,_⟩ :=
    source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
  have hmax : (H ⊓ M).subgroupOf H =
      ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP :=
    ChapterB.minimalParabolicMax_unique _ hP hN (by
      intro x hx
      exact ⟨x.property,hM.1.2 hx⟩)
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hnH) generationParameter_le_one_of_solvable
  have hex : ExchangedModel (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) K f := by
    rw [←hmax]
    exact .inl ⟨F,inferInstance,inferInstance,inferInstance,(by omega),hF,hmodel⟩
  obtain ⟨_,hc,_,_,_⟩ := source_normal_rank_one_kOne _ hP hs K hK hqK hgen hex
  have hcore : sourceKernel ((H ⊓ M).subgroupOf H) = pCore 2 H := by
    rw [hmax]
    exact hc
  obtain ⟨_,_,g,hg,hgN⟩ :=
    source_nonabelian_binary_data hG T hempty hM hu hmany hcard e H hH.1 hne
  refine ⟨g,hg,hgN,?_⟩
  exact source_nonabelian_linear_center_le_opposite hG T hempty hM hu hmany hcard e
    H hH.1 hne K hgen hcore f hr hF hmodel g hg hgN
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
