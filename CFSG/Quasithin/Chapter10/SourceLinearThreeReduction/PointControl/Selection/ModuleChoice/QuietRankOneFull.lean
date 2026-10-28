module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietRankOneActors
public import CFSG.Quasithin.ChapterD.Section03.StableNonFFConstituent

/-!
# Recognizing the original full quiet rank-one tensor

Every starred actor preserves the original seed and is faithful on it.
The seed's non-FF stabilizer image and the common-actor pair budget therefore
make the seed exhaust the full module. The proof uses its literal inclusion
into the original full action quotient, retaining that quotient's entire
kernel. The actual natural tensor coordinates then transport to the full
module with both original factor inclusions and exact two-core kernel.

ModuleChoice.Source applies this recognition to its point-selection
alternative. The ambient tensor exclusion and the distinct even-degree
positive fixed-layer assertion remain separate source obligations.
Source: Aschbacher--Smith D.3.21 and 3.2.6(1), pp.205--207,581;
original 10.1.1 preliminaries, p.741, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Representation.QuadraticFourGroup.TensorClassification
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 CentralHall.Nonlinear.Modules
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

/-- The original quiet natural tensor seed exhausts the original full module.
The same starred actor is faithful on every translate and preserves each;
two distinct translates would force an FF offender on the tensor seed. -/
theorem quiet_rankOne_seed_eq_full
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht)
    (hlocal : D.moduleSubgroup = D.seed) : D.seed = D.fullModule := by
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hSF : D.seed ≤ D.fullModule :=
    (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)
  have hFM : D.fullModule ≤ M := D.fullModule_le_orbit.trans R.le_normalizer
  let fG : D.seed →* U := {
    toFun v := ⟨⟨v,hFM (hSF v.property)⟩,hSF v.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let f : Additive D.seed →ₗ[ZMod 2] Additive U := fG.toAdditive.toZModLinearMap 2
  have hf : Function.Injective f := by
    intro v w he
    exact Additive.toMul.injective (Subtype.ext
      (congrArg (fun z : Additive U => ((z.toMul : M) : G)) he))
  have hact (l : R) (v : Additive D.seed) :
      f (originalSeedAction D l v) = ρ (q (inclusion R.le_normalizer l)) (f v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg (fun z : M => (z : G))
      (ChapterB.InternalThompsonAction.action_apply U (inclusion R.le_normalizer l) (f v))).symm
  let p : R →* X := (q.comp (inclusion R.le_normalizer)).codRestrict X
    (fun l => mem_map_of_mem q l.property)
  have hp : Function.Surjective p := by
    intro a
    obtain ⟨l,hl,he⟩ := a.property
    exact ⟨⟨l,hl⟩,Subtype.ext he⟩
  let I : Subrepresentation (ρ.comp X.subtype) := {
    toSubmodule := f.range
    apply_mem_toSubmodule a v hv := by
      obtain ⟨w,rfl⟩ := hv
      obtain ⟨l,rfl⟩ := hp a
      exact ⟨originalSeedAction D l w,hact l w⟩ }
  let E : Additive D.seed ≃ₗ[ZMod 2] I.toSubmodule := LinearEquiv.ofInjective f hf
  let b : (originalSeedAction D).Equiv (I.toRepresentation.comp p) :=
    .mk E (fun l => by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact hact l v)
  have hI : I.toRepresentation.IsIrreducible := by
    let := quiet_seed_action_irreducible D hmany hJ
    have hh := (RepEquiv.ofRepresentationEquiv b.symm).irreducible_of_euqiv inferInstance
    exact (irreducible_comp_surjective_iff p hp I.toRepresentation).mp hh
  have hXI : X ≤ subspaceStabilizer ρ I.toSubmodule := by
    apply le_subspaceStabilizer
    intro a ha v hv
    exact I.apply_mem_toSubmodule ⟨a,ha⟩ hv
  let Z := subspaceStabilizer ρ I.toSubmodule
  let k₀ : R →* Z := (q.comp (inclusion R.le_normalizer)).codRestrict Z
    (fun l => hXI (mem_map_of_mem q l.property))
  have hk₀ : k₀.range = X.subgroupOf Z := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      exact mem_map_of_mem q l.property
    · rintro ⟨l,hl,he⟩
      exact ⟨⟨l,hl⟩,Subtype.ext he⟩
  let k := (subspaceActionHom ρ I.toSubmodule).comp k₀
  have hkrange : k.range = (X.subgroupOf Z).map (subspaceActionHom ρ I.toSubmodule) := by
    rw [MonoidHom.range_comp,hk₀]
  let : k.range.Normal := by
    rw [hkrange]
    exact Normal.map inferInstance _ (stabilizerRepresentation ρ I.toSubmodule).asGroupHom.rangeRestrict_surjective
  let c : Representation.Equiv ((subspaceImageRepresentation ρ I.toSubmodule).comp k)
      ((originalSeedAction D).comp (MonoidHom.id R)) := .mk E.symm (by
    intro l
    apply LinearMap.ext
    intro v
    apply E.injective
    change E (E.symm ((subspaceImageRepresentation ρ I.toSubmodule) (k l) v)) =
      E (originalSeedAction D l (E.symm v))
    rw [E.apply_symm_apply]
    apply Subtype.ext
    exact ((hact l (E.symm v)).trans (congrArg (ρ (q (inclusion R.le_normalizer l)))
      (congrArg Subtype.val (E.apply_symm_apply v)))).symm)
  have hnff : ¬ IsFFModule (subspaceImageRepresentation ρ I.toSubmodule) :=
    not_isFFModule_of_marked_normal_range _ (subspaceImageRepresentation_injective ρ I.toSubmodule)
      k (originalSeedAction D) (MonoidHom.id R) Function.surjective_id c
      (quiet_rankOne_seed_normalizer_not_ff D hnon hn hm)
  have hs : ∀ A ∈ ChapterD.QhatStar ρ, A ≤ subspaceStabilizer ρ I.toSubmodule := by
    intro A hA
    apply le_subspaceStabilizer
    intro a ha v hv
    obtain ⟨m,rfl⟩ := (QuotientGroup.mk'_surjective (centralizer (U : Set M))) a
    obtain ⟨w,rfl⟩ := hv
    have hnrm := (quiet_rankOne_starred_preserves_seed D hmany hmin hnon hJ n hn e hm hlocal
      A hA m ha).2
    have hmem : (m:G)*(w.toMul:G)*(m:G)⁻¹ ∈ D.seed :=
      (mem_normalizer_iff.mp hnrm _).mp w.toMul.property
    refine ⟨Additive.ofMul ⟨_,hmem⟩,?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg (fun z : M => (z : G))
      (ChapterB.InternalThompsonAction.action_apply U m (f w))).symm
  have hfaith : ∀ A ∈ ChapterD.QhatStar ρ, subspaceKernel ρ I.toSubmodule A = ⊥ := by
    intro A hA
    apply bot_unique
    rintro a ⟨ha,hfix⟩
    obtain ⟨m,rfl⟩ := (QuotientGroup.mk'_surjective (centralizer (U : Set M))) a
    apply mem_bot.mpr
    apply quiet_rankOne_starred_seed_faithful D hmany hmin hnon hJ n hn e hm A hA m ha
    intro v hv
    have he := congrArg (fun z : Additive U => ((z.toMul : M) : G))
      (hfix (f (Additive.ofMul ⟨v,hv⟩)) ⟨_,rfl⟩)
    have he' := congrArg (fun z : M => (z : G))
      (ChapterB.InternalThompsonAction.action_apply U m (f (Additive.ofMul ⟨v,hv⟩)))
    have heq : (m:G)*v*(m:G)⁻¹ = v := he'.symm.trans he
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have htop := ChapterD.stable_nonFF_constituent_eq_top ρ (quiet_full_action_irreducible D hmany hmin hJ)
    X I hI (source_full_module_cubic_bound_of_many D hmany) hnff hs hfaith
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp htop
  apply le_antisymm hSF
  intro v hv
  obtain ⟨w,hw⟩ := hsurj (Additive.ofMul ⟨⟨v,hFM hv⟩,hv⟩)
  have he := congrArg (fun z : Additive U => ((z.toMul : M) : G)) hw
  have he' : (w.toMul : G) = v := he
  exact he' ▸ w.toMul.property

local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

/-- Literal tensor coordinates for the full module under both original
component inclusions, retaining the exact two-core kernel. -/
@[expose] def QuietRankOneFullTensorMarking {n : ℕ}
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) : Prop :=
    ∃ q : localOrbit T L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) ×
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
      ∃ α : MulAut (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)),
        Nonempty (Representation.Equiv
          ((originalFullAction D).comp (inclusion (localOrbit T L).le_normalizer))
          ((restrictScalars (k := ZMod 2)
            (externalTensor
              ((SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n))).comp α.symm.toMonoidHom)
              (SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n))))).comp q))

/-- Actual natural tensor coordinates on the original full module, with
both original factors and the complete two-core quotient unchanged. -/
theorem quiet_rankOne_full_tensor_coordinates
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht)
    (hlocal : D.moduleSubgroup = D.seed) :
    QuietRankOneFullTensorMarking D e ht := by
  have hfull := quiet_rankOne_seed_eq_full D hmany hmin hnon hJ n hn e hm hlocal
  obtain ⟨q,hq,hk,hl,hr,σ,_,_,hσ,_,α,⟨b⟩⟩ := hm
  let a : D.seed ≃* D.fullModule := MulEquiv.subgroupCongr hfull
  let E : Additive D.seed ≃ₗ[ZMod 2] Additive D.fullModule :=
    a.toAdditive.toLinearEquiv (fun c v => ZMod.map_smul a.toAdditive.toAddMonoidHom c v)
  refine ⟨q,hq,hk,hl,hr,α,⟨Representation.Equiv.mk (E.symm.trans b.toLinearEquiv) ?_⟩⟩
  intro l
  apply LinearMap.ext
  intro v
  have htransport : E.symm (originalFullAction D (inclusion (localOrbit T L).le_normalizer l) v) =
      originalSeedAction D l (E.symm v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  change b (E.symm (originalFullAction D (inclusion (localOrbit T L).le_normalizer l) v)) = _
  rw [htransport]
  have hσl := LinearMap.congr_fun (DFunLike.congr_fun hσ l) (E.symm v)
  change σ (q l) (E.symm v) = originalSeedAction D l (E.symm v) at hσl
  rw [←hσl]
  exact LinearMap.congr_fun (b.isIntertwining' (q l)) (E.symm v)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
