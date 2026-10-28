module
public import CFSG.Quasithin.ChapterD.Section03.SeedCubic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalSuzuki
public import Theory.GroupTheory.ReducedNormal.SubspaceQuotientAction
public import Theory.Representation.BinaryOffender.CubicRatio.MarkedNormalizer
public import CFSG.Quasithin.ChapterD.Section02.QuadraticOrbit

/-!
# The cubic bound and Suzuki separation on the original seed

The original homogeneous seed has an independent Sylow orbit because its
orbit-fixed space vanishes in the central Hall context. In the nonseparated
branch its kernel is exactly O₂(L₀). Passing to the faithful orbit action
therefore makes the normal generalized Fitting subgroup faithful on the
seed; the same elementary cubic actor has no pointwise seed kernel.
The D.2.5/D.2.9 descent gives a cubic bound on its actual stabilizer image,
which embeds in the original seed's full linear normalizer.

The checked Suzuki tensor exclusion now forces separation from the original
Context alone, in either seed orientation. Its crossed-action consequence
applies to [D.fullModule,L], and the literal Hall consumer retains only moved
minimality in this row. The other component rows and moved minimality remain
with qt-d-10-nona5-central-hall-orders; SeedAnalysisAt and the final source
Hall theorem are not asserted here.

Source: Aschbacher--Smith D.3.5--7, 3.2.6 and10.1.1--2,
printed pp.195--199,581 and741--742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

private theorem seedSpace_inf_fixed_eq_bot
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    D.seedSpace ⊓ fixedSpace (ReducedNormal.representation (localJoin T L))
      ((localOrbit T L).subgroupOf (localJoin T L)) = ⊥ := by
  apply bot_unique
  intro v hv
  have hs : (v.toMul.val : G) ∈ D.seed := ⟨_,⟨v.toMul,hv.1,rfl⟩,rfl⟩
  have hc := (ReducedNormal.mem_reduced_fixedSpace_iff (localJoin T L)
    (localOrbit T L) le_sup_left v).mp hv.2
  have hh : (⟨v.toMul.val,
      ((le_componentOrbit D.seed T).trans (le_componentOrbit _ _)) hs⟩ : D.fullModule) ∈
      D.fullCentralizer := hc
  rw [fullCentralizer_eq_bot_of_central_hstar D c] at hh
  have he : (v.toMul.val : G) = 1 := congrArg Subtype.val (mem_bot.mp hh)
  exact Additive.toMul.injective (Subtype.ext (Subtype.ext he))

/-- The original nonseparated seed, before any reselection, has degree above two. -/
theorem original_seed_finrank_gt_two_of_not_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    2 < Module.finrank (ZMod 2) (Additive D.seed) := by
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  obtain ⟨q,_,_,hl,hr,σ,_,hσ⟩ := original_seed_product_action D c (MulEquiv.refl _) ht htn
  have hf := original_seed_product_faithful_of_not_separated D (MulEquiv.refl _) ht hsep q hl hr σ hσ
  by_contra hn
  let τ := σ.comp (MonoidHom.inl (L ⧸ pCore 2 L) (L ⧸ pCore 2 L))
  have he := representation_eq_one_of_isPerfect_of_finrank_le_two τ (Nat.le_of_not_gt hn)
  obtain ⟨g,hg⟩ := exists_ne (1 : L ⧸ pCore 2 L)
  exact hg (congrArg Prod.fst (hf ((he g).trans σ.map_one.symm)))

omit [Finite G] in
private theorem intrinsic_cubic_of_eq
    (J : Subgroup G) (W : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup J)))
    (U : Subgroup J) [U.Normal] [IsElementaryAbelian 2 U]
    [(ReducedNormal.intrinsicSubspace J W).Normal]
    (he : ReducedNormal.intrinsicSubspace J W = U)
    (hb : cubicRatio (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2) :
    cubicRatio (NormalElementaryQuotient.representation (ReducedNormal.intrinsicSubspace J W)
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  subst U
  exact hb

private abbrev seedOrbit := orbitSpan (ReducedNormal.representation (localJoin T L)) ⊤ D.seedSpace
private abbrev seedOrbitAction := subspaceImageRepresentation
  (ReducedNormal.representation (localJoin T L)) (seedOrbit D)
private abbrev seedOrbitSpace := D.seedSpace.comap (seedOrbit D).subtype

/-- The actual Sylow-orbit cubic bound descends to the unchanged nonseparated seed. -/
private theorem original_seed_image_cubic_of_not_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    cubicRatio (subspaceImageRepresentation (seedOrbitAction D) (seedOrbitSpace D)) ≤ 2 := by
  let J := localJoin T L
  let X := (localOrbit T L).subgroupOf J
  let S := (T : Subgroup G).subgroupOf J
  let ρ := ReducedNormal.representation J
  let I := D.seedSpace
  let W := orbitSpan ρ ⊤ I
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ I)
  let σ := subspaceImageRepresentation ρ W
  let U := I.comap W.subtype
  let K := X.map f
  have hi := D.local_internal_module (source_module_nonsolvable_uniqueness D)
  let := hi.normal
  have hf : Function.Surjective f := invariantActionHom_surjective ρ W _
  let : K.Normal := Normal.map inferInstance f hf
  have hgen : X ⊔ (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right) : Subgroup J) = ⊤ := by
    change X ⊔ S = ⊤
    rw [←subgroupOf_sup (show localOrbit T L ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  have hF : generalizedFitting (subspaceActionImage ρ W) = K := by
    rw [show K = restrictedSubgroup ρ W X from invariantActionHom_map ρ W _ X]
    exact hi.faithfulOrbit_generalizedFitting hgen
  have hKI : K ≤ subspaceStabilizer σ U := by
    rw [show K = restrictedSubgroup ρ W X from invariantActionHom_map ρ W _ X]
    exact restrictedSubgroup_le_subspaceStabilizer_comap ρ W I D.homogeneous.invariant
  have hIW : I ≤ W := le_orbitSpan ρ ⊤ I
  let E : U ≃ₗ[ZMod 2] Additive D.seed :=
    (Submodule.comapSubtypeEquivOfLe hIW).trans (ReducedNormal.subspaceEquiv J I)
  have hcorefix : pCore 2 J ≤ (actionHom ρ).ker := by
    rw [ReducedNormal.representation_action_kernel]
    exact le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 J)
  have hk : subspaceKernel σ U K = ⊥ := by
    apply bot_unique
    rintro a ⟨ha,hfix⟩
    obtain ⟨x,hx,rfl⟩ := ha
    let l : localOrbit T L := ⟨x,hx⟩
    have hl : originalSeedAction D l = 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := E.surjective v
      have he := congrArg (fun z : W => (z.val.toMul.val : G)) (hfix w w.property)
      apply Additive.toMul.injective
      apply Subtype.ext
      exact he
    have hlcore : l ∈ pCore 2 (localOrbit T L) := by
      rw [←original_seed_kernel_of_not_separated D c ht htn hsep]
      exact hl
    have hxcoreG : (x : G) ∈ J.pCoreIn 2 :=
      (pCoreIn_mono_of_normalizes (show localOrbit T L ≤ J from le_sup_left)
        (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)))
        ⟨l,hlcore,rfl⟩
    obtain ⟨y,hy,he⟩ := hxcoreG
    have hxcore : x ∈ pCore 2 J := (Subtype.ext he : y = x) ▸ hy
    apply subspaceImageRepresentation_injective ρ W
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact (actionHom_eq_one_iff ρ x).mp (hcorefix hxcore) w.val
  have hind : sSupIndep (subspaceOrbit σ ⊤ U) := by
    apply independent_orbit_faithful_restriction ρ W I (orbitSpan_invariant ρ ⊤ I) hIW
    rw [subspaceOrbit_eq_of_normal_supplement ρ X S
      (show S ⊔ X = ⊤ by rw [sup_comm]; exact hgen) I D.homogeneous.invariant]
    exact D.homogeneous.independent_orbit_of_inf_fixedSpace_eq_bot ρ
      (seedSpace_inf_fixed_eq_bot D c)
  have hdim : 2 < Module.finrank (ZMod 2) U := by
    rw [E.finrank_eq]
    exact original_seed_finrank_gt_two_of_not_separated D c ht htn hsep
  have hbound : cubicRatio σ ≤ 2 := by
    have hUeq : ReducedNormal.intrinsicSubspace J W = D.moduleSubgroup.subgroupOf J := by
      rw [ReducedNormal.intrinsicSubspace_eq,D.local_orbitImage_eq_module]
    let : (ReducedNormal.intrinsicSubspace J W).Normal :=
      ReducedNormal.intrinsicSubspace_normal J W (orbitSpan_invariant ρ ⊤ I)
    apply ReducedNormal.cubicRatio_image_le_of_intrinsic_quotient J W
      (orbitSpan_invariant ρ ⊤ I) 2
    have hb := (cubic_bounds D c).1
    unfold SourceLocalModuleCubicBound at hb
    let := (source_parabolic_module_reduced D).normal
    let := (source_parabolic_module_reduced D).elementary
    exact intrinsic_cubic_of_eq J W _ hUeq hb
  have hseed := ChapterD.seed_cubic_bound_of_independent_orbit σ U hind hdim
    (fun A hA => ChapterD.subspaceKernel_eq_bot_of_faithful_fitting σ K hF
      hi.faithfulOrbit_twoCore_eq_bot U hKI hk A hA) hbound
  exact hseed

private theorem normal_range_comp_of_eq {A C E : Type*} [Group A] [Group C] [Group E]
    (f : A →* C) (g : C →* E) (K : Subgroup C) [K.Normal]
    (he : f.range = K) (hg : Function.Surjective g) : (g.comp f).range.Normal := by
  rw [MonoidHom.range_comp,he]
  exact Normal.map inferInstance g hg

/-- The actual Sylow-orbit cubic bound descends to the unchanged nonseparated seed. -/
theorem original_seed_normalizer_cubic_of_not_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    cubicRatio (normalizerRepresentation (originalSeedAction D)) ≤ 2 := by
  let J := localJoin T L
  let X := (localOrbit T L).subgroupOf J
  let ρ := ReducedNormal.representation J
  let I := D.seedSpace
  let W := seedOrbit D
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ I)
  let σ := seedOrbitAction D
  let U := seedOrbitSpace D
  let K := X.map f
  let := (D.local_internal_module (source_module_nonsolvable_uniqueness D)).normal
  let : K.Normal := Normal.map inferInstance f (invariantActionHom_surjective ρ W _)
  have hKI : K ≤ subspaceStabilizer σ U := by
    rw [show K = restrictedSubgroup ρ W X from invariantActionHom_map ρ W _ X]
    exact restrictedSubgroup_le_subspaceStabilizer_comap ρ W I D.homogeneous.invariant
  let E : U ≃ₗ[ZMod 2] Additive D.seed :=
    (Submodule.comapSubtypeEquivOfLe (le_orbitSpan ρ ⊤ I)).trans (ReducedNormal.subspaceEquiv J I)
  have hseed := original_seed_image_cubic_of_not_separated D c ht htn hsep
  let R := subspaceStabilizer σ U
  let j : localOrbit T L →* J := inclusion (show localOrbit T L ≤ J from le_sup_left)
  let i₀ : localOrbit T L →* R := (f.comp j).codRestrict R
    (fun l => hKI (mem_map_of_mem f (show j l ∈ X from l.property)))
  have hi₀ : i₀.range = K.subgroupOf R := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      exact mem_map_of_mem f (show (⟨l,(show localOrbit T L ≤ J from le_sup_left) l.property⟩ : J) ∈ X from l.property)
    · rintro ⟨x,hx,he⟩
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let i := (subspaceActionHom σ U).comp i₀
  let : i.range.Normal := normal_range_comp_of_eq i₀ (subspaceActionHom σ U)
    (K.subgroupOf R) hi₀ (stabilizerRepresentation σ U).asGroupHom.rangeRestrict_surjective
  let b : Representation.Equiv ((subspaceImageRepresentation σ U).comp i)
      ((originalSeedAction D).comp (MonoidHom.id (localOrbit T L))) :=
    Representation.Equiv.mk E (fun l => by
      apply LinearMap.ext
      intro w
      apply Additive.toMul.injective
      apply Subtype.ext
      rfl)
  exact cubicRatio_normalizer_le_of_marked_normal_range
    (subspaceImageRepresentation σ U) (subspaceImageRepresentation_injective σ U)
    i (originalSeedAction D) (MonoidHom.id _) Function.surjective_id b 2 hseed

/-- The original Suzuki seed is separated without any additional cubic-bound premise. -/
theorem original_seed_separated_of_suzuki
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  by_contra hsep
  exact hsep (original_seed_separated_of_suzuki_cubic D c m hm e ht htn
    (original_seed_normalizer_cubic_of_not_separated D c ht htn hsep))

/-- The full original Suzuki moved factors centralize one another, in either seed orientation. -/
theorem original_suzuki_crossed
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) :=
  full_moved_centralizes_opposite_of_seed_separated D ht htn
    (original_seed_separated_of_suzuki D c m hm e ht htn)

/-- The literal Hall exponent consumer now needs only the remaining moved
minimality premise in the Suzuki branch. Its discharge remains with the
central Hall source assembly owner, qt-d-10-nona5-central-hall-orders. -/
theorem hall_exponent_of_suzuki_and_moved_minimal
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hmin : MovedMinimal D) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  exact hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn hmin
    (original_suzuki_crossed D c m hm e ht htn)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
