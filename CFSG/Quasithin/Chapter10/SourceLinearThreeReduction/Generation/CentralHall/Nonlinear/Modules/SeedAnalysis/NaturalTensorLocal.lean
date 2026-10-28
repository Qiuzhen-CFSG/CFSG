module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorLargeActors
public import CFSG.Quasithin.ChapterD.Section03.NonFFSeedOrbit
public import Theory.Representation.BinaryOffender.NormalizerNonFF

/-!
# The original local tensor module equals its seed

The original faithful local orbit image has generalized Fitting subgroup
L₀/O₂(L₀), acting faithfully on the nonseparated seed. The seed's independent
Sylow orbit, original cubic bound and tensor-normalizer non-FF estimate
therefore force that orbit to have one member. Thus V_T = V° on the literal
ambient subgroups, with no assumption about the larger M-orbit V_M.

The consumer `NaturalTensorGeneration` uses this equality to apply B.2.4
and the TI-module form of E.6.1 directly to V_T.
Source: Aschbacher--Smith D.3.5--6, 3.2.6(1), and 9.2.1--4,
printed pp.195--197,581,730, refs/quasithin.pdf.
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

private theorem normal_range_comp_of_eq {A C E : Type*} [Group A] [Group C] [Group E]
    (f : A →* C) (g : C →* E) (K : Subgroup C) [K.Normal]
    (he : f.range = K) (hg : Function.Surjective g) : (g.comp f).range.Normal := by
  rw [MonoidHom.range_comp,he]
  exact Normal.map inferInstance g hg

private theorem seed_image_not_ff
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ¬ IsFFModule (subspaceImageRepresentation (seedOrbitAction D) (seedOrbitSpace D)) := by
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
  have hseed : ¬ IsFFModule (normalizerRepresentation (originalSeedAction D)) := by
    rintro ⟨A,hA,hbound⟩
    have hh := (original_even_seed_normalizer_bounds D c n hn e ht htn hsep A hA).2.1
    omega
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
  exact not_isFFModule_of_marked_normal_range
    (subspaceImageRepresentation σ U) (subspaceImageRepresentation_injective σ U)
    i (originalSeedAction D) (MonoidHom.id _) Function.surjective_id b hseed

/-- The original local module is exactly the original tensor seed.
This does not identify it with the full maximal-normalizer orbit. -/
theorem original_even_module_eq_seed
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    D.moduleSubgroup = D.seed := by
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
  have hs := ChapterD.seed_invariant_of_nonFF_independent_orbit σ K hF hi.faithfulOrbit_twoCore_eq_bot
    U hKI hk hind hdim hbound (seed_image_not_ff D c n hn e ht htn hsep)
  have hstableI : (⊤ : Subgroup J) ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer ρ I
    intro g _ v hv
    have hh := (hs (mem_top (f g)) ⟨v,hIW hv⟩).2 hv
    exact hh
  have he : W = I := orbitSpan_eq_self ρ hstableI
  calc
    D.moduleSubgroup = ReducedNormal.subspaceImage J W := D.local_orbitImage_eq_module.symm
    _ = ReducedNormal.subspaceImage J I := congrArg (ReducedNormal.subspaceImage J) he
    _ = D.seed := rfl

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
