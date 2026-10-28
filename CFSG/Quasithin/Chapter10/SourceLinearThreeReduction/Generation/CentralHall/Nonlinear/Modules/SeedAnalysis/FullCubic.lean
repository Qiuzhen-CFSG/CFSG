module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalBounded

/-!
# The full-module cubic bound on the original moved factor

Separation makes the two moved factors complementary inside the original
full module, without full/local equality. The actual quotient M/C_M(V_M)
permutes these factors, so the permuted-pair cubic estimate applies. The
stabilizer of the moved factor is exactly the component stabilizer: an
exchanger would equate the two disjoint nonzero factors. Its literal action
image therefore inherits the bound on the unchanged moved subgroup.

The component quotient is faithful on a quotient of W and is perfect and
nontrivial, which forces dim W > 2. Thus neither a degree premise nor a
local/full equality premise is needed here. Source separation remains with
qt-d-10-nona5-central-hall-orders; the natural-actor consumer is in
SeedAnalysis.NaturalDegree.

Source: Aschbacher--Smith D.2.5, D.2.9, D.3.21(3), and 3.2.6,
printed pp.179--182,205--206,581.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
abbrev fullCarrier := D.fullModule.subgroupOf D.maximalLocal
local instance : (fullCarrier D).Normal := (source_full_module_reduced D).normal
local instance : IsElementaryAbelian 2 (fullCarrier D) := (source_full_module_reduced D).elementary
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance : FiniteDimensional (ZMod 2) (Additive (fullCarrier D)) := Module.Finite.of_finite
abbrev fullActor := D.maximalLocal ⧸ centralizer (fullCarrier D : Set D.maximalLocal)
@[expose] def fullAction : Representation (ZMod 2) (fullActor D) (Additive (fullCarrier D)) :=
  representation (fullCarrier D) (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
@[expose] def fullMovedSpace : Submodule (ZMod 2) (Additive (fullCarrier D)) :=
  subgroupSpace (fullCarrier D) ((⁅D.fullModule,L⁆).subgroupOf D.maximalLocal)
private theorem moved_le_maximal : ⁅D.fullModule,L⁆ ≤ D.maximalLocal :=
  (moved_le_fullModule D).trans (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer)

def fullMovedSpaceEquiv : Additive (⁅D.fullModule,L⁆ : Subgroup G) ≃ₗ[ZMod 2] fullMovedSpace D := by
  let W := ⁅D.fullModule,L⁆
  let e := (subgroupOfEquivOfLe (moved_le_maximal D)).symm
  let : IsElementaryAbelian 2 (W.subgroupOf D.maximalLocal) :=
    IsElementaryAbelian.subgroupOf (moved_le_maximal D)
  let E : Additive W ≃ₗ[ZMod 2] Additive (W.subgroupOf D.maximalLocal) :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  exact E.trans (subgroupSpaceEquiv (fullCarrier D) _ (fun _ hx => moved_le_fullModule D hx))

theorem fullMovedSpace_permuted_pair {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    ∃ t : fullActor D, IsCompl (fullMovedSpace D) ((fullMovedSpace D).map (fullAction D t)) ∧
      ∀ a : fullActor D, (fullMovedSpace D).map (fullAction D a) = fullMovedSpace D ∨
        (fullMovedSpace D).map (fullAction D a) = (fullMovedSpace D).map (fullAction D t) := by
  let M := D.maximalLocal
  let U := fullCarrier D
  let W := ⁅D.fullModule,L⁆
  let tM : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  have hW := moved_le_fullModule D
  have hWM := moved_le_maximal D
  have hp := fullModule_pair_at D ht htn
  have hc := moved_pair_disjoint_of_seed_separated D c ht htn hsep
  have hmap (g : M) :
      (W.subgroupOf M).map (MulAut.conj g).toMonoidHom =
        (W.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf M := by
    ext x
    constructor
    · rintro ⟨a,ha,he⟩
      exact ⟨a,ha,congrArg Subtype.val he⟩
    · rintro ⟨a,ha,he⟩
      exact ⟨⟨a,hWM ha⟩,ha,Subtype.ext he⟩
  have hspace (g : M) : (fullMovedSpace D).map (fullAction D (q g)) =
      subgroupSpace U ((W.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf M) := by
    rw [fullMovedSpace,fullAction,subgroupSpace_map_conj,hmap]
  refine ⟨q tM,?_,?_⟩
  · rw [hspace]
    constructor
    · apply subgroupSpace_disjoint
      apply disjoint_iff.mpr
      apply bot_unique
      intro w hw
      exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hc.eq_bot.le hw)))
    · apply codisjoint_iff.mpr
      have hWt : W.map (MulAut.conj t).toMonoidHom ≤ D.fullModule := by
        rw [hp]
        exact le_sup_right
      change subgroupSpace U (W.subgroupOf M) ⊔
        subgroupSpace U ((W.map (MulAut.conj t).toMonoidHom).subgroupOf M) = ⊤
      have hWU : W.subgroupOf M ≤ U := fun _ hx => hW hx
      have hWtU : (W.map (MulAut.conj t).toMonoidHom).subgroupOf M ≤ U := fun _ hx => hWt hx
      rw [←subgroupSpace_sup U hWU hWtU,
        ←subgroupOf_sup hWM (hWt.trans (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer)),
        ←hp]
      ext v
      exact iff_of_true v.toMul.property Submodule.mem_top
  · intro a
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (U : Set M)) a
    rw [hspace g]
    have hV (s : M) : D.fullModule.map (MulAut.conj (s : G)).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule s.property)
    have hh := source_nonnormal_maximal_pair D c.nonnormal ht htn g g.property
    rcases hh with he | he
    · left
      have hw : W.map (MulAut.conj (g : G)).toMonoidHom = W := by
        change (⁅D.fullModule,L⁆ : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = _
        rw [map_commutator,hV,he]
      rw [hw]
      rfl
    · right
      rw [hspace tM]
      have hw : W.map (MulAut.conj (g : G)).toMonoidHom =
          W.map (MulAut.conj (tM : G)).toMonoidHom := by
        change (⁅D.fullModule,L⁆ : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom =
          (⁅D.fullModule,L⁆ : Subgroup G).map (MulAut.conj (tM : G)).toMonoidHom
        rw [map_commutator,map_commutator,hV,hV,he]
      rw [hw]

theorem full_moved_finrank_gt_two
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    2 < Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := by
  let W := ⁅D.fullModule,L⁆
  let Q := Additive (W ⧸ (sourceMovedFixed D).subgroupOf W)
  let : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  let : FiniteDimensional (ZMod 2) Q := Module.Finite.of_finite
  let ρ := movedQuotientAction D c.nonnormal
  let := D.quasisimple
  let := component_simple D c.nonnormal
  let : Group.IsPerfect (L ⧸ pCore 2 L) := inferInstance
  have hQ : 2 < Module.finrank (ZMod 2) Q := by
    by_contra hn
    have htr := representation_eq_one_of_isPerfect_of_finrank_le_two ρ (Nat.le_of_not_gt hn)
    obtain ⟨g,hg⟩ := exists_ne (1 : L ⧸ pCore 2 L)
    exact hg (movedQuotientAction_faithful D c.nonnormal ((htr g).trans ρ.map_one.symm))
  let f : Additive W →ₗ[ZMod 2] Q :=
    (QuotientGroup.mk' ((sourceMovedFixed D).subgroupOf W)).toAdditive.toZModLinearMap 2
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective ((sourceMovedFixed D).subgroupOf W) v.toMul
    exact ⟨Additive.ofMul w,congrArg Additive.ofMul hw⟩
  exact hQ.trans_le (LinearMap.finrank_le_finrank_of_surjective hf)

theorem fullMovedSpace_cubic_bound {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    :
    cubicRatio (subspaceImageRepresentation (fullAction D) (fullMovedSpace D)) ≤ 2 := by
  obtain ⟨s,hpair,hperm⟩ := fullMovedSpace_permuted_pair D c ht htn hsep
  have hb : cubicRatio (fullAction D) ≤ 2 := (cubic_bounds D c).2
  have hdim : 2 < Module.finrank (ZMod 2) (fullMovedSpace D) := by
    rw [←(fullMovedSpaceEquiv D).finrank_eq]
    exact full_moved_finrank_gt_two D c
  exact cubicRatio_le_two_of_permuted_pair (fullAction D)
    (representation_injective (fullCarrier D) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
    (fullMovedSpace D) s hpair hperm hdim hb

theorem fullMovedSpace_stabilizer_iff (g : D.maximalLocal) :
    QuotientGroup.mk' (centralizer (fullCarrier D : Set D.maximalLocal)) g ∈
      subspaceStabilizer (fullAction D) (fullMovedSpace D) ↔
      (g : G) ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let M := D.maximalLocal
  let U := fullCarrier D
  let W := ⁅D.fullModule,L⁆
  have hWU : W.subgroupOf M ≤ U := fun _ hx => moved_le_fullModule D hx
  have he := stabilizer_comap U (QuotientGroup.mk' (centralizer (U : Set M)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) ((W.subgroupOf M).subgroupOf U)
  rw [map_subgroupOf_eq_of_le hWU,←subgroupOf_normalizer_eq (moved_le_maximal D)] at he
  exact (congrArg (fun J : Subgroup M => g ∈ J) he).to_iff

theorem full_moved_normalizer_eq_component_stabilizer
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) =
      D.maximalLocal ⊓ normalizer (L : Set G) := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg.1,?_⟩
    rcases source_nonnormal_maximal_pair D c.nonnormal ht htn g hg.1 with he | he
    · exact mem_normalizer_iff_map_conj_eq.mpr he
    · have hv : D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
        mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hg.1)
      have hw : (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ :=
        mem_normalizer_iff_map_conj_eq.mp hg.2
      have htV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
        mem_normalizer_iff_map_conj_eq.mp
        (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))
      have hwe : (⁅D.fullModule,L⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom = ⁅D.fullModule,L⁆ := by
        rw [map_commutator,htV]
        rwa [map_commutator,hv,he] at hw
      have hd := moved_pair_disjoint_of_seed_separated D c ht htn hsep
      rw [hwe] at hd
      exact (source_full_moved_ne_bot D (disjoint_self.mp hd)).elim
  · intro g hg
    refine ⟨hg.1,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp hg.2,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hg.1)]

theorem fullMovedSpaceEquiv_apply_coe
    (w : Additive (⁅D.fullModule,L⁆ : Subgroup G)) :
    (((fullMovedSpaceEquiv D w).val.toMul : D.maximalLocal) : G) = (w.toMul : G) := by
  let : IsElementaryAbelian 2 ((⁅D.fullModule,L⁆).subgroupOf D.maximalLocal) :=
    IsElementaryAbelian.subgroupOf (moved_le_maximal D)
  exact congrArg D.maximalLocal.subtype
    (subgroupSpaceEquiv_apply_coe (fullCarrier D)
      ((⁅D.fullModule,L⁆).subgroupOf D.maximalLocal)
      (fun _ hx => moved_le_fullModule D hx)
      (Additive.ofMul ((subgroupOfEquivOfLe (moved_le_maximal D)).symm w.toMul)))

theorem movedStabilizerAction_cubic_bound
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    :
    cubicRatio (imageRepresentation (movedStabilizerAction D)) ≤ 2 := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let M := D.maximalLocal
  let U := fullCarrier D
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  have hn := full_moved_normalizer_eq_component_stabilizer D c ht htn hsep
  let f : N →* subspaceStabilizer (fullAction D) (fullMovedSpace D) :=
    ((q.comp (inclusion (show N ≤ M from inf_le_left))).codRestrict _
      (fun g => (fullMovedSpace_stabilizer_iff D ⟨g,g.property.1⟩).mpr
        ((hn.ge g.property).2)))
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (centralizer (U : Set M)) a.val
    have hgW : (g : G) ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
      apply (fullMovedSpace_stabilizer_iff D g).mp
      rw [hg]
      exact a.property
    refine ⟨⟨g,hn.le ⟨g.property,hgW⟩⟩,Subtype.ext hg⟩
  let E := fullMovedSpaceEquiv D
  have hE (g : N) (w : Additive (⁅D.fullModule,L⁆ : Subgroup G)) :
      E (movedStabilizerAction D g w) =
        stabilizerRepresentation (fullAction D) (fullMovedSpace D) (f g) (E w) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [fullMovedSpaceEquiv_apply_coe]
    change (g : G) * (w.toMul : G) * (g : G)⁻¹ =
      (((fullAction D (q ⟨g,g.property.1⟩) (E w).val).toMul : M) : G)
    have hh := congrArg M.subtype
      (representation_apply U q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        ⟨g,g.property.1⟩ (E w).val)
    change _ = (g : G) * (((E w).val.toMul : M) : G) * (g : G)⁻¹ at hh
    rw [fullMovedSpaceEquiv_apply_coe] at hh
    exact hh.symm
  have hEs (g : N) (v : fullMovedSpace D) :
      movedStabilizerAction D g (E.symm v) =
        E.symm (stabilizerRepresentation (fullAction D) (fullMovedSpace D) (f g) v) := by
    apply E.injective
    rw [E.apply_symm_apply,hE,E.apply_symm_apply]
  let ψ := equivariantActionImageEquiv (movedStabilizerAction D)
    (stabilizerRepresentation (fullAction D) (fullMovedSpace D)) f E.symm hf hEs
  apply cubicRatio_le_nat_of_equivariant
    (subspaceImageRepresentation (fullAction D) (fullMovedSpace D))
    (imageRepresentation (movedStabilizerAction D)) ψ.toMonoidHom ψ.injective E.symm _ 2
    (fullMovedSpace_cubic_bound D c ht htn hsep)
  intro a v
  change E.symm (a.val.val v) = E.symm (a.val.val (E (E.symm v)))
  rw [E.apply_symm_apply]

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
