module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarRadicals
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedSource
public import Theory.Representation.BinaryPermutation.Faithful
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedProjectionEquation

/-!
# The actual alternating-six star component on the doubled orbit

The original orbit W lies in Q and in a normal elementary module Y.
Its intersection with KQ puts W in O₂(KQ); C.2.7 puts that core inside Q,
which centralizes W. Thus W lies in the literal canonical star module.
The residual sixteen [W,A], with A contained in K, injects into the B.5
moved section modulo its fixed space, since its intersection with C(A)
is trivial. The full central quotient kernel is retained in this proof.

For an A₆ star component B.5 identifies that quotient with the natural
four-space. The injection is onto, so Q fixes the whole quotient. Its
faithful action makes the component Sylow image have order at most two,
contradicting perfectness. No full-component block identification is used.
The Chapter12 companion supplies all premises on the original chosen orbit.

Source: Aschbacher--Smith, the elimination after 7.7.10, printed p.709,
and C.2.7/B.5.1, printed pp.145--147 and 99--103, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarSix
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {H K Q M : Subgroup G}

/-- The original orbit enters the canonical star module through the reduced
normal module containing it, without a whole-component recognition. -/
theorem orbit_le_star_module
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (Y W : Subgroup G) (hHY : H ≤ normalizer (Y : Set G)) [IsElementaryAbelian 2 Y]
    (hWY : W ≤ Y) (hWQ : W ≤ Q) (hWfix : W ≤ centralizer (Q : Set G)) :
    W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype := by
  let J := K ⊔ Q
  let YJ := Y.subgroupOf J
  let : YJ.Normal := normal_subgroupOf_of_le_normalizer (h.join_le.trans hHY)
  have hYcore : YJ ≤ pCore 2 J := le_sSup
    ⟨inferInstance,(IsElementaryAbelian.isPGroup 2 Y).comap_subtype⟩
  let : (K.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  have hcore := source_joinCore_le_radical (source_join_input h)
  intro w hw
  have hwJ : w ∈ J := mem_sup_right (hWQ hw)
  refine ⟨⟨w,hwJ⟩,?_,rfl⟩
  change (⟨w,hwJ⟩ : J) ∈ omegaOneCenterAmbient (pCore 2 J)
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨hYcore (hWY hw),?_,?_⟩
  · apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian w (hWY hw)
  · intro x hx
    apply Subtype.ext
    exact hWfix hw x (hcore (mem_map_of_mem J.subtype hx))

omit [Finite G] in
/-- The residual four-space projects injectively into the actual central
quotient of the B.5 moved section. -/
theorem star_section_embedding
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J)) :
    ∃ f : Additive X →ₗ[ZMod 2] (s.space.toSubmodule ⧸ s.central.toSubmodule),
      Function.Injective f ∧ ∀ k : K, (k : G) ∈ centralizer (X : Set G) →
        ∀ x, (s.action.comp ((starImage K Q K).subgroupOf J).subtype)
          ((subgroupOfEquivOfLe hCJ).symm (toStarImage K Q k)) (f x) = f x := by
  let U := starV K Q
  let KJ := K.subgroupOf (K ⊔ Q)
  let XJ := ⁅U,KJ⁆
  have hXJ : X ≤ XJ.map (K ⊔ Q : Subgroup G).subtype := by
    rw [hX,map_commutator,map_subgroupOf_eq_of_le (show K ≤ K ⊔ Q from le_sup_left)]
    exact commutator_mono hWX hAK
  let j : X →* XJ := {
    toFun x := ⟨⟨x,(map_subtype_le XJ) (hXJ x.property)⟩,by
      obtain ⟨y,hy,he⟩ := hXJ x.property
      exact (Subtype.ext he : y = ⟨x,_⟩) ▸ hy⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let : IsElementaryAbelian 2 XJ := IsElementaryAbelian.of_injective
    (inclusion (commutator_le_left U KJ)) (inclusion_injective _)
  let q := QuotientGroup.mk' (starKernel K Q)
  have hs : s.space.toSubmodule = subspaceCommutator (starRepresentation K Q) ⊤ (KJ.map q) := by
    rw [s.space_eq]
    change subspaceCommutator ((starRepresentation K Q).comp J.subtype) ⊤
      ((starImage K Q K).subgroupOf J) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    rfl
  let a := (NormalElementaryQuotient.movedEquiv U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) KJ).trans (LinearEquiv.ofEq _ _ hs.symm)
  let f0 : Additive X →ₗ[ZMod 2] s.space.toSubmodule :=
    a.toLinearMap.comp (j.toAdditive.toZModLinearMap 2)
  have hf0 (x : Additive X) : ((f0 x).val.toMul.val.val : G) = x.toMul.val := rfl
  let f := s.central.toSubmodule.mkQ.comp f0
  have hfix (k : K) (x : Additive X) :
      (((s.space.toRepresentation (((subgroupOfEquivOfLe hCJ).symm
        (toStarImage K Q k)) : J) (f0 x)).val).toMul.val.val : G) =
        (k : G) * (x.toMul : G) * (k : G)⁻¹ := by
    have hh := NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (inclusion (show K ≤ K ⊔ Q from le_sup_left) k) (f0 x).val
    exact congrArg Subtype.val hh
  refine ⟨f,?_,?_⟩
  · apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro x hx
    have hc : f0 x ∈ s.central.toSubmodule := (Submodule.Quotient.mk_eq_zero s.central.toSubmodule).mp hx
    rw [s.central_eq] at hc
    have hxC : (x.toMul : G) ∈ centralizer (A : Set G) := by
      intro b hb
      have hh := congrArg (fun v : s.space.toSubmodule => (v.val.toMul.val.val : G))
        (hc ((subgroupOfEquivOfLe hCJ).symm (toStarImage K Q ⟨b,hAK hb⟩)))
      change (((s.space.toRepresentation (((subgroupOfEquivOfLe hCJ).symm
        (toStarImage K Q ⟨b,hAK hb⟩)) : J) (f0 x)).val).toMul.val.val : G) =
        ((f0 x).val.toMul.val.val : G) at hh
      rw [hfix,hf0] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hh := (disjoint_iff.mp hdis).le ⟨x.toMul.property,hxC⟩
    apply Additive.toMul.injective
    exact Subtype.ext (mem_bot.mp hh)
  · intro k hk x
    have he : s.space.toRepresentation (((subgroupOfEquivOfLe hCJ).symm
        (toStarImage K Q k)) : J) (f0 x) = f0 x := by
      apply Subtype.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      exact (hfix k x).trans (by rw [←hk _ x.toMul.property,mul_inv_cancel_right]; rfl)
    exact congrArg s.central.toSubmodule.mkQ he

/-- The half-Sylow index on H restricts to the original full component. -/
theorem component_sylow_index
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 H) (hi : (Q.subgroupOf H).relIndex (P : Subgroup H) ≤ 2) :
    ∃ S : Sylow 2 K, (Q.subgroupOf K).relIndex (S : Subgroup K) ≤ 2 := by
  let C := K.subgroupOf H
  let e : C ≃* K := subgroupOfEquivOfLe h.component.1
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_subnormal C h.component.2.subnormal
  have he : ((Q.subgroupOf H).subgroupOf C).map e.toMonoidHom = Q.subgroupOf K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x,h.component.1 x.property⟩,x.property⟩,hx,rfl⟩
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (Q.subgroupOf K).relIndex ((S : Subgroup C).map e.toMonoidHom) ≤ 2
  rw [←he,relIndex_map_map_of_injective _ _ e.injective,hS,
    ←inf_subgroupOf_right (P : Subgroup H) C,
    relIndex_subgroupOf (show (P : Subgroup H) ⊓ C ≤ C from inf_le_right)]
  exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hi

private theorem actionEquiv_eq_one_of_fixes_surjection
    {D E V W X : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    (a : ActionEquiv ρ σ) (hfaith : Function.Injective σ)
    (j : X → V) (hjs : Function.Surjective j) (k : D)
    (hfix : ∀ x, ρ k (j x) = j x) : a.groupEquiv k = 1 := by
  apply hfaith
  apply LinearMap.ext
  intro v
  obtain ⟨w,hw⟩ := a.linearEquiv.surjective v
  obtain ⟨x,hx⟩ := hjs w
  have hv : a.linearEquiv (j x) = v := (congrArg a.linearEquiv hx).trans hw
  calc
    σ (a.groupEquiv k) v = σ (a.groupEquiv k) (a.linearEquiv (j x)) := congrArg _ hv.symm
    _ = a.linearEquiv (ρ k (j x)) := (a.intertwines k (j x)).symm
    _ = a.linearEquiv (j x) := congrArg a.linearEquiv (hfix x)
    _ = v := hv
    _ = σ 1 v := by rw [map_one]; rfl

/-- An actual A₆ star component cannot contain the original Q-fixed residual
four-space, even without identifying the full component as a block. -/
theorem no_six_star
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    (hcard : Nat.card X = 16) (hQfix : X ≤ centralizer (Q : Set G))
    (S : Sylow 2 K) (hindex : (Q.subgroupOf K).relIndex (S : Subgroup K) ≤ 2)
    (e : starImage K Q K ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  obtain ⟨_,⟨a⟩⟩ := AlternatingSixMovedModel.source_natural _ c
    ((subgroupOfEquivOfLe hCJ).trans e)
  obtain ⟨j,hj,hfix⟩ := star_section_embedding W A X hWX hAK hX hdis hCJ c.sectionData
  have hc : Nat.card (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) = 16 := by
    rw [Nat.card_congr a.linearEquiv.toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num
  let : Finite (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) :=
    Finite.of_equiv (BinaryPermutation.natural (Fin 6)) a.linearEquiv.toEquiv.symm
  have hjs : Function.Surjective j :=
    (hj.bijective_of_nat_card_le (by rw [hc,Nat.card_congr Additive.toMul,hcard])).surjective
  let g := starMovedProjection hCJ a.groupEquiv
  have hgs : Function.Surjective g := starMovedProjection_surjective hCJ a.groupEquiv
  have hfaith : Function.Injective (alternatingNatural 6) := by
    intro x y he
    apply Subtype.ext
    exact BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide) he
  have hQker : Q.subgroupOf K ≤ g.ker := by
    intro k hk
    change starMovedProjection hCJ a.groupEquiv k = 1
    rw [starMovedProjection_apply]
    exact actionEquiv_eq_one_of_fixes_surjection a hfaith j hjs
      ((subgroupOfEquivOfLe hCJ).symm (toStarImage K Q k))
      (hfix k (le_centralizer_iff.mp hQfix hk))
  let P := S.mapSurjective hgs
  have hsmall : Nat.card P ≤ 2 := by
    change Nat.card ((S : Subgroup K).map g) ≤ 2
    rw [←relIndex_ker]
    exact (relIndex_le_of_le_left hQker index_ne_zero_of_finite).trans hindex
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have heven : Even (Nat.card (alternatingGroup (Fin 6))) := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact (not_lt_of_ge hsmall) (perfect_sylow_two_card_gt_two P heven)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarSix
