module
public import Theory.GroupTheory.GeneralizedFitting.JointCoreDetection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Survival
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.Complete

/-!
# The exceptional odd-pair contradiction

The action kernel on K is central modulo O₂(K). Passing to the faithful action
image modulo its two-core retains that bound, including the odd part of the
kernel. Since K is perfect and KT/K is a two-group, joint core detection shows
that [F,V] survives outside the action-image two-core. A chief flag therefore
contains a section moved by both the conjugated F*(K/O₂(K)) lift and V.
The seed displacement bound makes the latter action a transvection. The full
G.6.4 classification and the exceptional model comparison yield False.

All actions and quotient maps are the literal maps of the original geometry.
The earlier relative-component premise is supplied by
qt-d-1222-natural-relative-components; the local quotient and marked flag by
qt-d-1222-natural-flag-cartan; the surviving exceptional cases, including
triangle elimination, by qt-d-1222-shadow-component-triangle. Those statements
remain explicit as required by this paragraph's contract. No chief section,
survival premise or transvection-exclusion callback remains. The final owner
qt-d-1222-natural-closure-amalgam discharges OddPair existence and the earlier
premises when assembling K=L₁.

Source: Aschbacher--Smith, 11.5.8, printed p.784, using G.6.4, pp.345--346.
Left conjugation by g corresponds to the source right exponent g inverse.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)

private theorem component_injective : Function.Injective (Models.componentEmbedding E g) :=
  (Models.actorEquiv E g).injective.comp (inclusion_injective le_sup_left)

private theorem component_two_quotient (h : LocalInputs E) :
    let := Models.componentEmbedding_normal E g h
    IsPGroup 2 ((actor E g) ⧸ (Models.componentEmbedding E g).range) := by
  let := Models.componentEmbedding_normal E g h
  let S := ((T : Subgroup G).subgroupOf (KT E)).map (Models.actorEquiv E g).toMonoidHom
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype.map _
  have hn : E.K.subgroupOf (KT E) ⊔ (T : Subgroup G).subgroupOf (KT E) = ⊤ := by
    apply map_injective (f := (KT E).subtype) (KT E).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show E.K ≤ KT E from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ KT E from le_sup_right), ← MonoidHom.range_eq_map, range_subtype]
    rfl
  apply isPGroup_quotient_of_sup_eq_top _ S hS
  change (Models.componentEmbedding E g).range ⊔
    (((T : Subgroup G).subgroupOf (KT E)).map (Models.actorEquiv E g).toMonoidHom) = ⊤
  rw [Models.componentEmbedding, MonoidHom.range_comp, inclusion_range,
    ← Subgroup.map_sup, hn, map_top_of_surjective _ (Models.actorEquiv E g).surjective]

private theorem fittingLift_component_map :
    ((generalizedFitting (E.K ⧸ pCore 2 E.K)).comap
      (QuotientGroup.mk' (pCore 2 E.K))).map (Models.componentEmbedding E g) =
        markedFitting E g := by
  ext a
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_map_of_mem E.K.subtype hk)
  · rintro ⟨x,⟨k,hk,rfl⟩,he⟩
    exact ⟨k,hk,Subtype.ext he⟩

variable [IsElementaryAbelian 2 (localClosure E)]

private theorem action_component_kernel_bound (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    [IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁)] :
    (Models.componentAction E g (action E g)).ker ≤
      (center (E.K ⧸ pCore 2 E.K)).comap (QuotientGroup.mk' (pCore 2 E.K)) := by
  intro k hk
  have hm : Models.componentEmbedding E g k ∈ (action E g).ker := by
    exact LinearMap.ext ((actionHom_eq_one_iff (action E g) _).mp hk)
  rw [action_kernel] at hm
  have hc : (k : G) ∈ centralizer (localClosure E : Set G) := by
    change (MulAut.conj g) (k : G) ∈ centralizer
      ((localClosure E).map (MulAut.conj g).toMonoidHom : Set G) at hm
    rw [show ((localClosure E).map (MulAut.conj g).toMonoidHom : Set G) =
        (MulAut.conj g) '' (localClosure E : Set G) from rfl,
      ← map_centralizer_equiv (localClosure E : Set G) (MulAut.conj g), mem_map_equiv] at hm
    simpa only [MulEquiv.symm_apply_apply] using hm
  obtain ⟨y,hy,he⟩ := K_centralizer_le_two_center E h hK hlt ⟨k.property,hc⟩
  exact (show y = k from Subtype.ext he) ▸ hy

/-- Simultaneous detection uses the original seed outside the actor two-core. -/
theorem fitting_seed_commutator_not_le_twoCore (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    [IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁)] (p : OddPair E g) :
    ¬ ⁅markedFitting E g, (seed E g p).range⁆ ≤
      (pCore 2 (actionImage (action E g))).comap (actionHom (action E g)) := by
  let ρ := action E g
  let J := actionImage ρ ⧸ pCore 2 (actionImage ρ)
  let f : actor E g →* J := (QuotientGroup.mk' (pCore 2 (actionImage ρ))).comp (actionHom ρ)
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp ρ.asGroupHom.rangeRestrict_surjective
  have hkill : pCore 2 (actor E g) ≤ f.ker := by
    intro a ha
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (show (pCore 2 (actor E g)).map (actionHom ρ) ≤ pCore 2 (actionImage ρ) from
      le_sSup ⟨Normal.map inferInstance _ ρ.asGroupHom.rangeRestrict_surjective,
        pCore_isPGroup.map _⟩) (mem_map_of_mem _ ha)
  let u := Models.componentAction E g ρ
  have huk : u.rangeRestrict.ker ≤
      (center (E.K ⧸ pCore 2 E.K)).comap (QuotientGroup.mk' (pCore 2 E.K)) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact action_component_kernel_bound E g h hK hlt
  have huCore : pCore 2 E.K ≤ (pCore 2 u.range).comap u.rangeRestrict :=
    map_le_iff_le_comap.mp (le_sSup ⟨Normal.map inferInstance _ u.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩)
  have hcentral := u.rangeRestrict.coreMap_ker_le_center_of_map_ker
    u.rangeRestrict_surjective huCore (map_le_iff_le_comap.mpr huk)
  have hkK (k : E.K) (hk : f (Models.componentEmbedding E g k) = 1) :
      QuotientGroup.mk' (pCore 2 E.K) k ∈ center (E.K ⧸ pCore 2 E.K) := by
    apply hcentral
    apply (QuotientGroup.eq_one_iff _).mpr
    have hm : u k ∈ pCore 2 (actionImage ρ) := (QuotientGroup.eq_one_iff _).mp hk
    exact (show (pCore 2 (actionImage ρ)).comap u.range.subtype ≤ pCore 2 u.range from
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective _ u.range.subtype_injective⟩) hm
  let N := (Models.componentEmbedding E g).range
  let e : E.K ≃* N := MonoidHom.ofInjective (component_injective E g)
  let eQ := QuotientGroup.congr (pCore 2 E.K) (pCore 2 N) e (pCore_map_iso 2 e)
  let : N.Normal := Models.componentEmbedding_normal E g h
  let : Group.IsPerfect (⊤ : Subgroup E.K) := (Models.component_top E hK).perfect
  let : Group.IsPerfect E.K := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup E.K) ≃* E.K).toMonoidHom) topEquiv.surjective
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hk : N ⊓ f.ker ≤ ((center (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype := by
    rintro a ⟨ha,haf⟩
    obtain ⟨k,hka⟩ := e.surjective ⟨a,ha⟩
    have hki : Models.componentEmbedding E g k = a := congrArg Subtype.val hka
    refine ⟨e k,?_,hki⟩
    have hc := (centerCongr eQ ⟨QuotientGroup.mk' (pCore 2 E.K) k,
      hkK k (hki.symm ▸ haf)⟩).property
    exact hc
  have hmarker : ((generalizedFitting (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype = markedFitting E g := by
    rw [← fitting_core_preimage_map_equiv e, map_map]
    exact fittingLift_component_map E g
  intro hc
  have hcomm : ⁅((generalizedFitting (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype, (seed E g p).range⁆ ≤ f.ker := by
    rw [hmarker]
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr (hc hx)
  have hA : IsPGroup 2 (seed E g p).range := by
    let := D.elementary
    exact (IsElementaryAbelian.isPGroup 2 V).of_surjective
      (seed E g p).rangeRestrict (seed E g p).rangeRestrict_surjective
  have hcore := two_subgroup_le_core_of_fitting_commutator_killed N
    (component_two_quotient E g h) f hf hkill (pCore_quotient_pCore_eq_bot (G := actionImage ρ) 2)
    hk (seed E g p).range hA hcomm
  apply p.seed_not_core
  intro v hv
  exact mem_map_of_mem (actor E g).subtype (hcore (show seed E g p ⟨v,hv⟩ ∈
    (seed E g p).range from ⟨⟨v,hv⟩,rfl⟩))

/-- The source relative-component and local rank-one facts construct a chief
section on which both the generalized-Fitting lift and V survive. -/
theorem exists_joint_chief_section_of_rank_one (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (p : OddPair E g) :
    ∃ A B : Subrepresentation (action E g), A ⋖ B ∧
      ¬ markedFitting E g ≤ (sectionRepresentation (action E g) A B).ker ∧
      ∃ v : V, seed E g p v ∉ (sectionRepresentation (action E g) A B).ker := by
  obtain ⟨F,hfield,hfinite,hcard,⟨e⟩⟩ := hlocal
  have hlarge : 4 ≤ Nat.card F := by
    rw [hcard]
    change (2 : ℕ)^2 ≤ 2 ^ E.input.field.degree
    exact Nat.pow_le_pow_right (by decide) (by have := E.input.nonbinary; omega)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁) := e.isSimpleGroup
  exact exists_joint_fitting_chief_section E g p
    (fitting_seed_commutator_not_le_twoCore E g h hK hlt p)

omit [IsElementaryAbelian 2 (localClosure E)] in
/-- The last paragraph of 11.5.8 from its literal earlier-source premises.
The surrounding amalgam owner supplies OddPair existence; the flag and component
owners supply the point, local quotient, relative component and surviving cases. -/
theorem false_of_odd_pair (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (hp : E.point ≠ ⊥) (p : OddPair E g)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (hcase : Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree) : False := by
  let := localClosure_elementary E h hab
  obtain ⟨A,B,hAB,hF,v,hv⟩ := exists_joint_chief_section_of_rank_one E g h hK hlt hlocal p
  exact Models.false_of_surviving_chief_section E g h hab hs hp p hK hlt hcase A B hAB hF v hv

omit [IsElementaryAbelian 2 (localClosure E)] in
/-- Actual marked-flag application, deriving the nonzero point rather than
asking for another chief-action hypothesis. Only the first flag marking is
used by this paragraph. -/
theorem false_of_odd_pair_of_flag (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (c : LocalGeometry.Coordinates D E.input.field) (f : LocalGeometry.InvariantFlag c)
    (hpoint : E.point = c.binarySubspace (f.space 0)) (p : OddPair E g)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (hcase : Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree) : False := by
  have hp : E.point ≠ ⊥ := by
    intro hz
    apply f.space_ne_bot 0
    apply bot_unique
    apply (c.binarySubspace_le_iff (f.space 0) ⊥).mp
    rw [← hpoint,hz]
    exact bot_le
  exact false_of_odd_pair E g h hab hs hp p hK hlt hlocal hcase

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
