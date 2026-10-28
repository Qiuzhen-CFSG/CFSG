module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.CentralizerCoordinates
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.InvolutionImages
public import Theory.Representation.SL2NaturalOffenders.Ratios

/-!
# Fixed spaces of the actual noncentral J₂ actors

The checked centralizer coordinates split the literal displacement module W
as a trivial field line plus the natural SL₂(4) plane. The image of an elementary
actor is a two-subgroup of this actual SL₂, and rank at least three makes the
image nontrivial. Sylow conjugacy and the nonidentity-matrix fixed-space bound
show that it fixes one field line. The resulting fixed-space equivalence gives
binary dimension four. Quadraticity would centralize all six dimensions of W,
which is impossible.

Only the universal B.4.6 root-geometry clauses remain inputs; the particular
J₂ short-root placement is discharged by InvolutionImages. Recognition of the
marked module and the final source ratios belong to their independent owners.
Source: Aschbacher–Smith, K.4.5, printed p.460/PDF p.471.
-/

open Subgroup Representation Representation.BinaryOffender
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.InnerInvolutionCores
open CFSG.Quasithin.ChapterK.JankoTwo
open CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction
open Matrix
open scoped MatrixGroups
public noncomputable section

namespace CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction
variable {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K] [Finite K]
private theorem sl2_fixed_dimension (Q : Subgroup SL(2,K))
    (hne : Q ≠ ⊥) (hQ : IsPGroup 2 Q) :
    Module.finrank (ZMod 2) (fixedSpace (SL2NaturalOffenders.NoStrong.natural (F := K)) Q) =
      Module.finrank (ZMod 2) K := by
  let N := SL2NaturalOffenders.NoStrong.natural (F := K)
  obtain ⟨P,hP⟩ := hQ.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,K)
    (Matrix.SpecialLinearGroup.upperUnipotentSylow K 2) P
  have he : (P : Subgroup SL(2,K)) =
      (Matrix.SpecialLinearGroup.upperUnipotent K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  have hdim : Module.finrank (ZMod 2) (fixedSpace N (P : Subgroup SL(2,K))) =
      Module.finrank (ZMod 2) K := by
    rw [he, ← (fixedSpaceConjEquiv N _ g).finrank_eq]
    exact SL2NaturalOffenders.Ratios.upper_fixed_finrank
  have hlo := Submodule.finrank_mono (fixedSpace_antitone N hP)
  have hcard := SL2NaturalOffenders.fixedSpace_card_le_of_le
    ⊤ Subgroup.topEquiv N (fun _ _ => rfl) hne le_top
  have hpow : 2 ^ Module.finrank (ZMod 2) (fixedSpace N Q) ≤
      2 ^ Module.finrank (ZMod 2) K := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace N Q),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)] at hcard
    simpa using hcard
  have hhi := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  change Module.finrank (ZMod 2) (fixedSpace N Q) = _
  omega
end CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction

namespace CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction
variable {K : Type*} [Field K]
/-- The actual SL₂ image of the actor in the full centralizer coordinates. -/
@[expose] def actorSL2Image (φ : A5 ≃* SL(2,K)) (A : Subgroup Carrier) : Subgroup SL(2,K) :=
  (A.comap centralizerEmbedding).map (φ.toMonoidHom.comp (MonoidHom.snd E4 A5))

theorem actorSL2Image_isTwoGroup (φ : A5 ≃* SL(2,K)) (A : Subgroup Carrier)
    (hA : IsElementaryTwo A) : IsPGroup 2 (actorSL2Image φ A) := by
  let : IsElementaryAbelian 2 A := hA.2
  exact ((IsElementaryAbelian.isPGroup 2 A).comap_of_injective
    centralizerEmbedding centralizerEmbedding_injective).map _

theorem actorSL2Image_ne_bot (φ : A5 ≃* SL(2,K)) (A : Subgroup Carrier)
    (hA : IsElementaryTwo A) (ha : a ∈ A) (hr : 3 ≤ rank A) :
    actorSL2Image φ A ≠ ⊥ := by
  obtain ⟨x,hx,hne⟩ := exists_nontrivial_simple_coordinate A hA ha hr
  intro hb
  have hm : φ x.2 ∈ actorSL2Image φ A := mem_map_of_mem _ hx
  rw [hb, mem_bot] at hm
  exact hne (φ.injective (hm.trans φ.map_one.symm))

end CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction

namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)

private theorem centralizer_lift {A : Subgroup Carrier}
    (hAC : A ≤ involutionCentralizer) (x : A) :
    ∃ y : E4 × A5, centralizerEmbedding y = x := by
  refine ⟨a_centralizer_equiv ⟨x,hAC x.property⟩,?_⟩
  change (a_centralizer_equiv.symm (a_centralizer_equiv _)).val = x.val
  rw [MulEquiv.symm_apply_apply]

private theorem fixed_mem_localW (A : Subgroup Carrier) (ha : a ∈ A)
    (hW : D.localW.toSubmodule.restrictScalars (ZMod 2) =
      fixedSpace D.naturalCarrierAction (zpowers a))
    (v : fixedSpace D.naturalCarrierAction A) : v.val ∈ D.localW := by
  change v.val ∈ D.localW.toSubmodule.restrictScalars (ZMod 2)
  rw [hW, mem_fixedSpace_zpowers_iff]
  exact v.property ⟨a,ha⟩

private theorem coordinates_fixed_iff
    (φ : A5 ≃* SL(2,K)) (E : D.localW.toSubmodule ≃ₗ[K] K × (Fin 2 → K))
    (hE : ∀ (c : E4) (e : A5) (w : D.localW.toSubmodule),
      E (D.localW.toRepresentation (c,e) w) = ((E w).1, (φ e).val *ᵥ (E w).2))
    (A : Subgroup Carrier) (hAC : A ≤ involutionCentralizer)
    (w : D.localW.toSubmodule) :
    w.val ∈ fixedSpace D.naturalCarrierAction A ↔
      (E w).2 ∈ fixedSpace (SL2NaturalOffenders.NoStrong.natural (F := K)) (actorSL2Image φ A) := by
  constructor
  · intro hw x
    obtain ⟨y,hy,hyx⟩ := x.property
    have hv : D.localW.toRepresentation y w = w := Subtype.ext (hw ⟨_,hy⟩)
    have hh := congrArg (fun w => (E w).2) hv
    rw [hE y.1 y.2] at hh
    change x.val.val *ᵥ (E w).2 = (E w).2
    rw [← hyx]
    exact hh
  · intro hw x
    obtain ⟨y,hy⟩ := centralizer_lift hAC x
    have hm : φ y.2 ∈ actorSL2Image φ A := mem_map_of_mem _ (show centralizerEmbedding y ∈ A from hy.symm ▸ x.property)
    have he : D.localW.toRepresentation y w = w := by
      apply E.injective
      rw [hE y.1 y.2]
      exact Prod.ext rfl (hw ⟨_,hm⟩)
    have hh := congrArg Subtype.val he
    change D.naturalCarrierAction (centralizerEmbedding y) w.val = w.val at hh
    rwa [hy] at hh

/-- The actual actor's fixed space, with the literal equivariant coordinates. -/
def actorFixedEquiv
    (φ : A5 ≃* SL(2,K)) (E : D.localW.toSubmodule ≃ₗ[K] K × (Fin 2 → K))
    (hE : ∀ (c : E4) (e : A5) (w : D.localW.toSubmodule),
      E (D.localW.toRepresentation (c,e) w) = ((E w).1, (φ e).val *ᵥ (E w).2))
    (A : Subgroup Carrier) (hAC : A ≤ involutionCentralizer) (ha : a ∈ A)
    (hW : D.localW.toSubmodule.restrictScalars (ZMod 2) =
      fixedSpace D.naturalCarrierAction (zpowers a)) :
    fixedSpace D.naturalCarrierAction A ≃ₗ[ZMod 2]
      K × fixedSpace (SL2NaturalOffenders.NoStrong.natural (F := K)) (actorSL2Image φ A) where
  toFun v :=
    let w : D.localW.toSubmodule := ⟨v.val,D.fixed_mem_localW A ha hW v⟩
    ((E w).1, ⟨(E w).2,(D.coordinates_fixed_iff φ E hE A hAC w).mp v.property⟩)
  invFun v :=
    let w := E.symm (v.1,v.2.val)
    ⟨w.val,(D.coordinates_fixed_iff φ E hE A hAC w).mpr (by
      simpa only [w, LinearEquiv.apply_symm_apply] using v.2.property)⟩
  left_inv v := by
    apply Subtype.ext
    exact congrArg (fun w : D.localW.toSubmodule => w.val)
      (E.symm_apply_apply ⟨v.val,D.fixed_mem_localW A ha hW v⟩)
  right_inv v := by
    apply Prod.ext
    · exact congrArg (fun w : K × (Fin 2 → K) => w.1) (E.apply_symm_apply (v.1,v.2.val))
    · apply Subtype.ext
      exact congrArg (fun w : K × (Fin 2 → K) => w.2) (E.apply_symm_apply (v.1,v.2.val))
  map_add' v w := by
    have he := (E.restrictScalars (ZMod 2)).map_add
      ⟨v.val,D.fixed_mem_localW A ha hW v⟩ ⟨w.val,D.fixed_mem_localW A ha hW w⟩
    apply Prod.ext
    · exact congrArg (fun w : K × (Fin 2 → K) => w.1) he
    · apply Subtype.ext
      exact congrArg (fun w : K × (Fin 2 → K) => w.2) he
  map_smul' r v := by
    have he := (E.restrictScalars (ZMod 2)).map_smul r ⟨v.val,D.fixed_mem_localW A ha hW v⟩
    apply Prod.ext
    · exact congrArg (fun w : K × (Fin 2 → K) => w.1) he
    · apply Subtype.ext
      exact congrArg (fun w : K × (Fin 2 → K) => w.2) he

/-- W has binary dimension six, derived from the actual short-root coordinates. -/
theorem localW_binary_finrank
    (h : NaturalLocalAction.InvolutionImages.B46RootFacts K) :
    Module.finrank (ZMod 2) D.localW.toSubmodule = 6 := by
  obtain ⟨g,r,hr,he⟩ := D.carrierEmbedding_a_isShortRootElement h
  obtain ⟨φ,E,hE,-⟩ := D.localW_shortRoot_comparison g r hr he
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  rw [(E.restrictScalars (ZMod 2)).finrank_eq]
  simp [Module.finrank_prod, Module.finrank_pi_fintype, D.fieldDegree]

/-- Elementary actors of rank at least three containing a fix exactly four binary dimensions. -/
theorem noncentral_actor_fixed_finrank
    (h : NaturalLocalAction.InvolutionImages.B46RootFacts K)
    (A : Subgroup Carrier) (hA : IsElementaryTwo A) (ha : a ∈ A) (hr : 3 ≤ rank A) :
    Module.finrank (ZMod 2) (fixedSpace D.naturalCarrierAction A) = 4 := by
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  let : Finite K := Module.finite_of_finite (ZMod 2)
  obtain ⟨g,r,hr,he⟩ := D.carrierEmbedding_a_isShortRootElement h
  obtain ⟨φ,E,hE,hC,hW,-⟩ := D.localW_shortRoot_comparison g r hr he
  rw [(D.actorFixedEquiv φ E hE A (le_centralizer_of_elementary A hA ha) ha hW).finrank_eq,
    Module.finrank_prod,
    NaturalLocalAction.sl2_fixed_dimension _ (actorSL2Image_ne_bot φ A hA ha ‹3 ≤ rank A›)
      (actorSL2Image_isTwoGroup φ A hA), D.fieldDegree]

/-- These actors have fixed codimension eight in the actual natural quotient. -/
theorem noncentral_actor_fixedCodim
    (h : NaturalLocalAction.InvolutionImages.B46RootFacts K)
    (A : Subgroup Carrier) (hA : IsElementaryTwo A) (ha : a ∈ A) (hr : 3 ≤ rank A) :
    fixedCodim D.naturalCarrierAction A = 8 := by
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  let : Module.Finite (ZMod 2) (Atlas.G2.Natural.Space K) := Module.Finite.trans K _
  have hd := fixedCodim_add_finrank D.naturalCarrierAction A
  rw [D.finrank_space, D.noncentral_actor_fixed_finrank h A hA ha hr] at hd
  omega

/-- Quadraticity would centralize the actual displacement W, which has dimension six. -/
theorem noncentral_actor_not_quadratic
    (h : NaturalLocalAction.InvolutionImages.B46RootFacts K)
    (A : Subgroup Carrier) (hA : IsElementaryTwo A) (ha : a ∈ A) (hr : 3 ≤ rank A) :
    ¬ IsQuadratic D.naturalCarrierAction A := by
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  let : Module.Finite (ZMod 2) (Atlas.G2.Natural.Space K) := Module.Finite.trans K _
  intro hq
  have hle : D.localW.toSubmodule.restrictScalars (ZMod 2) ≤
      fixedSpace D.naturalCarrierAction A := by
    rintro w ⟨v,rfl⟩ x
    exact hq x x.property a ha v
  have hd := Submodule.finrank_mono hle
  rw [((D.localW.toSubmodule.restrictScalarsEquiv (ZMod 2)).restrictScalars
    (ZMod 2)).finrank_eq, D.localW_binary_finrank h,
    D.noncentral_actor_fixed_finrank h A hA ha hr] at hd
  omega

end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
