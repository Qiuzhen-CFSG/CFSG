module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors.Spaces
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors.Families
public import Theory.GroupAction.Defs

/-!
# Pencil centralizer assembly on literal quotients

This module transports the actual natural and trace-zero G₂(2) calculations to
literal source quotients. The full centralizer remains in the full actor; the
derived centralizer is obtained by intersection with the actual commutator
actor. Source marking, model equivalence and equivariance remain explicit
inputs, while all fixed-space, moved-space and commutator-family conclusions
are discharged by the model calculations.

Source: Aschbacher–Smith 14.7.55(4),(8), printed p.1066, PDF p.1083.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open Representation.BinaryOffender
open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors
variable {V Q D H : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Group Q] [Group D] [Group H] [MulDistribMulAction H Q]

private def pull (e : Multiplicative V ≃* Q) (S : Subgroup Q) : Submodule (ZMod 2) V where
  carrier := {v | e (Multiplicative.ofAdd v) ∈ S}
  zero_mem' := by change e 1 ∈ S; rw [map_one]; exact S.one_mem
  add_mem' {v w} hv hw := by
    change e (Multiplicative.ofAdd v * Multiplicative.ofAdd w) ∈ S
    rw [map_mul]
    exact S.mul_mem hv hw
  smul_mem' a v hv := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · simp only [zero_smul]; change e 1 ∈ S; rw [map_one]; exact S.one_mem
    · simpa only [one_smul] using hv

private def imageIso (e : Multiplicative V ≃* Q) : Submodule (ZMod 2) V ≃o Subgroup Q where
  toFun P := P.toAddSubgroup.toSubgroup.map e.toMonoidHom
  invFun := pull e
  left_inv P := by
    ext v
    change (∃ w : Multiplicative V, w.toAdd ∈ P ∧ e w = e (Multiplicative.ofAdd v)) ↔ v ∈ P
    simp only [e.injective.eq_iff, exists_eq_right]
    rfl
  right_inv S := by
    ext q
    change (∃ w : Multiplicative V, e w ∈ S ∧ e w = q) ↔ q ∈ S
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hq; exact ⟨e.symm q, by simpa, e.apply_symm_apply q⟩
  map_rel_iff' := by
    intro P R
    change P.toAddSubgroup.toSubgroup.map e.toMonoidHom ≤
      R.toAddSubgroup.toSubgroup.map e.toMonoidHom ↔ P ≤ R
    rw [Subgroup.map_le_map_iff_of_injective e.injective]
    rfl

private theorem image_mem (e : Multiplicative V ≃* Q) (P : Submodule (ZMod 2) V) (v : V) :
    e (Multiplicative.ofAdd v) ∈ imageIso e P ↔ v ∈ P := by
  change (∃ w : Multiplicative V, w.toAdd ∈ P ∧ e w = e (Multiplicative.ofAdd v)) ↔ _
  simp only [e.injective.eq_iff, exists_eq_right]
  rfl

private theorem image_fixed (ρ : Representation (ZMod 2) D V)
    (e : Multiplicative V ≃* Q) (α : D →* H)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) = e (Multiplicative.ofAdd (ρ g v)))
    (A : Subgroup D) :
    imageIso e (fixedSpace ρ A) = fixedPointSubgroup (A.map α) Q := by
  apply Subgroup.ext
  intro q
  obtain ⟨v, rfl⟩ := e.surjective q
  change e (Multiplicative.ofAdd v.toAdd) ∈ _ ↔ _
  rw [image_mem]
  constructor
  · intro hv
    rintro ⟨_, g, hg, rfl⟩
    exact (he g v.toAdd).trans (congrArg (fun w => e (Multiplicative.ofAdd w)) (hv ⟨g,hg⟩))
  · intro hv g
    apply Multiplicative.ofAdd.injective
    apply e.injective
    change e (Multiplicative.ofAdd (ρ g.val v.toAdd)) = e (Multiplicative.ofAdd v.toAdd)
    rw [← he]
    exact hv ⟨α g, Subgroup.mem_map_of_mem α g.property⟩

private theorem image_moved (ρ : Representation (ZMod 2) D V)
    (e : Multiplicative V ≃* Q) (α : D →* H)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) = e (Multiplicative.ofAdd (ρ g v)))
    (A : Subgroup D) (P : Submodule (ZMod 2) V) :
    imageIso e (subspaceCommutator ρ P A) = commutatorSubgroup (A.map α) Q (imageIso e P) := by
  have disp (g : D) (v : V) : e (Multiplicative.ofAdd (ρ g v - v)) =
      (e (Multiplicative.ofAdd v))⁻¹ * (α g • e (Multiplicative.ofAdd v)) := by
    rw [he, ← map_inv, ← map_mul]
    congr 1
    change ρ g v - v = -v + ρ g v
    exact sub_eq_neg_add _ _
  apply le_antisymm
  · rw [show imageIso e (subspaceCommutator ρ P A) =
        (subspaceCommutator ρ P A).toAddSubgroup.toSubgroup.map e.toMonoidHom from rfl,
      Subgroup.map_le_iff_le_comap]
    change subspaceCommutator ρ P A ≤ pull e (commutatorSubgroup (A.map α) Q (imageIso e P))
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    change e (Multiplicative.ofAdd (ρ g v - v)) ∈ commutatorSubgroup (A.map α) Q (imageIso e P)
    rw [disp]
    exact Subgroup.subset_closure ⟨⟨α g,Subgroup.mem_map_of_mem α hg⟩,
      e (Multiplicative.ofAdd v),(image_mem e P v).mpr hv,rfl⟩
  · rw [commutatorSubgroup, Subgroup.closure_le]
    rintro _ ⟨⟨_,g,hg,rfl⟩,q,hq,rfl⟩
    obtain ⟨v,rfl⟩ := e.surjective q
    change (e (Multiplicative.ofAdd v.toAdd))⁻¹ * (α g • e (Multiplicative.ofAdd v.toAdd)) ∈ imageIso e (subspaceCommutator ρ P A)
    rw [← disp, image_mem]
    exact Submodule.subset_span ⟨g,hg,v.toAdd,(image_mem e P v.toAdd).mp hq,rfl⟩

private theorem image_singleton (e : Multiplicative V ≃* Q) (v : V) :
    imageIso e ((ZMod 2) ∙ v) = Subgroup.zpowers (e (Multiplicative.ofAdd v)) := by
  apply le_antisymm
  · change ((ZMod 2) ∙ v).toAddSubgroup.toSubgroup.map e.toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    change ((ZMod 2) ∙ v) ≤ pull e _
    rw [Submodule.span_singleton_le_iff_mem]
    exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr ((image_mem e _ v).mpr (Submodule.mem_span_singleton_self v))

private theorem image_index (e : Multiplicative V ≃* Q) (P : Submodule (ZMod 2) V)
    (hp : Module.finrank (ZMod 2) (V ⧸ P) = 1) : (imageIso e P).index = 2 := by
  change (P.toAddSubgroup.toSubgroup.map e.toMonoidHom).index = 2
  rw [Subgroup.index_map_of_bijective e.bijective, AddSubgroup.index_toSubgroup, AddSubgroup.index_eq_card]
  change Nat.card (V ⧸ P) = 2
  let := Module.finite_of_finrank_eq_succ hp
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hp]
  simp

def quotientFixedSpan (B : Subgroup H) : Subgroup Q :=
  ⨆ (b : H) (_ : b ∈ B) (_ : b ≠ 1), fixedPointSubgroup (Subgroup.zpowers b) Q

private theorem image_fixedSpan (ρ : Representation (ZMod 2) D V)
    (e : Multiplicative V ≃* Q) (α : D →* H) (hinj : Function.Injective α)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) = e (Multiplicative.ofAdd (ρ g v)))
    (B : Subgroup D) :
    imageIso e (fixedSpaceSpan ρ B) = quotientFixedSpan (Q := Q) (B.map α) := by
  simp only [fixedSpaceSpan, (imageIso e).map_iSup, image_fixed ρ e α he,
    quotientFixedSpan]
  apply le_antisymm
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hne => ?_
    exact le_iSup_of_le (α b) (le_iSup_of_le (Subgroup.mem_map_of_mem α hb)
      (le_iSup_of_le (fun h => hne (hinj (h.trans (map_one α).symm))) (by rw [MonoidHom.map_zpowers])))
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hne => ?_
    obtain ⟨b,hb,rfl⟩ := hb
    exact le_iSup_of_le b (le_iSup_of_le hb
      (le_iSup_of_le (fun h => hne (h ▸ map_one α)) (by rw [MonoidHom.map_zpowers])))


/-- The derived-actor clauses of 14.7.55(4), stated for actual subgroups of
an action module, with the geometric perpendicular retained. -/
structure DerivedConclusions (geom : QuotientGeometry Q) (P W : Subgroup Q)
    (B : Subgroup H) : Prop where
  elementary : IsElementaryAbelian 2 B
  card : Nat.card B = 4
  moved : ∀ b ∈ B, b ≠ 1 →
    commutatorAction (Subgroup.zpowers b) Q ∈ quotientPencil geom P
  fixedSpan : quotientFixedSpan (Q := Q) B = W
  hyperplane : W.index = 2

/-- The full-actor part of 14.7.55(4) and the complete family equality (8).
The second family includes the identity of the elementary abelian module. -/
structure FullConclusions (geom : QuotientGeometry Q) (P : Subgroup Q)
    (A B : Subgroup H) : Prop where
  elementary : IsElementaryAbelian 2 A
  card : Nat.card A = 8
  spaces : ∀ a ∈ A, a ∉ B →
    quotientPencilSpan geom P ⊔ fixedPointSubgroup H Q =
      fixedPointSubgroup (Subgroup.zpowers a) Q ∧
    fixedPointSubgroup (Subgroup.zpowers a) Q = fixedPointSubgroup B Q ∧
    fixedPointSubgroup B Q = commutatorAction A Q
  families :
    {S | ∃ b ∈ B, S = commutatorAction (Subgroup.zpowers b) Q} =
    {S | ∃ w ∈ quotientFixedSpan (Q := Q) B,
      S = commutatorSubgroup A Q (Subgroup.zpowers w)}

private theorem transport_derived (f : SingularMap V)
    (ρ : Representation (ZMod 2) D V) (e : Multiplicative V ≃* Q) (α : D →* H)
    (hinj : Function.Injective α)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) = e (Multiplicative.ofAdd (ρ g v)))
    (p : SingularPoints (ZMod 2)) (B : Subgroup D)
    (hB : IsElementaryAbelian 2 B) (hcard : Nat.card B = 4)
    (hmoved : ∀ b ∈ B, b ≠ 1 → ∃ L : ZeroProductLine (ZMod 2), pointOnLine p L ∧
      subspaceCommutator ρ ⊤ (Subgroup.zpowers b) = f.line L)
    (hspan : fixedSpaceSpan ρ B = perpendicular f p)
    (hcodim : Module.finrank (ZMod 2) (V ⧸ perpendicular f p) = 1) :
    DerivedConclusions (transportGeometry f.geometry e)
      ((transportGeometry f.geometry e).point p) (imageIso e (perpendicular f p)) (B.map α) := by
  let := hB
  refine ⟨IsElementaryAbelian.map α,
    (Subgroup.card_map_of_injective hinj).trans hcard, ?_, ?_, image_index e _ hcodim⟩
  · rintro _ ⟨b,hb,rfl⟩ hne
    have hbne : b ≠ 1 := fun h => hne (h ▸ map_one α)
    obtain ⟨L,hL,hm⟩ := hmoved b hb hbne
    have hi := congrArg (imageIso e) hm
    rw [image_moved ρ e α he, (imageIso e).map_top] at hi
    rw [← MonoidHom.map_zpowers]
    change commutatorSubgroup _ Q ⊤ ∈ _
    rw [hi]
    exact ⟨⟨L,rfl⟩, ((transportGeometry f.geometry e).incidence p L).mp hL⟩
  · rw [← image_fixedSpan ρ e α hinj he, hspan]

private theorem transport_full (f : SingularMap V)
    (ρ : Representation (ZMod 2) D V) (e : Multiplicative V ≃* Q) (α : D ≃* H)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) = e (Multiplicative.ofAdd (ρ g v)))
    (p : SingularPoints (ZMod 2)) (A B : Subgroup D)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 8)
    (hspaces : ∀ a ∈ A, a ∉ B →
      pencilSpan f p ⊔ fixedSpace ρ ⊤ = fixedSpace ρ (Subgroup.zpowers a) ∧
      fixedSpace ρ (Subgroup.zpowers a) = fixedSpace ρ B ∧
      fixedSpace ρ B = subspaceCommutator ρ ⊤ A)
    (hfamily : {S | ∃ b ∈ B, S = subspaceCommutator ρ ⊤ (Subgroup.zpowers b)} =
      {S | ∃ w ∈ fixedSpaceSpan ρ B, S = subspaceCommutator ρ ((ZMod 2) ∙ w) A}) :
    FullConclusions (transportGeometry f.geometry e)
      ((transportGeometry f.geometry e).point p) (A.map α.toMonoidHom) (B.map α.toMonoidHom) := by
  let := hA
  refine ⟨IsElementaryAbelian.map _,
    (Subgroup.card_map_of_injective α.injective).trans hcard, ?_, ?_⟩
  · rintro _ ⟨a,ha,rfl⟩ hout
    obtain ⟨h1,h2,h3⟩ := hspaces a ha (fun hb => hout (Subgroup.mem_map_of_mem _ hb))
    have H1 := congrArg (imageIso e) h1
    have H2 := congrArg (imageIso e) h2
    have H3 := congrArg (imageIso e) h3
    rw [(imageIso e).map_sup, image_fixed ρ e α.toMonoidHom he,
      image_fixed ρ e α.toMonoidHom he] at H1
    rw [image_fixed ρ e α.toMonoidHom he, image_fixed ρ e α.toMonoidHom he] at H2
    rw [image_fixed ρ e α.toMonoidHom he, image_moved ρ e α.toMonoidHom he,
      (imageIso e).map_top] at H3
    rw [quotientPencilSpan_eq]
    have hz (x : D) : Subgroup.map α.toMonoidHom (Subgroup.zpowers x) =
        Subgroup.zpowers (α x) := MonoidHom.map_zpowers _ _
    have htopfix : FixedPoints.subgroup (⊤ : Subgroup H) Q = FixedPoints.subgroup H Q := by
      ext q
      change (∀ a : (⊤ : Subgroup H), a.1 • q = q) ↔ ∀ a : H, a • q = q
      constructor
      · intro h a; exact h ⟨a, by trivial⟩
      · intro h a; exact h a.1
    have htop : Subgroup.map α.toMonoidHom (⊤ : Subgroup D) = ⊤ :=
      Subgroup.map_top_of_surjective _ α.surjective
    rw [htop] at H1
    change (imageIso e (pencilSpan f p) ⊔ fixedPointSubgroup H Q =
      fixedPointSubgroup (Subgroup.zpowers (α a)) Q) ∧
      fixedPointSubgroup (Subgroup.zpowers (α a)) Q = fixedPointSubgroup (B.map α.toMonoidHom) Q ∧
      fixedPointSubgroup (B.map α.toMonoidHom) Q =
        commutatorSubgroup (A.map α.toMonoidHom) Q ⊤
    rw [hz a] at H1 H2
    change imageIso e (pencilSpan f p) ⊔ FixedPoints.subgroup (⊤ : Subgroup H) Q = _ at H1
    rw [htopfix] at H1
    have H3' : FixedPoints.subgroup (B.map α.toMonoidHom) Q =
        commutatorSubgroup (A.map α.toMonoidHom) Q ⊤ := by
      simpa only [commutatorAction] using H3
    exact ⟨H1, ⟨H2, H3'⟩⟩
  · have hm (b : D) : imageIso e (subspaceCommutator ρ ⊤ (Subgroup.zpowers b)) =
        commutatorAction (Subgroup.zpowers (α b)) Q := by
      rw [image_moved ρ e α.toMonoidHom he, (imageIso e).map_top, MonoidHom.map_zpowers]
      rfl
    have hw (w : V) : imageIso e (subspaceCommutator ρ ((ZMod 2) ∙ w) A) =
        commutatorSubgroup (A.map α.toMonoidHom) Q (Subgroup.zpowers (e (Multiplicative.ofAdd w))) := by
      rw [image_moved ρ e α.toMonoidHom he, image_singleton]
    have hf := image_fixedSpan ρ e α.toMonoidHom α.injective he B
    ext S
    constructor
    · rintro ⟨_,⟨b,hb,rfl⟩,rfl⟩
      have hb' : subspaceCommutator ρ ⊤ (Subgroup.zpowers b) ∈
          {S | ∃ b ∈ B, S = subspaceCommutator ρ ⊤ (Subgroup.zpowers b)} := ⟨b,hb,rfl⟩
      rw [hfamily] at hb'
      obtain ⟨w,hwfix,heq⟩ := hb'
      refine ⟨e (Multiplicative.ofAdd w), ?_, ?_⟩
      · rw [← hf, image_mem]; exact hwfix
      · change commutatorAction (Subgroup.zpowers (α b)) Q = _
        calc
          commutatorAction (Subgroup.zpowers (α b)) Q =
              imageIso e (subspaceCommutator ρ ⊤ (Subgroup.zpowers b)) := (hm b).symm
          _ = imageIso e (subspaceCommutator ρ ((ZMod 2) ∙ w) A) := congrArg (imageIso e) heq
          _ = _ := hw w
    · rintro ⟨q,hq,rfl⟩
      obtain ⟨w,rfl⟩ := e.surjective q
      have hwfix : w.toAdd ∈ fixedSpaceSpan ρ B := by
        rw [← hf] at hq
        exact (image_mem e _ w.toAdd).mp hq
      have hw' : subspaceCommutator ρ ((ZMod 2) ∙ w.toAdd) A ∈
          {S | ∃ w ∈ fixedSpaceSpan ρ B, S = subspaceCommutator ρ ((ZMod 2) ∙ w) A} :=
        ⟨w.toAdd,hwfix,rfl⟩
      rw [← hfamily] at hw'
      obtain ⟨b,hb,heq⟩ := hw'
      refine ⟨α b,Subgroup.mem_map_of_mem _ hb,?_⟩
      calc
        commutatorSubgroup (A.map α.toMonoidHom) Q (Subgroup.zpowers (e w)) =
            imageIso e (subspaceCommutator ρ ((ZMod 2) ∙ w.toAdd) A) := (hw w.toAdd).symm
        _ = imageIso e (subspaceCommutator ρ ⊤ (Subgroup.zpowers b)) := congrArg (imageIso e) heq
        _ = _ := hm b
/-- Assemble (4) and (8) with A the actual full pointwise centralizer and B
its intersection with the actual derived actor. -/
def FullPencilConclusions (geom : QuotientGeometry Q) (P W : Subgroup Q) : Prop :=
  let A := _root_.fixingSubgroup H (quotientPencilSpan geom P : Set Q)
  let B := A ⊓ commutator H
  DerivedConclusions geom P W B ∧ FullConclusions geom P A B

/-- The derived-only case has its entire actor as K*. No elementary eight
is asserted to lie in that actor. -/
def DerivedPencilConclusions (geom : QuotientGeometry Q) (P W : Subgroup Q) : Prop :=
  DerivedConclusions geom P W (_root_.fixingSubgroup H (quotientPencilSpan geom P : Set Q))

private theorem full_application (f : SingularMap V)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) V) (hf : f.Equivariant ρ)
    (e : Multiplicative V ≃* Q) (α : Model (ZMod 2) ≃* H)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) = e (Multiplicative.ofAdd (ρ g v)))
    (p : SingularPoints (ZMod 2))
    (hmoved : ∀ b ∈ derivedCentralizer f ρ p, b ≠ 1 →
      ∃ L : ZeroProductLine (ZMod 2), pointOnLine p L ∧
        subspaceCommutator ρ ⊤ (Subgroup.zpowers b) = f.line L)
    (hspan : fixedSpaceSpan ρ (derivedCentralizer f ρ p) = perpendicular f p)
    (hcodim : Module.finrank (ZMod 2) (V ⧸ perpendicular f p) = 1)
    (hspaces : ∀ a ∈ fullCentralizer f ρ p, a ∉ derivedCentralizer f ρ p →
      pencilSpan f p ⊔ fixedSpace ρ ⊤ = fixedSpace ρ (Subgroup.zpowers a) ∧
      fixedSpace ρ (Subgroup.zpowers a) = fixedSpace ρ (derivedCentralizer f ρ p) ∧
      fixedSpace ρ (derivedCentralizer f ρ p) = subspaceCommutator ρ ⊤ (fullCentralizer f ρ p))
    (hfamily : {S | ∃ b ∈ derivedCentralizer f ρ p,
        S = subspaceCommutator ρ ⊤ (Subgroup.zpowers b)} =
      {S | ∃ w ∈ perpendicular f p,
        S = subspaceCommutator ρ ((ZMod 2) ∙ w) (fullCentralizer f ρ p)}) :
    FullPencilConclusions (H := H) (transportGeometry f.geometry e)
      ((transportGeometry f.geometry e).point p) (imageIso e (perpendicular f p)) := by
  have hc : (commutator (Model (ZMod 2))).map α.toMonoidHom = commutator H := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ α.surjective]
    rfl
  dsimp [FullPencilConclusions]
  rw [quotient_fullCentralizer_eq f ρ e α he p]
  have hB : (fullCentralizer f ρ p).map α.toMonoidHom ⊓ commutator H =
      (derivedCentralizer f ρ p).map α.toMonoidHom := by
    rw [← hc, ← Subgroup.map_inf _ _ _ α.injective]
    rfl
  rw [hB]
  change DerivedConclusions _ _ _ ((derivedCentralizer f ρ p).map α.toMonoidHom) ∧ _
  obtain ⟨hB,hBc⟩ := derivedCentralizer_structure f ρ hf p
  obtain ⟨hA,hAc⟩ := fullCentralizer_structure f ρ hf p
  refine ⟨transport_derived f ρ e α.toMonoidHom α.injective he p _
    hB hBc hmoved hspan hcodim, ?_⟩
  apply transport_full f ρ e α he p _ _ hA hAc hspaces
  rwa [hspan]

private theorem derived_application (f : SingularMap V)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) V) (hf : f.Equivariant ρ)
    (e : Multiplicative V ≃* Q) (α : commutator (Model (ZMod 2)) ≃* H)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) = e (Multiplicative.ofAdd (ρ g.val v)))
    (p : SingularPoints (ZMod 2))
    (hmoved : ∀ b ∈ derivedCentralizer f ρ p, b ≠ 1 →
      ∃ L : ZeroProductLine (ZMod 2), pointOnLine p L ∧
        subspaceCommutator ρ ⊤ (Subgroup.zpowers b) = f.line L)
    (hspan : fixedSpaceSpan ρ (derivedCentralizer f ρ p) = perpendicular f p)
    (hcodim : Module.finrank (ZMod 2) (V ⧸ perpendicular f p) = 1) :
    DerivedPencilConclusions (H := H) (transportGeometry f.geometry e)
      ((transportGeometry f.geometry e).point p) (imageIso e (perpendicular f p)) := by
  let K := commutator (Model (ZMod 2))
  let B := (derivedCentralizer f ρ p).subgroupOf K
  let σ := ρ.comp K.subtype
  have hmap : B.map K.subtype = derivedCentralizer f ρ p :=
    Subgroup.map_subgroupOf_eq_of_le (derivedCentralizer_le f ρ p)
  have hspan' : fixedSpaceSpan σ B = perpendicular f p := by
    have h := fixedSpaceSpan_map_equivariant σ ρ K.subtype K.subtype_injective
      (LinearEquiv.refl (ZMod 2) V) (fun _ _ => rfl) B
    simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id, hmap, hspan] using h
  have hm (b : K) : subspaceCommutator σ ⊤ (Subgroup.zpowers b) =
      subspaceCommutator ρ ⊤ (Subgroup.zpowers (K.subtype b)) := by
    have h := subspaceCommutator_map_embedding σ ρ K.subtype
      (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ => rfl) (Subgroup.zpowers b) ⊤
    rw [MonoidHom.map_zpowers] at h
    simpa only [Submodule.map_id] using h
  have hmoved' (b : K) (hb : b ∈ B) (hne : b ≠ 1) :
      ∃ L : ZeroProductLine (ZMod 2), pointOnLine p L ∧
        subspaceCommutator σ ⊤ (Subgroup.zpowers b) = f.line L := by
    rw [hm]
    exact hmoved b.val hb (fun h => hne (Subtype.ext h))
  obtain ⟨hB,hBc⟩ := derivedActorCentralizer_structure f ρ hf p
  rw [derivedCentralizer_actor] at hB hBc
  unfold DerivedPencilConclusions
  rw [quotient_derivedCentralizer_eq f ρ e α he p]
  exact transport_derived f σ e α.toMonoidHom α.injective he p B hB hBc hmoved' hspan' hcodim

variable {G : Type*} [Group G]

/-- The natural realization of 14.7.55((4),(8)) on the literal source
quotient, conditional only on its equivariant model and singular-point marking. -/
theorem natural_source_full (U V₁ V₂ : Subgroup G)
    [(V₁.subgroupOf U).Normal] [MulDistribMulAction H (U ⧸ V₁.subgroupOf U)]
    (e : Multiplicative (Space (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (α : Model (ZMod 2) ≃* H)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) =
      e (Multiplicative.ofAdd (action (ZMod 2) g v)))
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (naturalQuotientGeometry (V₁.subgroupOf U) e).point p) :
    FullPencilConclusions (H := H) (naturalQuotientGeometry (V₁.subgroupOf U) e)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))
      ((perpendicular naturalMap p).toAddSubgroup.toSubgroup.map e.toMonoidHom) := by
  rw [hmark]
  exact full_application naturalMap (action (ZMod 2)) naturalMap_equivariant e α he p
    (natural_nonidentity_moved p) (natural_fixedSpaceSpan p) (natural_perpendicular_codim p)
    (natural_full_spaces p) (Families.natural_commutator_families p)

/-- The natural realization of 14.7.55((4)) on the literal source
quotient, conditional only on its equivariant model and singular-point marking. -/
theorem natural_source_derived (U V₁ V₂ : Subgroup G)
    [(V₁.subgroupOf U).Normal] [MulDistribMulAction H (U ⧸ V₁.subgroupOf U)]
    (e : Multiplicative (Space (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (α : commutator (Model (ZMod 2)) ≃* H)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) =
      e (Multiplicative.ofAdd (action (ZMod 2) g.val v)))
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (naturalQuotientGeometry (V₁.subgroupOf U) e).point p) :
    DerivedPencilConclusions (H := H) (naturalQuotientGeometry (V₁.subgroupOf U) e)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))
      ((perpendicular naturalMap p).toAddSubgroup.toSubgroup.map e.toMonoidHom) := by
  rw [hmark]
  exact derived_application naturalMap (action (ZMod 2)) naturalMap_equivariant e α he p
    (natural_nonidentity_moved p) (natural_fixedSpaceSpan p) (natural_perpendicular_codim p)

/-- The weyl realization of 14.7.55((4),(8)) on the literal source
quotient, conditional only on its equivariant model and singular-point marking. -/
theorem weyl_source_full (U V₁ V₂ : Subgroup G)
    [(V₁.subgroupOf U).Normal] [MulDistribMulAction H (U ⧸ V₁.subgroupOf U)]
    (e : Multiplicative (TraceZero (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (α : Model (ZMod 2) ≃* H)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) =
      e (Multiplicative.ofAdd (traceZeroAction (ZMod 2) g v)))
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (weylQuotientGeometry (V₁.subgroupOf U) e).point p) :
    FullPencilConclusions (H := H) (weylQuotientGeometry (V₁.subgroupOf U) e)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))
      ((perpendicular weylMap p).toAddSubgroup.toSubgroup.map e.toMonoidHom) := by
  rw [hmark]
  exact full_application weylMap (traceZeroAction (ZMod 2)) weylMap_equivariant e α he p
    (weyl_nonidentity_moved p) (weyl_fixedSpaceSpan p) (weyl_perpendicular_codim p)
    (weyl_full_spaces p) (Families.weyl_commutator_families p)

/-- The weyl realization of 14.7.55((4)) on the literal source
quotient, conditional only on its equivariant model and singular-point marking. -/
theorem weyl_source_derived (U V₁ V₂ : Subgroup G)
    [(V₁.subgroupOf U).Normal] [MulDistribMulAction H (U ⧸ V₁.subgroupOf U)]
    (e : Multiplicative (TraceZero (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (α : commutator (Model (ZMod 2)) ≃* H)
    (he : ∀ g v, α g • e (Multiplicative.ofAdd v) =
      e (Multiplicative.ofAdd (traceZeroAction (ZMod 2) g.val v)))
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (weylQuotientGeometry (V₁.subgroupOf U) e).point p) :
    DerivedPencilConclusions (H := H) (weylQuotientGeometry (V₁.subgroupOf U) e)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))
      ((perpendicular weylMap p).toAddSubgroup.toSubgroup.map e.toMonoidHom) := by
  rw [hmark]
  exact derived_application weylMap (traceZeroAction (ZMod 2)) weylMap_equivariant e α he p
    (weyl_nonidentity_moved p) (weyl_fixedSpaceSpan p) (weyl_perpendicular_codim p)

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors
