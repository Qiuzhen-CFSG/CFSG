module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Representation.Source

/-!
# The marked orthogonal action of the literal common-core join

Use the given natural marking for the first factor and the reconstructed
right action for the second factor. Their exact quotient maps give an
ordered product projection with kernel P. Every original element of K∨L₂
is a product of elements of the two factors, so their intertwining identities
combine into the determinant action M ↦ A M B⁻¹. The proved equality
Y=K∨L₂ then produces an OrthogonalMarking of the literal Y/P.

The resulting determinant form is invariant under original Y-conjugation,
as the final consumer records. Only the two relative C-component assertions
remain as premises; the common-core orthogonal task owns their discharge and
the subsequent Cartan recognition. No compatibility of the independent field
markings is used or asserted.

Source: Aschbacher--Smith, combined manuscript, printed p.774, the last
paragraph. The first factor's field has exactly the original degree.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

private theorem marked_projection
    {J E F : Type*} [Group J] [Finite J] [Group E] [Group F]
    [IsSimpleGroup E] [IsSimpleGroup F]
    (B C P : Subgroup J) [C.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hgen : B ⊔ C = ⊤) (hBP : B.pCoreIn 2 = P) (hCP : C.pCoreIn 2 = P)
    (eB : (B ⧸ pCore 2 B) ≃* E) (eC : (C ⧸ pCore 2 C) ≃* F) :
    ∃ q : J →* E × F, Function.Surjective q ∧ q.ker = P ∧
      B.map q = (MonoidHom.snd E F).ker ∧ C.map q = (MonoidHom.fst E F).ker ∧
      (∀ b : B, q b = (eB (QuotientGroup.mk' _ b), 1)) ∧
      (∀ c : C, q c = (1, eC (QuotientGroup.mk' _ c))) := by
  obtain ⟨q, hq, _, hb, hc⟩ := exists_twoCore_product_of_simple_pair B C hB hC hne hgen eB eC
  have hb0 (b : B) : q b = 1 ↔ (b : J) ∈ P := by
    rw [hb]
    change (eB (QuotientGroup.mk' _ b), 1) = (1, 1) ↔ _
    simp only [Prod.mk.injEq, and_true]
    rw [map_eq_one_iff eB eB.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hBP]
    exact (mem_map_iff_mem B.subtype_injective).symm
  have hc0 (c : C) : q c = 1 ↔ (c : J) ∈ P := by
    rw [hc]
    change (1, eC (QuotientGroup.mk' _ c)) = (1, 1) ↔ _
    simp only [Prod.mk.injEq, true_and]
    rw [map_eq_one_iff eC eC.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hCP]
    exact (mem_map_iff_mem C.subtype_injective).symm
  refine ⟨q,hq,?_,?_,?_,hb,hc⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨b,hb',c,hc',he⟩ := mem_sup_of_normal_right.mp (hgen ▸ mem_top x)
      have hh := show q x = 1 from hx
      rw [← he,map_mul,hb ⟨b,hb'⟩,hc ⟨c,hc'⟩] at hh
      have h1 : q b = 1 := by
        rw [hb ⟨b,hb'⟩]
        exact Prod.ext (by simpa using congrArg Prod.fst hh) rfl
      have h2 : q c = 1 := by
        rw [hc ⟨c,hc'⟩]
        exact Prod.ext rfl (by simpa using congrArg Prod.snd hh)
      rw [← he]
      exact P.mul_mem ((hb0 ⟨b,hb'⟩).mp h1) ((hc0 ⟨c,hc'⟩).mp h2)
    · intro hx
      exact (hb0 ⟨x,(hBP ▸ B.pCoreIn_le 2) hx⟩).mpr hx
  · ext x
    constructor
    · rintro ⟨b,hb',rfl⟩
      change (q b).2 = 1
      rw [hb ⟨b,hb'⟩]
    · intro hx
      obtain ⟨b,hb'⟩ := (eB.surjective.comp (QuotientGroup.mk'_surjective _)) x.1
      refine ⟨b,b.property,?_⟩
      rw [hb]
      exact Prod.ext hb' (show x.2 = 1 from hx).symm
  · ext x
    constructor
    · rintro ⟨c,hc',rfl⟩
      change (q c).1 = 1
      rw [hc ⟨c,hc'⟩]
    · intro hx
      obtain ⟨c,hc'⟩ := (eC.surjective.comp (QuotientGroup.mk'_surjective _)) x.2
      refine ⟨c,c.property,?_⟩
      rw [hc]
      exact Prod.ext (show x.1 = 1 from hx).symm hc'

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

theorem source_factorJoin_orthogonal_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    Nonempty (OrthogonalMarking (outsideResidual H ⊔ f.Li 1)
      (pairCore V H h) (outsideResidual H) (f.Li 1) d.pair_field) := by
  let J := outsideResidual H ⊔ f.Li 1
  have hJG : J ≤ coreNormalizer V H h := sup_le hK.1 hL.1
  have hn := source_factors_normal_of_components d hK hL
  have hln : coreNormalizer V H h ≤ normalizer (f.Li 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hL.1).mp hn.2
  let B := (outsideResidual H).subgroupOf J
  let C := (f.Li 1).subgroupOf J
  let P := (pairCore V H h).subgroupOf J
  let : C.Normal := normal_subgroupOf_of_le_normalizer (hJG.trans hln)
  have hb : B.IsCComponent := hK.2.subgroupOf_of_le le_sup_left hJG
  have hc : C.IsCComponent := hL.2.subgroupOf_of_le le_sup_right hJG
  have hne : B ≠ C := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le (show outsideResidual H ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show f.Li 1 ≤ J from le_sup_right)] at hh
    exact source_residual_ne_local d hh
  have hgen : B ⊔ C = ⊤ := by
    rw [← subgroupOf_sup (show outsideResidual H ≤ J from le_sup_left)
      (show f.Li 1 ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hbP : B.pCoreIn 2 = P := by
    rw [pCoreIn_subgroupOf _ _ _ le_sup_left,d.residual_core]
  have hcP : C.pCoreIn 2 = P := by
    rw [pCoreIn_subgroupOf _ _ _ le_sup_right,d.local_core]
  let b := subgroupOfEquivOfLe (show outsideResidual H ≤ J from le_sup_left)
  let c := subgroupOfEquivOfLe (show f.Li 1 ≤ J from le_sup_right)
  let hcomm := source_factor_commutator_of_components d hK hL
  let qC := source_localRightProjection d hcomm
  let eC0 : ((f.Li 1) ⧸ pCore 2 (f.Li 1)) ≃* SL(2,d.pair_field.Carrier) :=
    (QuotientGroup.quotientMulEquivOfEq (source_localRightProjection_ker d hcomm).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qC (source_localRightProjection_surjective d hcomm))
  let eB : (B ⧸ pCore 2 B) ≃* SL(2,d.pair_field.Carrier) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans d.pair_natural.quotientEquiv
  let eC : (C ⧸ pCore 2 C) ≃* SL(2,d.pair_field.Carrier) :=
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans eC0
  let : IsSimpleGroup PSL(2,d.pair_field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [d.pair_field.card_eq,d.pair_degree]
      exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
        (Nat.pow_le_pow_right (by decide) S.nonbinary))
  let : IsSimpleGroup SL(2,d.pair_field.Carrier) :=
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := d.pair_field.Carrier)).isSimpleGroup
  obtain ⟨q,hq,hker,hfirst,hsecond,hbval,hcval⟩ :=
    marked_projection B C P hb hc hne hgen hbP hcP eB eC
  let e := d.pair_natural.matrixCoordinates d.pair_multiplicity
  let r : J →* MulAut (pairCore V H h) :=
    (pairCore V H h).normalizerMonoidHom.comp (inclusion hJG)
  have hbact (x : B) (p : pairCore V H h) :
      (e (r x p)).toAdd = ClassicalOrthogonal.FourPlusMatrix.matrixAction (q x) (e p).toAdd := by
    rw [hbval]
    change (e (r x p)).toAdd =
      (eB (QuotientGroup.mk' _ x)).val * (e p).toAdd * (1 : SL(2,d.pair_field.Carrier))⁻¹.val
    rw [inv_one]
    change (e (r x p)).toAdd = (eB (QuotientGroup.mk' _ x)).val * (e p).toAdd *
      (1 : Matrix (Fin 2) (Fin 2) d.pair_field.Carrier)
    rw [mul_one]
    exact d.pair_natural.matrixCoordinates_intertwines d.pair_multiplicity (b x) p
  have hcact (x : C) (p : pairCore V H h) :
      (e (r x p)).toAdd = ClassicalOrthogonal.FourPlusMatrix.matrixAction (q x) (e p).toAdd := by
    rw [hcval]
    change (e (r x p)).toAdd =
      (1 : Matrix (Fin 2) (Fin 2) d.pair_field.Carrier) * (e p).toAdd * (eC (QuotientGroup.mk' _ x))⁻¹.val
    rw [one_mul]
    exact source_localRightProjection_action d hcomm (c x) p
  refine ⟨{
    core_le := (source_pairCore_le_factors d).1.trans le_sup_left
    first_le := le_sup_left
    second_le := le_sup_right
    normalizes := hJG
    projection := q
    surjective := hq
    kernel := hker
    first_factor := hfirst
    second_factor := hsecond
    coordinates := e
    intertwines := ?_ }⟩
  intro y p
  obtain ⟨x,hx,z,hz,he⟩ := mem_sup_of_normal_right.mp (hgen ▸ mem_top y)
  change (e (r y p)).toAdd = _
  rw [← he,map_mul]
  change (e (r x (r z p))).toAdd = _
  rw [hbact ⟨x,hx⟩,hcact ⟨z,hz⟩,map_mul]
  exact (LinearEquiv.congr_fun
    (ClassicalOrthogonal.FourPlusMatrix.matrixHom.map_mul (q x) (q z)) (e p).toAdd).symm

/-- The marked orthogonal action is on the literal source join Y and P. -/
theorem source_orthogonal_marking_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    Nonempty (OrthogonalMarking (orthogonalJoin (f.Li 1) V h)
      (pairCore V H h) (outsideResidual H) (f.Li 1) d.pair_field) := by
  rw [(source_factorJoin_and_residual_of_components d hK hL).1]
  exact source_factorJoin_orthogonal_of_components d hK hL

/-- Source application: the determinant form is preserved by original conjugation. -/
theorem source_quadratic_invariance_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    ∃ a : OrthogonalMarking (orthogonalJoin (f.Li 1) V h)
        (pairCore V H h) (outsideResidual H) (f.Li 1) d.pair_field,
      d.pair_field.degree = S.field.degree ∧
      ∀ (y : orthogonalJoin (f.Li 1) V h) (p : pairCore V H h),
        a.quadraticValue ((pairCore V H h).normalizerMonoidHom
          (inclusion a.normalizes y) p) = a.quadraticValue p := by
  obtain ⟨a⟩ := source_orthogonal_marking_of_components d hK hL
  exact ⟨a,d.pair_degree,a.quadraticValue_conjugation⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
