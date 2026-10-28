module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Reduction
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupAction.ModelConjugation
public import Theory.ElementaryAbelian.Quotient

/-!
# The genuine starred action and point commutator in G.2.5

The natural model makes the kernel of the LT-action on V exactly O₂(LT):
the kernel on L is detected by the supplied SL₃-model, and LT/L is a
two-group. Consequently the original star quotient acts faithfully.

The Sylow supplement to the two-residual places the full N_L(V₁) in H,
so this full setwise point stabilizer normalizes U. Natural transitivity
makes it transitive on the nonidentity elements of V₁. The earlier
Frattini bound and U*≠1 therefore give [V,U]=V₁. The same Frattini bound
makes the actual U* elementary abelian. Its faithful action fixes the
marked line pointwise and has every displacement in that line.

The point-stabilizer comparison uses the given star/model map. It does
not replace the two-residual by a solvable residual or replace the full
setwise stabilizer by a pointwise local. Radical identification and
three-point generation remain separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.1–2 and G.2.5(1), printed pp.332,335, and the G.2.3 argument on p.333.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)
namespace Hypothesis
include d

theorem LT_normalizes_V : D.LT ≤ normalizer (D.V : Set G) :=
  sup_le (normalizes_of_span D d.span_eq) d.setup.T_normalizes_V

theorem pointNormalizer_le_H : D.L ⊓ D.G₁ ≤ D.H := by
  let L' := D.L.subgroupOf D.LT
  let : L'.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.L.le_normalizer d.setup.T_normalizes_L)
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal L'
  let e : L' ≃* D.L := subgroupOfEquivOfLe le_sup_left
  let QL : Sylow 2 D.L := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQL (x : D.L) : x ∈ (QL : Subgroup D.L) ↔ (x : G) ∈ D.T := by
    change x ∈ (Q : Subgroup L').map e.toMonoidHom ↔ _
    rw [mem_map_equiv, hQ]
    change (⟨x, mem_sup_left x.property⟩ : D.LT) ∈ (P : Subgroup D.LT) ↔ _
    constructor
    · intro hx
      exact hP ▸ mem_map_of_mem D.LT.subtype hx
    · intro hx
      exact (mem_map_iff_mem (f := D.LT.subtype) D.LT.subtype_injective).mp (hP.symm ▸ hx)
  let N := D.G₁.subgroupOf D.L
  have hQN : (QL : Subgroup D.L) ≤ N := by
    intro x hx
    exact d.setup.T_normalizes_point ((hQL x).mp hx)
  have hs := congrArg (fun A : Subgroup N => A.map N.subtype)
    (pResidual_sup_sylow_eq_top (QL.subtype hQN))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hs
  let eN : N ≃* (D.L ⊓ D.G₁ : Subgroup G) :=
    { toFun := fun x => ⟨x, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hR : ((pResidual 2 N).map N.subtype).map D.L.subtype = D.L₁ := by
    change _ = (pResidual 2 (D.L ⊓ D.G₁ : Subgroup G)).map (D.L ⊓ D.G₁).subtype
    rw [← map_pResidual_of_surjective 2 eN.toMonoidHom eN.surjective, Subgroup.map_map, Subgroup.map_map]
    rfl
  intro x hx
  have hxN : (⟨x, hx.1⟩ : D.L) ∈ N := hx.2
  rw [← hs] at hxN
  have hm := mem_map_of_mem D.L.subtype hxN
  rw [Subgroup.map_sup, hR] at hm
  apply (sup_le (le_sup_left.trans d.setup.local_le)
    (show (((QL.subtype hQN : Sylow 2 N) : Subgroup N).map N.subtype).map D.L.subtype ≤ D.H from ?_)) hm
  rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  exact (le_sup_right.trans d.setup.local_le) ((hQL z.val).mp hz)

theorem pointNormalizer_normalizes_U : D.L ⊓ D.G₁ ≤ normalizer (D.U : Set G) :=
  d.pointNormalizer_le_H.trans (le_normalizer_conjugateSpanBy _ _)

/-- Actual conjugation before passing to the star quotient. -/
def naturalAction : D.LT →* MulAut (Multiplicative (Fin 3 → F)) :=
  Theory.GroupAction.ModelConjugation.action D.LT D.V d.LT_normalizes_V d.coordinates

theorem naturalAction_apply (x : D.LT) (v : D.V) :
    d.naturalAction x (d.coordinates v) = d.coordinates
      ⟨(x : G) * v * (x : G)⁻¹,
        (mem_normalizer_iff.mp (d.LT_normalizes_V x.property) v).mp v.property⟩ := by
  change d.coordinates ((D.V.normalizerMonoidHom (inclusion d.LT_normalizes_V x)) (d.coordinates.symm (d.coordinates v))) = _
  rw [d.coordinates.symm_apply_apply]
  rfl

theorem naturalAction_on_L (l : D.L) (v : Fin 3 → F) :
    (d.naturalAction ⟨l, mem_sup_left l.property⟩ (Multiplicative.ofAdd v)).toAdd =
      (d.model (starProjection D l)).val *ᵥ v := by
  have he := d.naturalAction_apply ⟨l, mem_sup_left l.property⟩
    (d.coordinates.symm (Multiplicative.ofAdd v))
  rw [d.coordinates.apply_symm_apply] at he
  exact (congrArg Multiplicative.toAdd he).trans (by simpa using d.equivariant l (d.coordinates.symm (Multiplicative.ofAdd v)))

theorem naturalAction_core_le_ker : pCore 2 D.LT ≤ d.naturalAction.ker := by
  rw [naturalAction, Theory.GroupAction.ModelConjugation.action_ker]
  intro x hx
  exact d.LT_core_centralizes_V (show (x : G) ∈ D.LT.pCoreIn 2 from ⟨x, hx, rfl⟩)

private theorem naturalAction_ker_on_L (x : D.LT) (hx : (x : G) ∈ D.L)
    (hk : x ∈ d.naturalAction.ker) : x ∈ pCore 2 D.LT := by
  let l : D.L := ⟨x, hx⟩
  have he : d.model (starProjection D l) = 1 := by
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext v
    have hh := d.naturalAction_on_L l v
    have hx1 : d.naturalAction x = 1 := hk
    change (d.naturalAction x (Multiplicative.ofAdd v)).toAdd = _ at hh
    rw [hx1] at hh
    simpa using hh.symm
  have he' : starProjection D l = 1 := d.model.injective (he.trans d.model.map_one.symm)
  exact (QuotientGroup.eq_one_iff (N := pCore 2 D.LT) x).mp (congrArg Subtype.val he')

theorem naturalAction_ker : d.naturalAction.ker = pCore 2 D.LT := by
  apply le_antisymm _ d.naturalAction_core_le_ker
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  let L' := D.L.subgroupOf D.LT
  let : L'.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.L.le_normalizer d.setup.T_normalizes_L)
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  have hs : L' ⊔ (P : Subgroup D.LT) = ⊤ := by
    apply Subgroup.map_injective D.LT.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show D.L ≤ D.LT from le_sup_left), hP,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hp := isPGroup_quotient_of_sup_eq_top L' (P : Subgroup D.LT) P.isPGroup' hs
  intro x
  obtain ⟨k, hk⟩ := hp (QuotientGroup.mk' L' x.val)
  have hL : ((x.val ^ 2 ^ k : D.LT) : G) ∈ D.L := by
    change x.val ^ 2 ^ k ∈ L'
    apply (QuotientGroup.eq_one_iff (N := L') _).mp
    change (QuotientGroup.mk' L') (x.val ^ 2 ^ k) = 1
    simpa only [map_pow] using hk
  have hC := d.naturalAction_ker_on_L (x.val ^ 2 ^ k) hL
    (d.naturalAction.ker.pow_mem x.property _)
  obtain ⟨j, hj⟩ := (show IsPGroup 2 (pCore 2 D.LT) from pCore_isPGroup)
    ⟨x.val ^ 2 ^ k, hC⟩
  refine ⟨k + j, ?_⟩
  apply Subtype.ext
  have hj' := congrArg Subtype.val hj
  simpa only [coe_pow, coe_one, ← pow_mul, ← pow_add] using hj'


/-- Conjugation on the natural module, through the original star quotient. -/
def starAction : D.Star →* MulAut (Multiplicative (Fin 3 → F)) :=
  QuotientGroup.lift (pCore 2 D.LT) d.naturalAction d.naturalAction_core_le_ker

theorem starAction_injective : Function.Injective d.starAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [starAction, QuotientGroup.ker_lift, d.naturalAction_ker]
  exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])

theorem starAction_mk (x : D.LT) :
    d.starAction (QuotientGroup.mk' (pCore 2 D.LT) x) = d.naturalAction x := rfl

theorem commutator_V_U_le_point (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : ⁅D.V, D.U⁆ ≤ D.V₁ :=
  (commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans
    (derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf)

private theorem coord_ne_zero (v : D.V) (hv : (v : G) ≠ 1) :
    (d.coordinates v).toAdd ≠ 0 := by
  intro he
  apply hv
  exact congrArg Subtype.val (d.coordinates.injective (he.trans d.coordinates.map_one.symm))

/-- The actual point normalizer is transitive on the nonidentity elements of
V₁, including over the binary field. -/
theorem pointNormalizer_transitive (a b : G) (ha : a ∈ D.V₁) (hb : b ∈ D.V₁)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ l ∈ D.L ⊓ D.G₁, l * a * l⁻¹ = b := by
  let aV : D.V := ⟨a, d.setup.point_le ha⟩
  let bV : D.V := ⟨b, d.setup.point_le hb⟩
  have ha0 := d.coord_ne_zero aV ha1
  have hb0 := d.coord_ne_zero bV hb1
  obtain ⟨s, hs⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ ha0 hb0
  obtain ⟨l, hl⟩ := (d.model.surjective.comp (starProjection_surjective D)) s
  change d.model (starProjection D l) = s at hl
  have hla : (l : G) * a * (l : G)⁻¹ = b := by
    have he := (d.equivariant l aV).trans (by simpa only [hl] using hs)
    exact congrArg Subtype.val (d.coordinates.injective he)
  refine ⟨l, ⟨l.property, ?_⟩, hla⟩
  apply mem_normalizer_fintype
  intro w hw
  let wV : D.V := ⟨w, d.setup.point_le hw⟩
  have hca := (d.point_mem aV).mp ha
  have hcw := (d.point_mem wV).mp hw
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one d.point_dimension
    (show (⟨(d.coordinates aV).toAdd, hca⟩ : d.point) ≠ 0 from
      fun he => ha0 (congrArg Subtype.val he))
    (⟨(d.coordinates wV).toAdd, hcw⟩ : d.point)
  have hc' : c • (d.coordinates aV).toAdd = (d.coordinates wV).toAdd :=
    congrArg Subtype.val hc
  have hv := (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) w).mp wV.property
  apply (d.point_mem ⟨(l : G) * w * (l : G)⁻¹, hv⟩).mpr
  rw [d.equivariant l wV, ← hc', Matrix.mulVec_smul, hl, hs]
  exact d.point.smul_mem c ((d.point_mem bV).mp hb)

theorem commutator_V_U_ne_bot : ⁅D.V, D.U⁆ ≠ ⊥ := by
  intro he
  have hc : D.U ≤ centralizer (D.V : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  apply d.star_U_ne_bot
  apply le_antisymm _ bot_le
  rintro _ ⟨u, hu, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [← d.naturalAction_ker, naturalAction, Theory.GroupAction.ModelConjugation.action_ker]
  exact hc hu

/-- The commutator clause of G.2.5(1), without a radical-identification premise. -/
theorem commutator_V_U_eq_point (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : ⁅D.V, D.U⁆ = D.V₁ := by
  have hle := d.commutator_V_U_le_point hUT hf
  apply le_antisymm hle
  obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp (d.commutator_V_U_ne_bot)
  intro b hb
  by_cases hb1 : b = 1
  · simpa only [hb1] using (⁅D.V, D.U⁆ : Subgroup G).one_mem
  obtain ⟨l, hl, he⟩ := d.pointNormalizer_transitive a b (hle a.property) hb
    (fun he => ha (Subtype.ext he)) hb1
  have hV : D.V.map (MulAut.conj l).toMonoidHom = D.V :=
    mem_normalizer_iff_map_conj_eq.mp (normalizes_of_span D d.span_eq hl.1)
  have hU : D.U.map (MulAut.conj l).toMonoidHom = D.U :=
    mem_normalizer_iff_map_conj_eq.mp (d.pointNormalizer_normalizes_U hl)
  have hm := mem_map_of_mem (MulAut.conj l).toMonoidHom a.property
  rw [map_commutator, hV, hU] at hm
  exact he ▸ hm


/-- The normal natural two-module is contained in the actual star kernel. -/
theorem V_le_LT_core : D.V ≤ D.LT.pCoreIn 2 := by
  let := d.setup.elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.V)
    (d.setup.V_le_T.trans le_sup_right) d.LT_normalizes_V

/-- The star map restricted to U, without any generation hypothesis. -/
def UStarProjection (D : Setup G) (hUT : D.U ≤ D.T) : D.U →* D.star D.U :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp
    (inclusion (hUT.trans le_sup_right))).codRestrict _
      (fun u => ⟨⟨u, (hUT.trans le_sup_right) u.property⟩, u.property, rfl⟩)

omit d [Field F] [Finite F] [Finite G] in
theorem UStarProjection_surjective (hUT : D.U ≤ D.T) :
    Function.Surjective (UStarProjection D hUT) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Elementarity follows directly from the earlier Frattini bound. -/
theorem star_U_elementary (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : IsElementaryAbelian 2 (D.star D.U) := by
  let : Fact (IsPGroup 2 D.U) := ⟨d.U_isPGroup hUT⟩
  let : IsElementaryAbelian 2 (D.U ⧸ frattini D.U) := isElementaryAbelian_quotient_frattini
  have hker : frattini D.U ≤ (UStarProjection D hUT).ker := by
    intro u hu
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    have hk := d.V_le_LT_core (d.setup.point_le (hf (mem_map_of_mem D.U.subtype hu)))
    obtain ⟨v, hv, he⟩ := hk
    exact (show v = inclusion (hUT.trans le_sup_right) u from Subtype.ext he) ▸ hv
  exact IsElementaryAbelian.of_surjective
    (QuotientGroup.lift (frattini D.U) (UStarProjection D hUT) hker)
    (QuotientGroup.lift_surjective_of_surjective (frattini D.U) _ (UStarProjection_surjective hUT) hker)

/-- Each starred U-actor fixes the marked F-line pointwise. -/
theorem starAction_U_fixes_point (u : D.Star) (hu : u ∈ D.star D.U)
    (v : Fin 3 → F) (hv : v ∈ d.point) :
    d.starAction u (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
  obtain ⟨x, hx, rfl⟩ := hu
  let w := d.coordinates.symm (Multiplicative.ofAdd v)
  have hw : (w : G) ∈ D.V₁ := (d.point_mem w).mpr (by simpa [w] using hv)
  have hc := d.setup.toBaseHypothesis.U_le_centralizer_point hx _ hw
  change (w : G) * (x : G) = (x : G) * w at hc
  have he : (x : G) * w * (x : G)⁻¹ = w := by rw [← hc, mul_inv_cancel_right]
  rw [d.starAction_mk]
  have hact := d.naturalAction_apply x w
  have hsame : (⟨(x : G) * w * (x : G)⁻¹,
      (mem_normalizer_iff.mp (d.LT_normalizes_V x.property) w).mp w.property⟩ : D.V) = w :=
    Subtype.ext he
  rw [hsame] at hact
  simpa [w] using hact

/-- The actual starred action is trivial modulo the marked F-line. -/
theorem starAction_U_displacement (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (u : D.Star) (hu : u ∈ D.star D.U) (v : Fin 3 → F) :
    (d.starAction u (Multiplicative.ofAdd v)).toAdd - v ∈ d.point := by
  obtain ⟨x, hx, rfl⟩ := hu
  let w := d.coordinates.symm (Multiplicative.ofAdd v)
  have hw : (x : G) * w * (x : G)⁻¹ ∈ D.V :=
    (mem_normalizer_iff.mp (d.LT_normalizes_V x.property) w).mp w.property
  let y : D.V := ⟨(x : G) * w * (x : G)⁻¹, hw⟩
  have hc : (y * w⁻¹ : D.V).val ∈ D.V₁ := by
    apply d.commutator_V_U_le_point hUT hf
    rw [commutator_comm]
    exact commutator_mem_commutator hx w.property
  have hp := (d.point_mem (y * w⁻¹)).mp hc
  rw [map_mul, map_inv] at hp
  have hact := d.naturalAction_apply x w
  change d.naturalAction x (d.coordinates w) = d.coordinates y at hact
  rw [d.starAction_mk]
  change (d.naturalAction x (Multiplicative.ofAdd v)).toAdd - v ∈ d.point
  rw [toAdd_mul, toAdd_inv, ← sub_eq_add_neg] at hp
  rw [← hact] at hp
  simpa only [w, d.coordinates.apply_symm_apply, toAdd_ofAdd] using hp


/-- The coordinate model identifies the full setwise point stabilizer,
not just the pointwise local subgroup. -/
theorem model_mem_pointStabilizer_iff (l : D.L) :
    d.model (starProjection D l) ∈
      MulAction.stabilizer SL(3,F) (d.point : Set (Fin 3 → F)) ↔ (l : G) ∈ D.G₁ := by
  rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 3 → F⦄, v ∈ d.point →
    (d.model (starProjection D l)).val *ᵥ v ∈ d.point) ↔ _
  constructor
  · intro hl
    apply mem_normalizer_fintype
    intro w hw
    have hwV := d.setup.point_le hw
    have he := d.equivariant l ⟨w, hwV⟩
    apply (d.point_mem ⟨(l : G) * w * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) w).mp hwV⟩).mpr
    rw [he]
    exact hl ((d.point_mem ⟨w, hwV⟩).mp hw)
  · intro hl v hv
    let w := d.coordinates.symm (Multiplicative.ofAdd v)
    have hw : (w : G) ∈ D.V₁ := (d.point_mem w).mpr (by simpa [w] using hv)
    have hc := (mem_normalizer_iff.mp hl w).mp hw
    have hp := (d.point_mem ⟨(l : G) * w * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) w).mp w.property⟩).mp hc
    rw [d.equivariant l w] at hp
    simpa only [w, d.coordinates.apply_symm_apply, toAdd_ofAdd] using hp

/-- The literal star image of N_L(V₁), transported by the supplied model. -/
theorem pointNormalizer_model :
    ((D.star (D.L ⊓ D.G₁)).subgroupOf (D.star D.L)).map d.model.toMonoidHom =
      MulAction.stabilizer SL(3,F) (d.point : Set (Fin 3 → F)) := by
  ext s
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, hx, he⟩ := hq
    let l : D.L := ⟨x, hx.1⟩
    have hq' : starProjection D l = q := Subtype.ext he
    rw [← hq']
    exact (d.model_mem_pointStabilizer_iff l).mpr hx.2
  · intro hs
    obtain ⟨l, hl⟩ := (d.model.surjective.comp (starProjection_surjective D)) s
    change d.model (starProjection D l) = s at hl
    have hx : (l : G) ∈ D.G₁ := (d.model_mem_pointStabilizer_iff l).mp (hl.symm ▸ hs)
    exact ⟨starProjection D l,
      ⟨⟨l, mem_sup_left l.property⟩, ⟨l.property, hx⟩, rfl⟩, hl⟩


/-- The starred L is normal in the original star quotient. -/
theorem star_L_normal : (D.star D.L).Normal := by
  let : (D.L.subgroupOf D.LT).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.L.le_normalizer d.setup.T_normalizes_L)
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

/-- On the actual starred L, the quotient action is the supplied natural model. -/
theorem starAction_on_L (l : D.star D.L) (v : Fin 3 → F) :
    (d.starAction l (Multiplicative.ofAdd v)).toAdd = (d.model l).val *ᵥ v := by
  obtain ⟨x, rfl⟩ := starProjection_surjective D l
  exact d.naturalAction_on_L x v

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
