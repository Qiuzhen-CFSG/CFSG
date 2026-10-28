module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.PointFixerModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstTwentyFive
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# Point-centralizing Sylow elements on the original natural quotient

Conjugation by the original Sylow subgroup is transported through the chosen
projection V → V/C_V(L), with the literal automorphism of L/O₂(L).
If a Sylow element centralizes V₁, it fixes the corresponding field line.
The three natural-model normalizer calculations identify its binary operator
with an actual natural group element fixing that same line pointwise.
The resulting conjugation formula retains the original quotient map on L.

The PSL₂(25) consumer combines this conclusion with the previously constructed
outer witness on L₁/O₂(L₁). The residual lift in PointResidual supplies the
remaining contradiction; innerness on L/O₂(L) alone does not assert it.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
proof of 11.1.2, printed p.762.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

private theorem sylow_intertwines (t : T) (l : L) (v : c.Space) :
    c.sylowAction S t (c.modelAction (c.quotientMap l) v) =
      c.modelAction (c.quotientMap (L.normalizerMonoidHom
        (inclusion D.sylow_normalizes_component t) l)) (c.sylowAction S t v) := by
  obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  have hv : (c.projection w).toAdd = v := congrArg Multiplicative.toAdd hw
  change c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes t
    (c.modelAction (c.quotientMap l) v) =
      c.modelAction (c.quotientMap (L.normalizerMonoidHom
        (inclusion D.sylow_normalizes_component t) l))
        (c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes t v)
  rw [← hv,← c.projection_component_conjugation,
    c.conjugationAction_projection D.sylow_normalizes_component S.sylow_normalizes,
    c.conjugationAction_projection D.sylow_normalizes_component S.sylow_normalizes,
    ← c.projection_component_conjugation]
  congr 2
  apply Subtype.ext
  change (t : G) * ((l : G) * (w : G) * (l : G)⁻¹) * (t : G)⁻¹ =
    ((t : G) * (l : G) * (t : G)⁻¹) * ((t : G) * (w : G) * (t : G)⁻¹) *
      ((t : G) * (l : G) * (t : G)⁻¹)⁻¹
  group

private theorem fixes_point_coordinates (t : T)
    (ht : (t : G) ∈ centralizer (f.Vi 0 : Set G)) :
    ∀ v ∈ f.space 0, c.sylowAction S t v = v := by
  intro v hv
  obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  have hv' : (c.projection w).toAdd = v := congrArg Multiplicative.toAdd hw
  have hwV : (w : G) ∈ f.Vi 0 := (c.mem_preimage _ w).mpr (by
    change (c.projection w).toAdd ∈ f.space 0
    rwa [hv'])
  rw [← hv']
  change c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes t _ = _
  rw [c.conjugationAction_projection]
  congr 2
  apply Subtype.ext
  change (t : G) * (w : G) * (t : G)⁻¹ = w
  exact mul_inv_eq_iff_eq_mul.mpr (ht w hwV).symm

private theorem model_faithful (c : Coordinates D S.field) :
    Function.Injective c.modelAction := by
  cases c with
  | sl3 m =>
    intro g h he
    apply Subtype.ext
    ext i j
    have hh := congrFun (LinearMap.congr_fun he (Pi.single j 1)) i
    change specialLinearNatural 3 g (Pi.single j 1) i =
      specialLinearNatural 3 h (Pi.single j 1) i at hh
    change (g.val.mulVec (Pi.single j 1)) i = (h.val.mulVec (Pi.single j 1)) i at hh
    simpa [Matrix.mulVec_single] using hh
  | sp4 m =>
    intro g h he
    apply SymplecticNaturalNormalizer.naturalHom_injective
    exact LinearEquiv.ext (fun v => LinearMap.congr_fun he v)
  | g2 m => exact Atlas.G2.Natural.action_injective _

/-- A point-centralizing original Sylow element is the natural operator of an
actual model element, fixing the same line and inducing the literal quotient action. -/
theorem point_centralizing_sylow_model_operator (t : T)
    (ht : (t : G) ∈ centralizer (f.Vi 0 : Set G)) :
    ∃ g : c.ModelGroup, (∀ v, c.sylowAction S t v = c.modelAction g v) ∧
      (∀ v ∈ f.space 0, c.modelAction g v = v) ∧
      (∀ l : L, c.quotientMap (L.normalizerMonoidHom
        (inclusion D.sylow_normalizes_component t) l) = g * c.quotientMap l * g⁻¹) := by
  let α := (MulAut.congr c.groupEquiv)
    (Closure.coreQuotientAction L (inclusion D.sylow_normalizes_component t))
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv ((c.sylowAction S).asGroupHom t)
  have he : ∀ g v, e (c.modelAction g v) = c.modelAction (α g) (e v) := by
    intro g v
    obtain ⟨l,rfl⟩ := c.quotientMap_surjective g
    have ha : α (c.quotientMap l) = c.quotientMap
        (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t) l) := by
      change c.groupEquiv (Closure.coreQuotientAction L _
        (c.groupEquiv.symm (c.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)))) = _
      rw [c.groupEquiv.symm_apply_apply,Closure.coreQuotientAction_apply_mk]
      rfl
    rw [ha]
    exact sylow_intertwines D S t l v
  have hf : ∀ v ∈ f.space 0, e v = v := fixes_point_coordinates D S f t ht
  obtain ⟨k,hk⟩ := T.isPGroup' t
  have hep : e ^ (2 ^ k) = 1 := by
    have hh := congrArg (c.sylowAction S).asGroupHom hk
    rw [map_pow,map_one] at hh
    apply LinearEquiv.ext
    intro v
    have heq (n : ℕ) (w : c.Space) :
        (e ^ n) w = (((c.sylowAction S).asGroupHom t) ^ n).val w := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ',pow_succ']
        change e ((e ^ n) w) = c.sylowAction S t _
        rw [ih]
        rfl
    rw [heq,hh]
    rfl
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) S.nonbinary
  have hex : ∃ g : c.ModelGroup, ∀ v, e v = c.modelAction g v := by
    cases c with
    | sl3 m => exact PointFixer.sl3_operator α e he (f.space 0) (f.space_ne_bot 0) hf hep
    | sp4 m => exact PointFixer.sp4_operator hq α e he (f.space 0) (f.space_ne_bot 0) hf hep
    | g2 m =>
      let : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra S.field.Carrier 2
      let a' : Atlas.G2.Natural.Space S.field.Carrier ≃+
          Atlas.G2.Natural.Space S.field.Carrier := e.toAddEquiv
      let e' : Atlas.G2.Natural.Space S.field.Carrier ≃ₗ[ZMod 2]
          Atlas.G2.Natural.Space S.field.Carrier :=
        { a' with map_smul' := ZMod.map_smul a' }
      have hep' : e' ^ (2 ^ k) = 1 := by
        apply LinearEquiv.ext
        intro v
        have heq (n : ℕ) : (e' ^ n) v = (e ^ n) v := by
          induction n with
          | zero => rfl
          | succ n ih =>
            rw [pow_succ',pow_succ']
            change e ((e' ^ n) v) = e ((e ^ n) v)
            rw [ih]
        rw [heq,hep]
        rfl
      exact PointFixer.g2_operator hq α e' he (f.space 0) (f.space_ne_bot 0) hf hep'
  obtain ⟨g,hg⟩ := hex
  refine ⟨g,hg,(fun v hv => (hg v).symm.trans (hf v hv)),?_⟩
  intro l
  apply model_faithful D S c
  apply LinearMap.ext
  intro v
  obtain ⟨v,rfl⟩ := (c.modelAction.apply_bijective g).surjective v
  have hh := sylow_intertwines D S t l v
  change e (c.modelAction (c.quotientMap l) v) =
    c.modelAction (c.quotientMap (L.normalizerMonoidHom
      (inclusion D.sylow_normalizes_component t) l)) (e v) at hh
  rw [hg,hg] at hh
  rw [← hh]
  simp only [← Module.End.mul_apply,← map_mul,inv_mul_cancel_right]

/-- The induced automorphism on the original component quotient is inner. -/
theorem point_centralizing_sylow_inner_on_component (t : T)
    (ht : (t : G) ∈ centralizer (f.Vi 0 : Set G)) :
    Closure.coreQuotientAction L (inclusion D.sylow_normalizes_component t) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  obtain ⟨g,_,_,ha⟩ := point_centralizing_sylow_model_operator D S f t ht
  refine ⟨c.groupEquiv.symm g,?_⟩
  ext x : 1
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
  apply c.groupEquiv.injective
  rw [Closure.coreQuotientAction_apply_mk,MulAut.conj_apply,map_mul,map_mul,map_inv,
    c.groupEquiv.apply_symm_apply]
  exact (ha l).symm

/-- The PSL₂(25) witness is inner on the original natural component quotient
but outer on the first local residual quotient. -/
theorem first_twentyFive_inner_outer_witness
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25) :
    ∃ t : T, (t : G) ∈ K ∧ (t : G) ∈ centralizer (f.Vi 0 : Set G) ∧
      Closure.coreQuotientAction L (inclusion D.sylow_normalizes_component t) ∈
        MulAut.innerSubgroup (L ⧸ pCore 2 L) ∧
      Closure.coreQuotientAction (f.Li 0) ⟨t,f.sylow_normalizes_Li 0 t.property⟩ ∉
        MulAut.innerSubgroup (f.Li 0 ⧸ pCore 2 (f.Li 0)) := by
  obtain ⟨t,ht,htK,htfix,hout⟩ :=
    first_twentyFive_outer_centralizes_point D S f hm hfour hfix hK hLK hk
  exact ⟨⟨t,ht⟩,htK,htfix,point_centralizing_sylow_inner_on_component D S f ⟨t,ht⟩ htfix,hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
