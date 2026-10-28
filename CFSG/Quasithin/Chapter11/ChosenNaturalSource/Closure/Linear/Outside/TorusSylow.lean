module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Natural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Flag
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Setup
public import Theory.Representation.SL3OddNaturalNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Odd
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Quotients
public import Mathlib.Algebra.CharP.Reduced
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Even
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import Theory.GroupTheory.Hall.OddNormalProducts

/-!
# Marked SL₃ torus and Sylow geometry for the outside-H argument

For even field degree, the kernel X₀ of the original Cartan on L/O₂(L)
is identified with the full scalar center of the marked SL₃. It has order
three, lies in the original X₁, and satisfies the ambient equality [W,X₀]=V.
For odd degree, the original Sylow action and its actual kernel give T=T_L;
lifting two-elements through the marked point-parabolic residual gives T∩L≤K.

The final theorems apply both results to the original selected H. The even
application retains the independent abelianness input for the actual action
image on W/V₁. The block conclusions are the explicit authorized inputs;
full source assembly remains with the outside-H consumer.

Source: Aschbacher–Smith, 11.5.7, refs/quasithin.pdf, printed p.782.
-/

/-!
# The actual odd-degree Sylow action

Conjugation by the original T normalizes the marked binary natural SL₃
image. The intrinsic odd-index normalizer theorem puts this two-group
image inside SL₃. Maximality of the image of T∩L then supplies inner
representatives in that same intersection. The kernel is proved to be
C_T(V), using injectivity of the original coordinate projection on V;
the preceding source equality C_T(V)=O₂(LT) gives T=T_L.

No faithfulness of the ambient action is assumed. Source: Aschbacher–Smith,
11.5.7, refs/quasithin.pdf, printed p.782, odd-degree ending.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
include m

private theorem action_compatibility (t : T) (l : L) (v : (Coordinates.sl3 m).Space) :
    (Coordinates.sl3 m).sylowAction S t
      (specialLinearNatural 3 ((Coordinates.sl3 m).quotientMap l) v) =
    specialLinearNatural 3 ((Coordinates.sl3 m).quotientMap
      (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t) l))
      ((Coordinates.sl3 m).sylowAction S t v) := by
  let c := Coordinates.sl3 m
  obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  have hv : (c.projection w).toAdd = v := congrArg Multiplicative.toAdd hw
  change c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes t
    (c.modelAction (c.quotientMap l) v) =
    c.modelAction (c.quotientMap (L.normalizerMonoidHom
      (inclusion D.sylow_normalizes_component t) l))
      (c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes t v)
  rw [← hv, ← c.projection_component_conjugation,
    c.conjugationAction_projection D.sylow_normalizes_component S.sylow_normalizes,
    c.conjugationAction_projection D.sylow_normalizes_component S.sylow_normalizes,
    ← c.projection_component_conjugation]
  congr 2
  apply Subtype.ext
  change (t : G) * ((l : G) * (w : G) * (l : G)⁻¹) * (t : G)⁻¹ =
    ((t : G) * (l : G) * (t : G)⁻¹) * ((t : G) * (w : G) * (t : G)⁻¹) *
      ((t : G) * (l : G) * (t : G)⁻¹)⁻¹
  group

theorem sylowAction_normalizes_naturalImage :
    ((Coordinates.sl3 m).sylowAction S).asGroupHom.range ≤
      SL3OddNaturalNormalizer.normalizer S.field.Carrier := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨t,rfl⟩ _ ⟨g,rfl⟩
  obtain ⟨l,rfl⟩ := (Coordinates.sl3 m).quotientMap_surjective g
  refine ⟨(Coordinates.sl3 m).quotientMap
    (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t) l), ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro v
  change specialLinearNatural 3 _ v =
    (Coordinates.sl3 m).sylowAction S t
      (specialLinearNatural 3 _ ((Coordinates.sl3 m).sylowAction S t⁻¹ v))
  rw [action_compatibility]
  have he : (Coordinates.sl3 m).sylowAction S t
      ((Coordinates.sl3 m).sylowAction S t⁻¹ v) = v := by
    have hh : (Coordinates.sl3 m).sylowAction S t *
        (Coordinates.sl3 m).sylowAction S t⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact LinearMap.congr_fun hh v
  exact congrArg (specialLinearNatural 3 _) he.symm

theorem sylowAction_inner (hodd : Odd S.field.degree) :
    ((Coordinates.sl3 m).sylowAction S).asGroupHom.range ≤
      SL3OddNaturalNormalizer.naturalImage S.field.Carrier := by
  let α : T →* SL3OddNaturalNormalizer.BinaryGL S.field.Carrier :=
    ((Coordinates.sl3 m).sylowAction S).asGroupHom
  change α.range ≤ SL3OddNaturalNormalizer.naturalImage S.field.Carrier
  apply SL3OddNaturalNormalizer.two_subgroup_le_naturalImage _ S.field.degree_pos hodd
    S.field.card_eq _
  · exact T.isPGroup'.of_surjective α.rangeRestrict α.rangeRestrict_surjective
  · exact sylowAction_normalizes_naturalImage D S m

theorem sylowAction_eq_natural (l : L) (hl : (l : G) ∈ (T : Subgroup G)) :
    ((Coordinates.sl3 m).sylowAction S).asGroupHom ⟨l,hl⟩ =
      (SL3OddNaturalNormalizer.binaryNatural S.field.Carrier).asGroupHom
        ((Coordinates.sl3 m).quotientMap l) := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  obtain ⟨w,hw⟩ := (Coordinates.sl3 m).projection_surjective (Multiplicative.ofAdd v)
  have hv : ((Coordinates.sl3 m).projection w).toAdd = v := congrArg Multiplicative.toAdd hw
  change (Coordinates.sl3 m).sylowAction S ⟨l,hl⟩ v = specialLinearNatural 3 _ v
  rw [← hv, Coordinates.sylowAction, Coordinates.conjugationAction_projection]
  exact (Coordinates.sl3 m).projection_component_conjugation l w

/-- The original Sylow-action kernel is the actual ambient centralizer of V. -/
theorem sylowAction_kernel (t : T) :
    t ∈ ((Coordinates.sl3 m).sylowAction S).asGroupHom.ker ↔
      (t : G) ∈ centralizer (V : Set G) := by
  constructor
  · intro ht v hv
    have he := LinearMap.congr_fun (congrArg Units.val (MonoidHom.mem_ker.mp ht))
      (((Coordinates.sl3 m).projection ⟨v,hv⟩).toAdd)
    change (Coordinates.sl3 m).sylowAction S t _ = _ at he
    rw [Coordinates.sylowAction, Coordinates.conjugationAction_projection] at he
    have hh := LocalGeometry.SL3.projection_injective D S m
      (congrArg Multiplicative.ofAdd he)
    have hc := congrArg Subtype.val hh
    change (t : G) * v * (t : G)⁻¹ = v at hc
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro ht
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := (Coordinates.sl3 m).projection_surjective (Multiplicative.ofAdd v)
    have hv : ((Coordinates.sl3 m).projection w).toAdd = v := congrArg Multiplicative.toAdd hw
    change (Coordinates.sl3 m).sylowAction S t v = v
    rw [← hv, Coordinates.sylowAction, Coordinates.conjugationAction_projection]
    congr 2
    apply Subtype.ext
    change (t : G) * (w : G) * (t : G)⁻¹ = (w : G)
    exact mul_inv_eq_iff_eq_mul.mpr (ht w w.property).symm

/-- Odd field degree puts the original Sylow inside its inner action times its kernel. -/
theorem sylow_eq_sourceTL (hodd : Odd S.field.degree) :
    (T : Subgroup G) = sourceTL T L := by
  let α := ((Coordinates.sl3 m).sylowAction S).asGroupHom
  let β := (SL3OddNaturalNormalizer.binaryNatural S.field.Carrier).asGroupHom
  let P := α.range.comap β
  have hP : IsPGroup 2 P := (T.isPGroup'.of_surjective α.rangeRestrict α.rangeRestrict_surjective).comap_of_injective β
    (SL3OddNaturalNormalizer.binaryNatural_asGroupHom_injective _)
  have hSP : (LocalGeometry.SL3.innerSylow D S m : Subgroup _) ≤ P := by
    rw [LocalGeometry.SL3.innerSylow_eq]
    rintro _ ⟨l,hl,rfl⟩
    exact ⟨⟨l,hl⟩, sylowAction_eq_natural D S m l hl⟩
  have heP : P = (LocalGeometry.SL3.innerSylow D S m : Subgroup _) :=
    (LocalGeometry.SL3.innerSylow D S m).is_maximal' hP hSP
  apply le_antisymm
  · intro t ht
    obtain ⟨g,hg⟩ := sylowAction_inner D S m hodd (show α ⟨t,ht⟩ ∈ α.range from ⟨_,rfl⟩)
    have hgP : g ∈ P := ⟨⟨t,ht⟩,hg.symm⟩
    rw [heP,LocalGeometry.SL3.innerSylow_eq] at hgP
    obtain ⟨l,hl,he⟩ := hgP
    have hat : α (⟨l,hl⟩ : T) = α (⟨t,ht⟩ : T) := by
      rw [sylowAction_eq_natural D S m l hl,he]
      exact hg
    have hk : (⟨l,hl⟩ : T)⁻¹ * ⟨t,ht⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hat,inv_mul_cancel]
    have hq : (l : G)⁻¹ * t ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      rw [← WeakClosure.seed_sylow_centralizer D S]
      exact ⟨T.mul_mem (T.inv_mem hl) ht, (sylowAction_kernel D S m _).mp hk⟩
    refine ⟨ht, ?_⟩
    have hm := (L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
      (mem_sup_left l.property) (mem_sup_right hq)
    change t ∈ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2
    simpa only [mul_inv_cancel_left] using hm
  · exact inf_le_left

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow

/-!
# The inner Sylow in the original point residual

A two-element of a proper SL₃ parabolic acts trivially on its scalar
quotient: Frobenius is injective in characteristic two. The checked
parabolic residual calculation therefore places that element in the
solvable residual. Apply this to the original marked point projection,
lift through its surjective residual map, and absorb the difference
in O₂(L)=V≤O₂(K). This proves T∩L≤K without identifying it with O₂(K).

Source: Aschbacher–Smith, 11.5.7, refs/quasithin.pdf, printed p.782.
The block outputs are explicit authorized inputs.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow
open LocalGeometry Matrix Matrix.PSL3.LinearThree

private def pointScalar (F : Type*) [Field F] [Finite F] : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]

private def lineScalar (F : Type*) [Field F] [Finite F] : lineParabolicSL F →* F where
  toFun g := g.val.val 2 2
  map_one' := by simp
  map_mul' g h := by
    have hg := (mem_lineParabolicSL_iff F g).mp g.property
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2]

private theorem point_two_element_mem_residual (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (a : pointParabolicSL F) {n : ℕ} (ha : a ^ (2^n) = 1) :
    a ∈ solvableResidual (pointParabolicSL F) := by
  have hs : pointScalar F a = 1 := by
    apply iterateFrobenius_inj F 2 n
    change (pointScalar F a) ^ (2^n) = 1 ^ (2^n)
    rw [← map_pow, ha, map_one, one_pow]
  have hp : (a : SL(3,F)) ∈ pointLocalSL F :=
    (mem_pointLocalSL_iff F a).mpr ⟨hs, (mem_pointParabolicSL_iff F a).mp a.property⟩
  rw [← pointParabolicSL_residual F hF] at hp
  obtain ⟨b,hb,he⟩ := hp
  exact (Subtype.ext he : b = a) ▸ hb

private theorem line_two_element_mem_residual (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (a : lineParabolicSL F) {n : ℕ} (ha : a ^ (2^n) = 1) :
    a ∈ solvableResidual (lineParabolicSL F) := by
  have hs : lineScalar F a = 1 := by
    apply iterateFrobenius_inj F 2 n
    change (lineScalar F a) ^ (2^n) = 1 ^ (2^n)
    rw [← map_pow, ha, map_one, one_pow]
  have hp := (mem_lineParabolicSL_iff F a).mp a.property
  have hl : (a : SL(3,F)) ∈ lineLocalSL F :=
    (mem_lineLocalSL_iff F a).mpr ⟨hp.1, hp.2, hs⟩
  rw [← lineParabolicSL_residual F hF] at hl
  obtain ⟨b,hb,he⟩ := hl
  exact (Subtype.ext he : b = a) ▸ hb

/-- A two-element of any genuine proper SL₃ parabolic lies in its solvable residual. -/
theorem parabolic_two_element_mem_residual (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (U : Submodule F (Fin 3 → F)) (hU : U ≠ ⊥) (hUt : U ≠ ⊤)
    (a : HigherLinear.parabolicSL U) {n : ℕ} (ha : a ^ (2^n) = 1) :
    a ∈ solvableResidual (HigherLinear.parabolicSL U) := by
  rcases Matrix.PSL3.LinearThree.SubspaceTransport.exists_parabolic_equiv U hU hUt with h | h
  · obtain ⟨e⟩ := h
    have hp := point_two_element_mem_residual F hF (e a)
      (by rw [← map_pow,ha,map_one])
    have hh := map_solvableResidual_le e.symm.toMonoidHom (mem_map_of_mem _ hp)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hh
  · obtain ⟨e⟩ := h
    have hp := line_two_element_mem_residual F hF (e a)
      (by rw [← map_pow,ha,map_one])
    have hh := map_solvableResidual_le e.symm.toMonoidHom (mem_map_of_mem _ hp)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hh

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (f : InvariantFlag (.sl3 m))

/-- The actual inner Sylow lies in K; no identification with O₂(K) is used. -/
theorem sylow_intersection_le_K
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace (f.space 0))
    (hKL : E.K = E.L₁) (hcore : L.pCoreIn 2 = V)
    (hW : E.W = E.K.pCoreIn 2) : (T : Subgroup G) ⊓ L ≤ E.K := by
  let c := Coordinates.sl3 m
  let U := f.space 0
  have hV : V ≤ E.K := (le_conjugateSpanBy V E.G₁).trans (hW.le.trans (pCoreIn_le 2 _))
  have hP : E.V₁ = c.preimage U := by
    change D.centralQuotientPreimage E.point = D.centralQuotientPreimage _
    rw [hpoint]
  have hR : E.L₁ = localResidual L (c.preimage U) := by
    change residualIn (L ⊓ normalizer (E.V₁ : Set G)) = _
    rw [hP]
    rfl
  have hF : 4 ≤ Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    change (2 : ℕ)^2 ≤ 2 ^ E.input.field.degree
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by have := E.input.nonbinary; omega)
  have hUt : U ≠ ⊤ := by
    intro h
    have hd := f.dimension 0
    change Module.finrank E.input.field.Carrier U = 1 at hd
    rw [h,finrank_top] at hd
    change Module.finrank E.input.field.Carrier (Fin 3 → E.input.field.Carrier) = 1 at hd
    rw [Module.finrank_fin_fun] at hd
    omega
  intro t ht
  let a : ↥(L ⊓ normalizer (c.preimage U : Set G)) := ⟨t,ht.2,f.invariant 0 ht.1⟩
  obtain ⟨n,hn⟩ := T.isPGroup' ⟨t,ht.1⟩
  have ha : a ^ (2^n) = 1 := by
    apply Subtype.ext
    exact congrArg (fun z : T => (z : G)) hn
  have ha' : (c.normalizerProjection U a) ^ (2^n) = 1 :=
    (map_pow (c.normalizerProjection U) a (2^n)).symm.trans
      ((congrArg (c.normalizerProjection U) ha).trans (map_one _))
  have hap : c.normalizerProjection U a ∈ solvableResidual (c.modelStabilizer U) := by
    change c.normalizerProjection U a ∈ solvableResidual (HigherLinear.parabolicSL U)
    exact parabolic_two_element_mem_residual E.input.field.Carrier hF U (f.space_ne_bot 0) hUt
      _ (n := n) ha'
  obtain ⟨k,hk⟩ := c.residualProjection_surjective U ⟨_,hap⟩
  have he : c.quotientMap ⟨k,(localResidual_le _ k.property).1⟩ = c.quotientMap ⟨t,ht.2⟩ := by
    rw [← c.residualProjection_coe]
    exact congrArg (fun z : solvableResidual (c.modelStabilizer U) => (z.val : c.ModelGroup)) hk
  let k' : L := ⟨k,(localResidual_le _ k.property).1⟩
  have hker : k'⁻¹ * ⟨t,ht.2⟩ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply c.groupEquiv.injective
    change c.quotientMap (k'⁻¹ * ⟨t,ht.2⟩) = c.groupEquiv 1
    rw [map_mul,map_inv,he,map_one,inv_mul_cancel]
  have hv : (k : G)⁻¹ * t ∈ V := hcore.le (mem_map_of_mem L.subtype hker)
  have hkK : (k : G) ∈ E.K := hKL.symm ▸ (hR.symm ▸ k.property)
  have hh := E.K.mul_mem hkK (hV hv)
  simpa only [mul_inv_cancel_left] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow

/-!
# The scalar kernel in the original Cartan

Define X₀ as the literal kernel of the selected X on L/O₂(L). Its
quotient image is central in the marked full SL₃. Hall index arithmetic
lifts the whole scalar center into this same X, and the two-group
quotient kernel is disjoint from X. Thus X₀ is isomorphic to the full
scalar center and has order three in even field degree.

A nonidentity scalar moves all of the original natural V. Since W≤L
and O₂(L)=V, this gives [W,X₀]=V. The original quotient-centralizer
criterion also gives X₀≤X₁, using K=L₁ and W=O₂(K).

Source: Aschbacher–Smith, 11.5.7, refs/quasithin.pdf, printed p.782.
No conjugate Cartan or ambient faithful action is substituted.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The original Cartan kernel on L/O₂(L), hence on L/V once O₂(L)=V. -/
@[expose] def X₀ : Subgroup G := E.X ⊓ coreQuotientCentralizer L

omit [Finite G] in
private theorem mem_coreCentralizer_iff (A : Subgroup G) (x : G) :
    x ∈ coreQuotientCentralizer A ↔ x ∈ normalizer (A : Set G) ∧
      ∀ a ∈ A, ⁅x,a⁆ ∈ A.pCoreIn 2 := by
  constructor
  · rintro ⟨b,hb,rfl⟩
    refine ⟨b.property, ?_⟩
    intro a ha
    have he := congrArg (fun f : MulAut (A ⧸ pCore 2 A) =>
      f (QuotientGroup.mk' (pCore 2 A) ⟨a,ha⟩)) (MonoidHom.mem_ker.mp hb)
    rw [coreQuotientAction_apply_mk] at he
    have hc := QuotientGroup.eq_iff_div_mem.mp he
    simpa only [pCoreIn, subtype_apply, div_eq_mul_inv, coe_mul, coe_inv,
      normalizerMonoidHom_apply_apply_coe, commutatorElement_def] using
        mem_map_of_mem A.subtype hc
  · rintro ⟨hn,hc⟩
    refine ⟨⟨x,hn⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    ext z
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) z
    rw [coreQuotientAction_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨k,hk,he⟩ := hc a a.property
    have he' : k = A.normalizerMonoidHom ⟨x,hn⟩ a / a := by
      apply Subtype.ext
      simpa only [div_eq_mul_inv, coe_mul, coe_inv, commutatorElement_def,
        subtype_apply, normalizerMonoidHom_apply_apply_coe] using he
    exact he' ▸ hk

/-- Membership records exactly the action on the original quotient L/V. -/
theorem mem_X₀_iff (hcore : L.pCoreIn 2 = V) (x : G) :
    x ∈ X₀ E ↔ x ∈ E.X ∧ x ∈ normalizer (L : Set G) ∧
      ∀ l ∈ L, ⁅x,l⁆ ∈ V := by
  change x ∈ E.X ∧ x ∈ coreQuotientCentralizer L ↔ _
  rw [mem_coreCentralizer_iff,hcore]

/-- The original cubic kernel centralizes the actual K/O₂(K). -/
theorem X₀_le_X₁ (hXG : E.X ≤ E.G₁) (hKL : E.K = E.L₁)
    (hcore : L.pCoreIn 2 = V) (hW : E.W = E.K.pCoreIn 2) : X₀ E ≤ X₁ E := by
  intro x hx
  refine ⟨hx.1, (mem_coreCentralizer_iff E.K x).mpr ⟨E.G₁_normalizes_K (hXG hx.1), ?_⟩⟩
  intro k hk
  have hc := ((mem_X₀_iff E hcore x).mp hx).2.2 k (E.L₁_le (hKL ▸ hk))
  exact hW.le (le_conjugateSpanBy V E.G₁ hc)

variable (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
include m

/-- The original quotient marking sends X₀ into the full scalar center of SL₃. -/
theorem X₀_image_central (hX : IsCartan T L E.X) (x : X₀ E) :
    (Coordinates.sl3 m).quotientMap ⟨x,(hX.1 x.property.1).1⟩ ∈
      center SL(3,E.input.field.Carrier) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  obtain ⟨l,rfl⟩ := (Coordinates.sl3 m).quotientMap_surjective g
  have hc := ((mem_coreCentralizer_iff L x).mp x.property.2).2 l l.property
  let a : L := ⟨x,(hX.1 x.property.1).1⟩
  have hk : ⁅a,l⁆ ∈ pCore 2 L := by
    obtain ⟨k,hk,he⟩ := hc
    exact (Subtype.ext he : k = ⁅a,l⁆) ▸ hk
  have hq : (Coordinates.sl3 m).quotientMap ⁅a,l⁆ = 1 := by
    change (Coordinates.sl3 m).groupEquiv (QuotientGroup.mk' _ ⁅a,l⁆) = 1
    exact (congrArg (Coordinates.sl3 m).groupEquiv
      ((QuotientGroup.eq_one_iff _).mpr hk)).trans (map_one _)
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hq
  exact hq.symm

private theorem X₀_image_ne_one (hX : IsCartan T L E.X) (x : X₀ E)
    (hx : x ≠ 1) :
    (Coordinates.sl3 m).quotientMap ⟨x,(hX.1 x.property.1).1⟩ ≠ 1 := by
  intro he
  have hk : (⟨x,(hX.1 x.property.1).1⟩ : L) ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply (Coordinates.sl3 m).groupEquiv.injective
    change (Coordinates.sl3 m).quotientMap ⟨x,(hX.1 x.property.1).1⟩ =
      (Coordinates.sl3 m).groupEquiv 1
    exact he.trans (map_one _).symm
  have hp : (x : G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hk
  have hd : Disjoint E.X (L.pCoreIn 2) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)).map L.subtype |>.exists_card_eq
    apply disjoint_of_coprime_natCard
    change Nat.Coprime (Nat.card E.X) (Nat.card ((pCore 2 L).map L.subtype))
    rw [hn]
    exact (Nat.coprime_two_right.mpr hX.odd).pow_right n
  exact hx (Subtype.ext (mem_bot.mp ((disjoint_iff.mp hd).le ⟨x.property.1,hp⟩)))

/-- A nonidentity scalar in the marked original Cartan moves the entire V. -/
theorem seed_le_commutator_X₀ (hX : IsCartan T L E.X) (x : X₀ E) (hx : x ≠ 1) :
    V ≤ ⁅E.W,X₀ E⁆ := by
  let c := Coordinates.sl3 m
  let a : L := ⟨x,(hX.1 x.property.1).1⟩
  obtain ⟨r,_,hmat⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    (X₀_image_central E m hX x)
  have hr1 : r ≠ 1 := by
    intro he
    apply X₀_image_ne_one E m hX x hx
    apply Subtype.ext
    change ((Coordinates.sl3 m).quotientMap ⟨x,(hX.1 x.property.1).1⟩).val =
      (1 : Matrix (Fin 3) (Fin 3) E.input.field.Carrier)
    simpa only [he,map_one] using hmat.symm
  have hscalar (u : V) :
      (c.projection (V.normalizerMonoidHom (inclusion D.normalizes a) u)).toAdd =
        r • (c.projection u).toAdd := by
    rw [c.projection_component_conjugation]
    change Matrix.mulVec (c.quotientMap a).val _ = _
    rw [← hmat]
    exact Matrix.diagonal_const_mulVec r _
  intro v hv
  obtain ⟨u,hu⟩ := c.projection_surjective
    (Multiplicative.ofAdd ((r-1)⁻¹ • (c.projection ⟨v,hv⟩).toAdd))
  let w := V.normalizerMonoidHom (inclusion D.normalizes a) u * u⁻¹
  have hw : c.projection w = c.projection ⟨v,hv⟩ := by
    apply Multiplicative.toAdd.injective
    change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes a) u * u⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    rw [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [hscalar,hu]
    change r • ((r-1)⁻¹ • (c.projection ⟨v,hv⟩).toAdd) -
      (r-1)⁻¹ • (c.projection ⟨v,hv⟩).toAdd = (c.projection ⟨v,hv⟩).toAdd
    calc
      _ = (r-1) • ((r-1)⁻¹ • (c.projection ⟨v,hv⟩).toAdd) := by
        rw [sub_smul, one_smul]
      _ = _ := by
        rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hr1), one_smul]
  have he : (w : G) = v := congrArg Subtype.val (SL3.projection_injective D E.input m hw)
  rw [← he,commutator_comm]
  exact commutator_mem_commutator x.property (le_conjugateSpanBy V E.G₁ u.property)

/-- The literal ambient commutator identity, conditional only on the cubic kernel's size. -/
theorem commutator_X₀_eq_seed (hX : IsCartan T L E.X)
    (hcore : L.pCoreIn 2 = V) (hWL : E.W ≤ L) (hcard : Nat.card (X₀ E) = 3) :
    ⁅E.W,X₀ E⁆ = V := by
  have hn : Nontrivial (X₀ E) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,hx⟩ := exists_ne (1 : X₀ E)
  apply le_antisymm
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro x hx w hw
    exact ((mem_X₀_iff E hcore x).mp hx).2.2 w (hWL hw)
  · exact seed_le_commutator_X₀ E m hX x hx

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow
open LocalGeometry

private theorem odd_central_le_hall {A : Type*} [Group A] [Finite A]
    (Y Z : Subgroup A) (hY : IsHallSubgroup OddHall.oddPrimes Y)
    (hZ : Odd (Nat.card Z)) (hc : Z ≤ center A) : Z ≤ Y := by
  have hn : Z ≤ normalizer (Y : Set A) := hc.trans (center_le_normalizer _)
  have hi : Y.relIndex Z ∣ Y.index := by
    rw [← OddHall.relIndex_normalized_sup Y Z hn]
    exact relIndex_dvd_index_of_le le_sup_left
  have hcop : Nat.Coprime (Nat.card Z) Y.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpZ hpY
    have hp2 : p = 2 := Classical.not_not.mp (hY.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpY)
    subst p
    exact hZ.not_two_dvd_nat hpZ
  exact relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop (relIndex_dvd_card _ _) hi)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
include m

private theorem original_cartan_map_injective (hX : IsCartan T L E.X) :
    Function.Injective ((Coordinates.sl3 m).quotientMap.comp
      (inclusion (hX.1.trans inf_le_left))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hk : (⟨x,(hX.1 x.property).1⟩ : L) ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply (Coordinates.sl3 m).groupEquiv.injective
    change ((Coordinates.sl3 m).quotientMap.comp (inclusion (hX.1.trans inf_le_left))) x =
      (Coordinates.sl3 m).groupEquiv 1
    exact (MonoidHom.mem_ker.mp hx).trans (map_one _).symm
  have hd : Disjoint E.X (L.pCoreIn 2) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)).map L.subtype |>.exists_card_eq
    apply disjoint_of_coprime_natCard
    change Nat.Coprime (Nat.card E.X) (Nat.card ((pCore 2 L).map L.subtype))
    rw [hn]
    exact (Nat.coprime_two_right.mpr hX.odd).pow_right n
  apply Subtype.ext
  exact mem_bot.mp ((disjoint_iff.mp hd).le ⟨x.property,mem_map_of_mem L.subtype hk⟩)

/-- Every scalar central element lifts to the selected Cartan itself. -/
theorem original_cartan_covers_center (hX : IsCartan T L E.X) :
    center SL(3,E.input.field.Carrier) ≤
      ((Coordinates.sl3 m).quotientMap.comp (inclusion (hX.1.trans inf_le_left))).range := by
  let c := Coordinates.sl3 m
  let N := normalizer (c.modelSylow : Set c.ModelGroup)
  let Y := (E.X.subgroupOf (cartanNormalizer T L)).map c.cartanProjection
  let Z := (center c.ModelGroup).subgroupOf N
  have hY : IsHallSubgroup OddHall.oddPrimes Y := by
    refine ⟨fun p hp => hX.2.p_in_pi_of_p_dvd_card p
      (hp.trans ((E.X.subgroupOf (cartanNormalizer T L)).card_map_dvd c.cartanProjection)), ?_⟩
    intro p hp
    exact hX.2.p_in_pi_of_p_dvd_index p
      (hp.trans (index_map_dvd _ c.cartanProjection_surjective))
  have hZ : Odd (Nat.card Z) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (center_le_normalizer _)).toEquiv]
    change Odd (Nat.card (center SL(3,E.input.field.Carrier)))
    rw [← Matrix.PSL3.projection_ker, Matrix.PSL3.card_projectionKernel]
    exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left _ _)
  have hZc : Z ≤ center N := by
    intro z hz
    apply Subgroup.mem_center_iff.mpr
    intro n
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz n)
  have hzY := odd_central_le_hall Y Z hY hZ hZc
  intro z hz
  have hzN : z ∈ N := center_le_normalizer _ hz
  obtain ⟨x,hx,he⟩ := hzY (show (⟨z,hzN⟩ : N) ∈ Z from hz)
  refine ⟨⟨x,hx⟩, ?_⟩
  exact (c.cartanProjection_coe x).symm.trans (congrArg Subtype.val he)

private theorem original_cartan_center_iff (hX : IsCartan T L E.X) (x : E.X) :
    (x : G) ∈ X₀ E ↔
      (Coordinates.sl3 m).quotientMap ⟨x,(hX.1 x.property).1⟩ ∈
        center SL(3,E.input.field.Carrier) := by
  constructor
  · intro hx
    exact X₀_image_central E m hX ⟨x,hx⟩
  · intro hx
    refine ⟨x.property, (mem_coreCentralizer_iff L x).mpr
      ⟨L.le_normalizer (hX.1 x.property).1, ?_⟩⟩
    intro l hl
    let a : L := ⟨x,(hX.1 x.property).1⟩
    have hk : ⁅a,(⟨l,hl⟩ : L)⁆ ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply (Coordinates.sl3 m).groupEquiv.injective
      change (Coordinates.sl3 m).quotientMap ⁅a,(⟨l,hl⟩ : L)⁆ =
        (Coordinates.sl3 m).groupEquiv 1
      rw [map_one,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hx _).symm
    exact mem_map_of_mem L.subtype hk

/-- The literal Cartan kernel is isomorphic to the full SL₃ scalar center. -/
def original_cartan_center_equiv (hX : IsCartan T L E.X) :
    X₀ E ≃* center SL(3,E.input.field.Carrier) := by
  let f : X₀ E →* center SL(3,E.input.field.Carrier) :=
    { toFun x := ⟨(Coordinates.sl3 m).quotientMap ⟨x,(hX.1 x.property.1).1⟩,
        X₀_image_central E m hX x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' x y := by
        apply Subtype.ext
        exact map_mul (Coordinates.sl3 m).quotientMap
          (⟨x,(hX.1 x.property.1).1⟩ : L) (⟨y,(hX.1 y.property.1).1⟩ : L) }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y he
    have hh := original_cartan_map_injective E m hX (a₁ := ⟨x,x.property.1⟩)
      (a₂ := ⟨y,y.property.1⟩) (congrArg Subtype.val he)
    exact Subtype.ext (congrArg (fun z : E.X => (z : G)) hh)
  · intro z
    obtain ⟨x,hx⟩ := original_cartan_covers_center E m hX z.property
    have hx0 : (x : G) ∈ X₀ E :=
      (original_cartan_center_iff E m hX x).mpr (hx.symm ▸ z.property)
    exact ⟨⟨x,hx0⟩,Subtype.ext hx⟩

/-- For even field degree the original C_X(L/V) has order three. -/
theorem X₀_card (hX : IsCartan T L E.X) (heven : Even E.input.field.degree) :
    Nat.card (X₀ E) = 3 := by
  rw [Nat.card_congr (original_cartan_center_equiv E m hX).toEquiv,
    ← Matrix.PSL3.projection_ker,Matrix.PSL3.card_projectionKernel,E.input.field.card_eq]
  apply Nat.gcd_eq_left_iff_dvd.mpr
  obtain ⟨k,hk⟩ := heven
  have he : 2 ^ E.input.field.degree % 3 = 1 := by
    rw [hk,← two_mul,pow_mul,Nat.pow_mod]
    norm_num
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow

/-!
# Marked torus and Sylow geometry for the two outside-H endings

For odd field degree, the original natural marking proves T=T_L and
the point-parabolic residual puts T∩L in K. These discharge both
geometric premises of Outside.contradiction_of_sourceTL_eq, whose
B.6.8 argument already proves H normalizes C_T(W).

For even field degree, the original Cartan kernel X₀ has order three,
lies in X₁, and satisfies the literal ambient identity [W,X₀]=V.
The even endpoint retains only the independent abelianness input for
the multiplicity-action image, besides the preceding source hypotheses
and the authorized block outputs. The outside-H owner retains the full
11.5.7 assembly.

Source: Aschbacher–Smith, 11.5.7, refs/quasithin.pdf, printed p.782.
-/

public section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
include m

/-- Both geometric inputs of the odd outside-H endpoint, on the original marking and flag. -/
theorem odd_geometry (f : InvariantFlag (.sl3 m))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace (f.space 0))
    (hKL : E.K = E.L₁) (hcore : L.pCoreIn 2 = V) (hW : E.W = E.K.pCoreIn 2)
    (hodd : Odd E.input.field.degree) :
    (T : Subgroup G) = sourceTL T L ∧ (T : Subgroup G) ⊓ L ≤ E.K :=
  ⟨sylow_eq_sourceTL D E.input m hodd, sylow_intersection_le_K E m f hpoint hKL hcore hW⟩

/-- Close the odd branch without the incorrect assertion W=T∩L. -/
theorem odd_contradiction (f : InvariantFlag (.sl3 m))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace (f.space 0))
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hKL : E.K = E.L₁)
    (hrespoint : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨ ⁅E.K,outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hWL : E.W ≤ L) (hcore : L.pCoreIn 2 = V) (hW : E.W = E.K.pCoreIn 2)
    (hsplit : sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hNT : normalizer (T : Set G) ≤ E.M) (hodd : Odd E.input.field.degree) : False := by
  obtain ⟨hTL,hTK⟩ := odd_geometry E m f hpoint hKL hcore hW hodd
  exact contradiction_of_sourceTL_eq E hH hHG hKL hrespoint hselect hWL hTK hTL hsplit hNT

/-- The selected Cartan's actual cubic kernel and ambient moved subgroup. -/
theorem even_geometry (hX : IsCartan T L E.X) (hXG : E.X ≤ E.G₁)
    (hKL : E.K = E.L₁) (hWL : E.W ≤ L) (hcore : L.pCoreIn 2 = V)
    (hW : E.W = E.K.pCoreIn 2) (heven : Even E.input.field.degree) :
    Nat.card (X₀ E) = 3 ∧ X₀ E ≤ X₁ E ∧ ⁅E.W,X₀ E⁆ = V :=
  ⟨X₀_card E m hX heven, X₀_le_X₁ E hXG hKL hcore hW,
    commutator_X₀_eq_seed E m hX hcore hWL (X₀_card E m hX heven)⟩

/-- The even outside-H application retains only the independent abelian-image input. -/
theorem even_contradiction (hX : IsCartan T L E.X)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hKL : E.K = E.L₁) (hWL : E.W ≤ L) (hcore : L.pCoreIn 2 = V)
    (hW : E.W = E.K.pCoreIn 2) (heven : Even E.input.field.degree)
    (hab : IsMulCommutative
      (quotientAction E (C E)
        (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG)).range) : False := by
  obtain ⟨_,hX₀,hmove⟩ := even_geometry E m hX hXG hKL hWL hcore hW heven
  exact contradiction_of_moved_seed E hH hHG hXG hab (X₀ E) hX₀ hmove

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow