module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCenters
public import Theory.GroupAction.BinaryTransvectionImage

/-!
# The actual crossing fixed space and full transvection action

Commutators of X with E belong to the conjugate Frattini line, which is
disjoint from Z(U). Thus a quotient representative in E is fixed exactly
when it commutes with X. The original center cuts give C_E(X) = Z_S,
hence C_{E-hat}(X-dot) = Z_S-hat. Binary duality now realizes every linear
functional vanishing on the marked line by one actual element of X-dot.
The same action moves the commutator-form perpendicular hyperplane into E-hat.

Source: Aschbacher--Smith, 6.2.17(3),(7)--(8), printed pp.689--690.
The remaining G.10 fixed bound and rank equation, G.11 classification and
strict contradiction stay with qt-d-1222-recognition-strict-elimination.
LocalAnalysis is discharged by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Commutators of the crossed actors with E lie in the conjugate Frattini line. -/
theorem LocalAnalysis.strict_crossing_commutator_le_line
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (d : G) :
    ⁅strictCrossingGroup (T : Subgroup G) L R z d,
      strictCrossingIntersection (T : Subgroup G) L R z d⁆ ≤
        (zpowers z).map (MulAut.conj d⁻¹).toMonoidHom := by
  let U := sourceClosure (T : Subgroup G) L R z
  let U' := U.map (MulAut.conj d⁻¹).toMonoidHom
  have hp : IsPGroup 2 U' :=
    (((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core).map _
  let : Fact (IsPGroup 2 U') := ⟨hp⟩
  apply Subgroup.commutator_le.mpr
  intro x hx e he
  have hc : ⁅x,e⁆ ∈ (frattini U').map U'.subtype :=
    ⟨⁅(⟨x, hx.1⟩ : U'), ⟨e, he.2⟩⁆,
      SmallNonabelianTwoGroup.frattini_commutator_mem hp _ _, rfl⟩
  rwa [frattini_image_map _ _ (MulAut.conj d⁻¹).injective,
    (A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).1] at hc

/-- Each displacement on E-hat belongs to the original marked source line. -/
theorem LocalAnalysis.strict_crossing_displacement_mem_line
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    {d : G} (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    {a : StrictActor (T : Subgroup G) L R z}
    (ha : a ∈ strictCrossingImage (T : Subgroup G) L R z d)
    {e : Additive (StrictVectorQuotient (T : Subgroup G) L R z)}
    (he : e ∈ strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d)) :
    strictRepresentation (T : Subgroup G) L R z a e - e ∈ strictSourceLine (T : Subgroup G) L R z := by
  obtain ⟨h, hh, rfl⟩ := ha
  obtain ⟨u, hu, he⟩ := he
  have hc := A.strict_crossing_commutator_le_line h611 hnatural hz horder hstrict d
    (commutator_mem_commutator hh hu)
  have hline : (zpowers z).map (MulAut.conj d⁻¹).toMonoidHom ≤ ZS (T : Subgroup G) L R := by
    have hh := map_mono (f := (MulAut.conj d⁻¹).toMonoidHom) (zpowers_le.mpr hz)
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (ZS (T : Subgroup G) L R : Set G)).inv_mem hdZ))
  have hd : ((strictClosureAction (T : Subgroup G) L R z h u / u : sourceClosure (T : Subgroup G) L R z) : G) =
      ⁅(h : G),(u : G)⁆ := by
    change ((h : G) * (u : G) * (h : G)⁻¹) / (u : G) = _
    simp only [div_eq_mul_inv, commutatorElement_def]
  have hm : strictClosureAction (T : Subgroup G) L R z h u / u ∈
      (ZS (T : Subgroup G) L R).subgroupOf (sourceClosure (T : Subgroup G) L R z) := by
    change ((strictClosureAction (T : Subgroup G) L R z h u / u : sourceClosure (T : Subgroup G) L R z) : G) ∈ ZS (T : Subgroup G) L R
    rw [hd]
    exact hline hc
  have he' : e = strictHatElement (T : Subgroup G) L R z u := (congrArg Additive.ofMul he).symm
  rw [he', strictRepresentation_mk, strictHatElement, toMul_ofMul, strictQuotientAction_mk]
  exact ⟨_, hm, map_div _ _ _⟩

/-- A fixed quotient representative in E actually commutes with X. -/
theorem LocalAnalysis.strict_crossing_hat_fixed_iff_commute
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    {d : G} (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G))
    (u : sourceClosure (T : Subgroup G) L R z)
    (hu : (u : G) ∈ strictCrossingIntersection (T : Subgroup G) L R z d) :
    (∀ a ∈ strictCrossingImage (T : Subgroup G) L R z d,
      strictRepresentation (T : Subgroup G) L R z a (strictHatElement (T : Subgroup G) L R z u) =
        strictHatElement (T : Subgroup G) L R z u) ↔
      (u : G) ∈ centralizer (strictCrossingGroup (T : Subgroup G) L R z d : Set G) := by
  let U := sourceClosure (T : Subgroup G) L R z
  let C := (center U).map U.subtype
  let f := (MulAut.conj d⁻¹).toMonoidHom
  have hline : (zpowers z).map f ≤ ZS (T : Subgroup G) L R := by
    exact (map_mono (zpowers_le.mpr hz)).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (ZS (T : Subgroup G) L R : Set G)).inv_mem hdZ))
  have hdis : Disjoint ((zpowers z).map f) C := by
    apply disjoint_iff.mpr
    apply bot_unique
    have hi : (zpowers z).map f ⊓ C ≤ (zpowers z).map f ⊓ zpowers z :=
      le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans (hline.trans inf_le_left))).trans_eq
        (A.strict_layer_center_intersection h611 hnatural hz horder hstrict))
    exact hi.trans (strict_disjoint_conjugate_line horder hd).symm.le_bot
  constructor
  · intro hfix x hx
    let h : centralizer ({z} : Set G) := ⟨x, strictCrossingGroup_le_centralizer _ _ _ _ _ hz hx⟩
    have hf := hfix (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker h)
      (mem_map_of_mem _ (show h ∈ (strictCrossingGroup (T : Subgroup G) L R z d).subgroupOf _ from hx))
    change Additive.ofMul (strictQuotientAction (T : Subgroup G) L R z h (QuotientGroup.mk' (center U) u)) = _ at hf
    have he := Additive.ofMul.injective hf
    rw [strictQuotientAction_mk] at he
    have hc := QuotientGroup.eq_iff_div_mem.mp he
    have hdc : ((strictClosureAction (T : Subgroup G) L R z h u / u : U) : G) = ⁅x,(u : G)⁆ := by
      change (x * (u : G) * x⁻¹) / (u : G) = _
      simp only [div_eq_mul_inv, commutatorElement_def]
    have hzC : ⁅x,(u : G)⁆ ∈ C := ⟨_, hc, hdc⟩
    have hzline := A.strict_crossing_commutator_le_line h611 hnatural hz horder hstrict d
      (commutator_mem_commutator hx hu)
    exact (commutatorElement_eq_one_iff_mul_comm.mp (mem_bot.mp (hdis.le_bot ⟨hzline, hzC⟩)))
  · intro hc a ha
    obtain ⟨h, hh, rfl⟩ := ha
    rw [strictRepresentation_mk, strictHatElement, toMul_ofMul, strictQuotientAction_mk]
    have he : strictClosureAction (T : Subgroup G) L R z h u = u := by
      apply Subtype.ext
      rw [strictClosureAction_apply, hc h hh, mul_inv_cancel_right]
    rw [he]

/-- Source 6.2.17(8), for the actual dotted action and actual E-hat. -/
theorem LocalAnalysis.strict_crossing_fixed_space
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    {d : G} (hdL : d ∈ L)
    (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G))
    (e : strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d)) :
    (∀ a ∈ strictCrossingImage (T : Subgroup G) L R z d,
      strictRepresentation (T : Subgroup G) L R z a e = e) ↔
      (e : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∈ strictSourceLine (T : Subgroup G) L R z := by
  constructor
  · intro hfix
    obtain ⟨u, hu, he⟩ := e.property
    have he' : (e : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) =
        strictHatElement (T : Subgroup G) L R z u := (congrArg Additive.ofMul he).symm
    rw [he'] at hfix ⊢
    have hc := (A.strict_crossing_hat_fixed_iff_commute h611 hnatural hz horder hstrict hdZ hd u hu).mp hfix
    have hS := (A.strict_crossing_fixed_subgroup h611 hnatural hz horder hTH hstrict hdL hdZ hd).le ⟨hu,hc⟩
    exact ⟨u, hS, rfl⟩
  · intro he a ha
    exact strict_crossingImage_fixes_sourceLine h611 hz d ha he

/-- Source 6.2.17(3) on the same commutator form: X moves the perpendicular
hyperplane into the actual crossing space. -/
theorem strict_crossing_perpendicular_displacement
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (hB : ∀ u v : sourceClosure (T : Subgroup G) L R z,
      B (strictHatElement (T : Subgroup G) L R z u)
        (strictHatElement (T : Subgroup G) L R z v) = 0 ↔ Commute u v)
    {d : G} (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    {a : StrictActor (T : Subgroup G) L R z}
    (ha : a ∈ strictCrossingImage (T : Subgroup G) L R z d)
    {e : Additive (StrictVectorQuotient (T : Subgroup G) L R z)}
    (he : e ∈ B.orthogonal (strictSourceLine (T : Subgroup G) L R z)) :
    strictRepresentation (T : Subgroup G) L R z a e - e ∈
      strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d) := by
  obtain ⟨h, hh, rfl⟩ := ha
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center (sourceClosure (T : Subgroup G) L R z)) e.toMul
  have he' : e = strictHatElement (T : Subgroup G) L R z u := (congrArg Additive.ofMul hu).symm
  rw [he'] at he ⊢
  have hcu := (strict_hat_orthogonal_iff B hB _ (hstrict.le.trans inf_le_left) u).mp he
  have hcomm := strict_crossing_commutator_le_intersection h611 hz hdZ
  rw [Subgroup.commutator_comm] at hcomm
  have hc := hcomm (commutator_mem_commutator hh ⟨u.property, hcu⟩)
  have hd : ((strictClosureAction (T : Subgroup G) L R z h u / u : sourceClosure (T : Subgroup G) L R z) : G) =
      ⁅(h : G),(u : G)⁆ := by
    change ((h : G) * (u : G) * (h : G)⁻¹) / (u : G) = _
    simp only [div_eq_mul_inv, commutatorElement_def]
  have hm : strictClosureAction (T : Subgroup G) L R z h u / u ∈
      (strictCrossingIntersection (T : Subgroup G) L R z d).subgroupOf (sourceClosure (T : Subgroup G) L R z) := by
    change ((strictClosureAction (T : Subgroup G) L R z h u / u : sourceClosure (T : Subgroup G) L R z) : G) ∈ strictCrossingIntersection (T : Subgroup G) L R z d
    rw [hd]
    exact hc
  rw [strictRepresentation_mk, strictHatElement, toMul_ofMul, strictQuotientAction_mk]
  exact ⟨_, hm, map_div _ _ _⟩

/-- Source 6.2.17(7), realizing every entire centered transvection. -/
theorem LocalAnalysis.strict_crossing_full_transvections
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    {d : G} (hdL : d ∈ L)
    (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G))
    (v : strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d))
    (hv : (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ≠ 0)
    (hvS : (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∈ strictSourceLine (T : Subgroup G) L R z) :
    let E := strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d)
    let X := strictCrossingImage (T : Subgroup G) L R z d
    let ρ := strictRepresentation (T : Subgroup G) L R z
    (∀ a : X, ∃ φ : Module.Dual (ZMod 2) E, φ v = 0 ∧
      ∀ e : E, ρ a e = (e : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) + φ e • (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))) ∧
    (∀ φ : Module.Dual (ZMod 2) E, φ v = 0 → ∃ a : X,
      ∀ e : E, ρ a e = (e : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) + φ e • (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))) := by
  let E := strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d)
  let X := strictCrossingImage (T : Subgroup G) L R z d
  let ρ := strictRepresentation (T : Subgroup G) L R z
  let α := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z))).toMonoidHom.comp
    (ρ.asGroupHom.comp X.subtype)
  have hline : strictSourceLine (T : Subgroup G) L R z =
      Submodule.span (ZMod 2) {(v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))} :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (A.strictSourceLine_finrank h611 hnatural hz horder hstrict) hvS hv
  apply BinaryTransvection.full_action_of_fixed_space α E v hv
  · intro a e
    rw [← hline]
    exact A.strict_crossing_displacement_mem_line h611 hnatural hz horder hstrict hdZ a.property e.property
  · intro e
    change (∀ a : X, ρ a e = (e : Additive (StrictVectorQuotient (T : Subgroup G) L R z))) ↔ _
    rw [show (∀ a : X, ρ a e = (e : Additive (StrictVectorQuotient (T : Subgroup G) L R z))) ↔
      ∀ a ∈ X, ρ a e = e from Subtype.forall]
    rw [A.strict_crossing_fixed_space h611 hnatural hz horder hTH hstrict hdL hdZ hd, hline]
    constructor
    · intro he
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp he
      exact Submodule.mem_span_singleton.mpr ⟨t, Subtype.ext ht⟩
    · intro he
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp he
      exact Submodule.mem_span_singleton.mpr ⟨t, congrArg Subtype.val ht⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
