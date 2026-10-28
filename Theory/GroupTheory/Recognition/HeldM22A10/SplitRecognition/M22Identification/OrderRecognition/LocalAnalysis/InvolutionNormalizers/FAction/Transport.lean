module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Model
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.AmbientElementary

/-!
# Realizing the F-automizer in fixed coordinates

Conjugation identifies N_G(F)/F with its image in Aut(F), since C_G(F)=F.
The marked central involution has exactly the coordinate Sylow action as
stabilizer. The image order is eight times an odd number. If z is conjugate
to d, a Sylow subgroup of C_G(d) containing F is also an ambient Sylow
subgroup; relative normality of F puts it in N_G(F). Its action has order
eight and fixes d.

These are the ambient inputs to the finite calculation in Janko's Lemma 2.
No simplicity, global fusion or recognition theorem enters this transport.
The arbitrary coordinate map need not preserve the originally chosen Sylow.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, pp.4–5.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The actual image equivalence between coordinate F and ambient F. -/
@[expose] public noncomputable def coordinates : modelF ≃* F D k :=
  (modelF.equivMapOfInjective (into D k) (into_injective D k)).trans
    (MulEquiv.subgroupCongr (modelF_map D k))

omit [Finite G] in
public theorem coordinates_apply (x : modelF) : (coordinates D k x : G) = into D k x := rfl

/-- Conjugation in the ambient normalizer, transported to coordinate F. -/
@[expose] public noncomputable def action : normalizer (F D k : Set G) →* MulAut modelF :=
  (MulAut.congr (coordinates D k).symm).toMonoidHom.comp (F D k).normalizerMonoidHom

/-- The faithful image of the ambient normalizer in the fixed automorphism group. -/
@[expose] public noncomputable def automizer : Subgroup (MulAut modelF) := (action D k).range

public theorem action_ker : (action D k).ker =
    (F D k).subgroupOf (normalizer (F D k : Set G)) := by
  rw [action, MonoidHom.ker_comp_of_injective _ _ (MulAut.congr (coordinates D k).symm).injective,
    normalizerMonoidHom_ker, F_centralizer D k]

/-- The actual normalizer quotient is isomorphic to its coordinate action image. -/
public noncomputable def quotientEquiv :
    (normalizer (F D k : Set G) ⧸
      (F D k).subgroupOf (normalizer (F D k : Set G))) ≃* automizer D k :=
  (QuotientGroup.quotientMulEquivOfEq (action_ker D k).symm).trans
    (QuotientGroup.quotientKerEquivRange (action D k))

omit [Finite G] in
public theorem action_apply (g : normalizer (F D k : Set G)) (x : modelF) :
    into D k ((action D k g x : modelF) : TwistedModel) =
      (g : G) * into D k x * (g : G)⁻¹ := by
  change ((coordinates D k) ((coordinates D k).symm
    ((F D k).normalizerMonoidHom g (coordinates D k x))) : G) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

private def liftLocal (g : normalizer (modelF : Set TwistedModel)) :
    normalizer (F D k : Set G) := ⟨into D k g, by
  rw [← modelF_map D k]
  exact le_normalizer_map _ (mem_map_of_mem _ g.property)⟩

omit [Finite G] in
private theorem action_liftLocal (g : normalizer (modelF : Set TwistedModel)) :
    action D k (liftLocal D k g) = modelF.normalizerMonoidHom g := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  apply into_injective D k
  rw [action_apply]
  change into D k g * into D k x * (into D k g)⁻¹ =
    into D k ((g : TwistedModel) * x * (g : TwistedModel)⁻¹)
  simp only [map_mul, map_inv]

omit [Finite G] in
public theorem localAutomizer_le : localAutomizer ≤ automizer D k := by
  rintro a ⟨g, rfl⟩
  exact ⟨liftLocal D k g, action_liftLocal D k g⟩

public theorem action_fix_pointZ_iff (g : normalizer (F D k : Set G)) :
    action D k g pointZ = pointZ ↔ (g : G) ∈ D.centralizer := by
  constructor
  · intro h
    have hh := congrArg (fun x : modelF => into D k x) h
    rw [action_apply] at hh
    change (g : G) * into D k (z 0) * (g : G)⁻¹ = into D k (z 0) at hh
    rw [into_z_zero D k] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
  · intro hg
    apply Subtype.ext
    apply into_injective D k
    rw [action_apply]
    change (g : G) * into D k (z 0) * (g : G)⁻¹ = into D k (z 0)
    rw [into_z_zero D k]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)

public theorem stabilizer_pointZ (a : MulAut modelF) (ha : a ∈ automizer D k) :
    a pointZ = pointZ ↔ a ∈ localAutomizer := by
  obtain ⟨g, rfl⟩ := ha
  constructor
  · intro hz
    have hgT : (g : G) ∈ caseIISylow D k := by
      change (g : G) ∈ (caseIISylow D k : Subgroup G)
      rw [← normalizer_F_inf_centralizer D k]
      exact ⟨g.property, (action_fix_pointZ_iff D k g).mp hz⟩
    obtain ⟨t, ht, htg⟩ := hgT
    have htN : t ∈ normalizer (modelF : Set TwistedModel) := by
      rwa [modelF_normalizer]
    refine ⟨⟨t, htN⟩, ?_⟩
    rw [← action_liftLocal D k]
    congr 1
    exact Subtype.ext htg
  · rintro ⟨t, ht⟩
    rw [← ht, ← action_liftLocal D k]
    apply (action_fix_pointZ_iff D k _).mpr
    exact (k t).property

public theorem normalizer_card : Nat.card (normalizer (F D k : Set G)) =
    Nat.card (automizer D k) * 16 := by
  have h := card_eq_card_quotient_mul_card_subgroup
    ((F D k).subgroupOf (normalizer (F D k : Set G)))
  rwa [Nat.card_congr (quotientEquiv D k).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (H := F D k) le_normalizer).toEquiv,
    F_card D k] at h

public theorem automizer_card_eight_mul_odd :
    ∃ m : ℕ, Odd m ∧ Nat.card (automizer D k) = 8 * m := by
  let P := (caseIISylow D k).subtype (caseIISylow_le_normalizer_F D k)
  have hc : Nat.card P = 128 := by
    change Nat.card ((caseIISylow D k : Subgroup G).subgroupOf
      (normalizer (F D k : Set G))) = 128
    rw [Nat.card_congr (subgroupOfEquivOfLe (caseIISylow_le_normalizer_F D k)).toEquiv,
      (caseIISylow D k).card_eq_multiplicity, ← D.sylow.card_eq_multiplicity, D.sylow_card]
  refine ⟨(P : Subgroup (normalizer (F D k : Set G))).index, ?_, ?_⟩
  · exact Nat.not_even_iff_odd.mp (fun he => P.not_dvd_index (even_iff_two_dvd.mp he))
  · have h := (P : Subgroup (normalizer (F D k : Set G))).card_mul_index
    rw [hc, normalizer_card D k] at h
    omega

public theorem exists_sylow_centralizing_d (hd : IsConj D.z (into D k d)) :
    ∃ P : Sylow 2 G, F D k ≤ P ∧
      (P : Subgroup G) ≤ centralizer ({into D k d} : Set G) ∧
      (P : Subgroup G) ≤ normalizer (F D k : Set G) := by
  let C := centralizer ({into D k d} : Set G)
  have hFC : F D k ≤ C := by
    let := F_elementary D k
    have hdF : into D k d ∈ F D k := by
      rw [← modelF_map D k]
      exact mem_map_of_mem _ modelF_generators.2.2.2
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((le_centralizer (F D k) hx) _ hdF).symm
  obtain ⟨Q, hQ⟩ := ((F_elementary D k).isPGroup.of_equiv
    (subgroupOfEquivOfLe hFC).symm).exists_le_sylow
  obtain ⟨g, hg⟩ := isConj_iff.mp hd
  let P₀ : Sylow 2 G := g • D.sylow
  have hP₀ : (P₀ : Subgroup G) ≤ C := by
    change (D.sylow : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ C
    rintro y ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change MulAut.conj g x * into D k d = into D k d * MulAut.conj g x
    have he : MulAut.conj g D.z = into D k d := hg
    simpa only [map_mul, he] using congrArg (MulAut.conj g)
      (mem_centralizer_singleton_iff.mp (D.sylow_le_centralizer hx))
  have hcQ : Nat.card Q = 128 := by
    calc
      Nat.card Q = Nat.card (P₀.subtype hP₀) := by
        rw [Q.card_eq_multiplicity, (P₀.subtype hP₀).card_eq_multiplicity]
      _ = Nat.card P₀ :=
        Nat.card_congr (subgroupOfEquivOfLe hP₀).toEquiv
      _ = 128 := by
        rw [P₀.card_eq_multiplicity, ← D.sylow.card_eq_multiplicity, D.sylow_card]
  have hc : Nat.card ((Q : Subgroup C).map C.subtype) = 128 := by
    rw [← Nat.card_congr ((Q : Subgroup C).equivMapOfInjective C.subtype
      Subtype.val_injective).toEquiv, hcQ]
  let P : Sylow 2 G := Sylow.ofCard ((Q : Subgroup C).map C.subtype) (by
    rw [hc, ← D.sylow.card_eq_multiplicity, D.sylow_card])
  have hFP : F D k ≤ P := by
    intro x hx
    exact ⟨⟨x, hFC hx⟩, hQ hx, rfl⟩
  refine ⟨P, hFP, map_subtype_le _, ?_⟩
  have hnormal := elementary_sixteen_normal_in_sylow D k P (F D k) hFP
    (F_elementary D k) (F_card D k)
  exact (normal_subgroupOf_iff_le_normalizer hFP).mp hnormal

omit [Finite G] in
public theorem action_fix_pointD_iff (g : normalizer (F D k : Set G)) :
    action D k g pointD = pointD ↔
      (g : G) ∈ centralizer ({into D k d} : Set G) := by
  constructor
  · intro h
    have hh := congrArg (fun x : modelF => into D k x) h
    rw [action_apply] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
  · intro hg
    apply Subtype.ext
    apply into_injective D k
    rw [action_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)

public theorem stabilizer_pointD_card_ge (hd : IsConj D.z (into D k d)) :
    8 ≤ Nat.card ↥(automizer D k ⊓ MulAction.stabilizer (MulAut modelF) pointD) := by
  obtain ⟨P, hFP, hPC, hPN⟩ := exists_sylow_centralizing_d D k hd
  let f : P →* MulAut modelF := (action D k).comp (inclusion hPN)
  have hker : f.ker = (F D k).subgroupOf P := by
    ext p
    change inclusion hPN p ∈ (action D k).ker ↔ (p : G) ∈ F D k
    rw [action_ker D k]
    rfl
  have hcard : Nat.card f.range = 8 := by
    have h := card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
      hker, Nat.card_congr (subgroupOfEquivOfLe hFP).toEquiv,
      F_card D k, P.card_eq_multiplicity, ← D.sylow.card_eq_multiplicity,
      D.sylow_card] at h
    omega
  have hle : f.range ≤ automizer D k ⊓ MulAction.stabilizer (MulAut modelF) pointD := by
    rintro a ⟨p, rfl⟩
    refine ⟨⟨inclusion hPN p, rfl⟩, ?_⟩
    exact (action_fix_pointD_iff D k (inclusion hPN p)).mpr (hPC p.property)
  let : Finite modelF := Nat.finite_of_card_ne_zero (modelF_card ▸ (by decide))
  let : Finite (MulAut modelF) := Finite.of_injective
    (fun a : MulAut modelF => (a : modelF → modelF)) DFunLike.coe_injective
  rw [← hcard]
  exact Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)

/-- Ambient fusion supplies all the hypotheses of the finite automizer problem. -/
public theorem finiteSetup (hd : IsConj D.z (into D k d)) :
    FiniteSetup (automizer D k) :=
  ⟨localAutomizer_le D k, stabilizer_pointZ D k,
    automizer_card_eight_mul_odd D k, stabilizer_pointD_card_ge D k hd⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
