module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Factor
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootActions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Relations
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
import Mathlib.Tactic.Group

/-!
# The source actor needed for Held's marked involutions

The four marked elements lie in the symmetric extension. The first three are
conjugate using only the corrected six-point data. The additional source actor
supplies the remaining conjugacy and fuses their commuting threefold product
with pi, whose ambient centralizer has order 384. Injecting a relative centralizer
into that ambient centralizer gives the obstruction involving the prime five.

`RootTranspositionActor` retains the actual earlier alpha relations, fixes the
xi normalization, and records placement of tau'*alpha*tau' in W and the extra
mu-prime conjugation from 5.10. Its existence is not asserted here. In particular,
`commute_v_of_beta_mem` proves the argument of 5.9 from placement alone, without
assuming the extra mu-prime relation. No compatible permutation marking is used.

Source: D. Held, *A Characterization of some multiply transitive permutation
groups, I*, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemmas 2.13, 4.2 and 5.9–5.10, pp.231–238.
Conjugation in the source is x^g = g⁻¹*x*g.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
open NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e) (F : RootFactor D e L)
/-- The four ambient words as actual elements of the symmetric extension. -/
@[expose] public noncomputable def rootMark (i : Fin 4) : (F.W ⊔ zpowers (mu' D e) : Subgroup G) :=
  ⟨![mu' D e, L.v * mu' D e, pi D e * mu D e * mu' D e, xi D e] i,
    F.marked_mem D e L (by fin_cases i <;> simp)⟩
/-- The missing source actor, with the fixed xi used by the six-point data.
This is an intermediate input, not a transposition or recognition hypothesis. -/
public structure RootTranspositionActor where
  relations : AlphaRelations D e 0
  beta_mem : tau' D e * relations.alpha * tau' D e ∈ F.W
  mu'_alpha : relations.alpha⁻¹ * mu' D e * relations.alpha = mu D e * mu' D e
private theorem old_pi : NoncentralAnalysis.Coordinates.pi = modelElement 0 := by decide +kernel
private theorem old_mu : NoncentralAnalysis.Coordinates.mu = modelElement 1 := by decide +kernel
private theorem old_xi : NoncentralAnalysis.Coordinates.xi = modelElement 7 := by decide +kernel
variable (a : RootTranspositionActor D e L F)
public theorem RootTranspositionActor.mu_alpha : a.relations.alpha⁻¹ * mu D e * a.relations.alpha = mu D e * xi D e := by
  simpa only [normalizedXi, Fin.val_zero, pow_zero, one_mul, map_mul, old_pi, old_mu, old_xi, element] using a.relations.mu_alpha
public theorem RootTranspositionActor.xi_alpha : a.relations.alpha⁻¹ * xi D e * a.relations.alpha = mu D e := by
  simpa only [normalizedXi, Fin.val_zero, pow_zero, one_mul, old_mu, old_xi, element] using a.relations.xi_alpha
public theorem RootTranspositionActor.pi_alpha : a.relations.alpha⁻¹ * pi D e * a.relations.alpha = pi D e * xi D e := by
  simpa only [normalizedXi, Fin.val_zero, pow_zero, one_mul, map_mul, old_pi, old_mu, old_xi, element] using a.relations.pi_alpha

local notation "m₀" => rootMark D e L F 0
local notation "m₁" => rootMark D e L F 1
local notation "m₂" => rootMark D e L F 2
local notation "m₃" => rootMark D e L F 3

public theorem rootMark_square (i : Fin 4) : (rootMark D e L F i) ^ 2 = 1 := by
  apply Subtype.ext
  change (![mu' D e, L.v * mu' D e, pi D e * mu D e * mu' D e, xi D e] i) ^ 2 = 1
  fin_cases i
  · exact element_square D e 2 (by decide)
  · change (L.v * mu' D e) ^ 2 = 1
    calc
      _ = L.v * (mu' D e * L.v * mu' D e) := by rw [pow_two, mul_assoc, ← mul_assoc (mu' D e)]
      _ = 1 := by rw [L.mu'_v, mul_inv_cancel]
  · change (pi D e * mu D e * mu' D e) ^ 2 = 1
    have h : (modelElement 0 * modelElement 1 * modelElement 2) ^ 2 = 1 := by decide +kernel
    simpa only [element, map_mul, map_pow, map_one] using congrArg (D.a10ModelEmbedding e) h
  · exact element_square D e 7 (by decide)

public theorem rootMark_zero_odd (s : (F.W ⊔ zpowers (mu' D e) : Subgroup G) ≃* Perm (Fin 7)) :
    Perm.sign (s m₀) ≠ 1 := by
  intro h
  have hm : m₀ ∈ (alternatingGroup (Fin 7)).comap s.toMonoidHom :=
    Perm.mem_alternatingGroup.mpr h
  rw [F.even_subgroup D e L s] at hm
  exact F.mu'_not_mem D e L hm

public theorem rootMark_conj_one : IsConj m₀ m₁ := by
  let v : (F.W ⊔ zpowers (mu' D e) : Subgroup G) :=
    ⟨L.v, (show F.W ≤ F.W ⊔ zpowers (mu' D e) from le_sup_left) (F.A_le D e L L.v_mem)⟩
  have hv3 : L.v ^ 3 = 1 := by rw [← L.v_order, pow_orderOf_eq_one]
  have hv : mu' D e * L.v = L.v⁻¹ * mu' D e := by
    apply mul_right_cancel (b := mu' D e)
    rw [L.mu'_v, mul_assoc, ← pow_two, element_square D e 2 (by decide), mul_one]
  apply isConj_iff.mpr
  refine ⟨v⁻¹, Subtype.ext ?_⟩
  simp only [inv_inv]
  change L.v⁻¹ * mu' D e * L.v = L.v * mu' D e
  calc
    _ = (L.v⁻¹ * L.v⁻¹) * mu' D e := by rw [mul_assoc, hv, ← mul_assoc]
    _ = L.v * mu' D e := by
      congr 1
      calc
        _ = L.v ^ 3 * (L.v⁻¹ * L.v⁻¹) := by rw [hv3, one_mul]
        _ = L.v := by group

public theorem rootMark_conj_two : IsConj m₀ m₂ := by
  let t : (F.W ⊔ zpowers (mu' D e) : Subgroup G) :=
    ⟨tau D e * lam D e, (show F.W ≤ F.W ⊔ zpowers (mu' D e) from le_sup_left) (F.A_le D e L L.tau_lam_mem)⟩
  apply isConj_iff.mpr
  refine ⟨t, Subtype.ext ?_⟩
  have h : (modelElement 3 * modelElement 6) * modelElement 2 *
      (modelElement 3 * modelElement 6)⁻¹ = modelElement 0 * modelElement 1 * modelElement 2 :=
    by decide +kernel
  change (tau D e * lam D e) * mu' D e * (tau D e * lam D e)⁻¹ = pi D e * mu D e * mu' D e
  simpa only [element, map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) h

public theorem RootTranspositionActor.beta_mu' :
    (tau' D e * a.relations.alpha * tau' D e)⁻¹ * mu' D e *
      (tau' D e * a.relations.alpha * tau' D e) = pi D e * mu D e * mu' D e := by
  have ht : tau' D e * mu' D e * tau' D e = mu' D e := by
    simpa only [MulAut.conj_apply, coordinate_inv D e 4 (by decide)] using tau'_mu' D e
  have hc : tau' D e * (mu D e * mu' D e) * tau' D e =
      pi D e * mu D e * mu' D e := by
    have h : modelElement 4 * (modelElement 1 * modelElement 2) * modelElement 4 =
      modelElement 0 * modelElement 1 * modelElement 2 := by decide +kernel
    simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h
  rw [mul_inv_rev, mul_inv_rev, coordinate_inv D e 4 (by decide)]
  calc
    _ = tau' D e * (a.relations.alpha⁻¹ * (tau' D e * mu' D e * tau' D e) *
        a.relations.alpha) * tau' D e := by group
    _ = _ := by rw [ht, a.mu'_alpha, hc]

public theorem RootTranspositionActor.beta_middle :
    (tau' D e * a.relations.alpha * tau' D e)⁻¹ *
      (pi D e * mu D e * mu' D e) *
      (tau' D e * a.relations.alpha * tau' D e) = xi D e := by
  have ht : tau' D e * (pi D e * mu D e * mu' D e) * tau' D e =
      mu D e * mu' D e := by
    have h : modelElement 4 * (modelElement 0 * modelElement 1 * modelElement 2) *
      modelElement 4 = modelElement 1 * modelElement 2 := by decide +kernel
    simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h
  have hc : tau' D e * ((mu D e * xi D e) * (mu D e * mu' D e)) * tau' D e =
      xi D e := by
    have h : modelElement 4 * ((modelElement 1 * modelElement 7) *
      (modelElement 1 * modelElement 2)) * modelElement 4 = modelElement 7 := by decide +kernel
    simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h
  rw [mul_inv_rev, mul_inv_rev, coordinate_inv D e 4 (by decide)]
  calc
    _ = tau' D e * (a.relations.alpha⁻¹ *
        (tau' D e * (pi D e * mu D e * mu' D e) * tau' D e) *
        a.relations.alpha) * tau' D e := by group
    _ = tau' D e * ((a.relations.alpha⁻¹ * mu D e * a.relations.alpha) *
        (a.relations.alpha⁻¹ * mu' D e * a.relations.alpha)) * tau' D e := by rw [ht]; group
    _ = _ := by rw [RootTranspositionActor.mu_alpha D e L F a, a.mu'_alpha, hc]

include a in
public theorem RootTranspositionActor.marked_conjugacy (i : Fin 4) : IsConj m₀ (rootMark D e L F i) := by
  fin_cases i
  · exact IsConj.refl _
  · exact rootMark_conj_one D e L F
  · exact rootMark_conj_two D e L F
  · let b : (F.W ⊔ zpowers (mu' D e) : Subgroup G) :=
      ⟨tau' D e * a.relations.alpha * tau' D e, (show F.W ≤ F.W ⊔ zpowers (mu' D e) from le_sup_left) a.beta_mem⟩
    have h01 : IsConj m₀ m₂ := isConj_iff.mpr ⟨b⁻¹, Subtype.ext (by
      simp only [inv_inv]
      change (tau' D e * a.relations.alpha * tau' D e)⁻¹ * mu' D e *
        (tau' D e * a.relations.alpha * tau' D e) = pi D e * mu D e * mu' D e
      exact RootTranspositionActor.beta_mu' D e L F a)⟩
    have h12 : IsConj m₂ m₃ := isConj_iff.mpr ⟨b⁻¹, Subtype.ext (by
      simp only [inv_inv]
      change (tau' D e * a.relations.alpha * tau' D e)⁻¹ * (pi D e * mu D e * mu' D e) *
        (tau' D e * a.relations.alpha * tau' D e) = xi D e
      exact RootTranspositionActor.beta_middle D e L F a)⟩
    exact h01.trans h12

include a in
public theorem RootTranspositionActor.pi_fusion [Finite G] : IsConj D.z (pi D e * mu D e * xi D e) := by
  rw [← pi_eq D e]
  apply isConj_iff.mpr
  refine ⟨a.relations.alpha⁻¹ * a.relations.alpha⁻¹, ?_⟩
  calc
    _ = a.relations.alpha⁻¹ * (a.relations.alpha⁻¹ * pi D e * a.relations.alpha) *
        a.relations.alpha := by simp only [mul_inv_rev, inv_inv, mul_assoc]
    _ = (a.relations.alpha⁻¹ * pi D e * a.relations.alpha) *
        (a.relations.alpha⁻¹ * xi D e * a.relations.alpha) := by
      conv_lhs => rw [RootTranspositionActor.pi_alpha D e L F a]
      group
    _ = (pi D e * xi D e) * mu D e := by rw [RootTranspositionActor.pi_alpha D e L F a, RootTranspositionActor.xi_alpha D e L F a]
    _ = _ := by rw [mul_assoc, (mu_commute_xi D e).symm.eq, ← mul_assoc]

public theorem rootMark_triple_val : ((m₀ * m₂ * m₃ : (F.W ⊔ zpowers (mu' D e) : Subgroup G)) : G) =
    pi D e * mu D e * xi D e := by
  change mu' D e * (pi D e * mu D e * mu' D e) * xi D e = _
  have h : modelElement 2 * (modelElement 0 * modelElement 1 * modelElement 2) *
    modelElement 7 = modelElement 0 * modelElement 1 * modelElement 7 := by decide +kernel
  simpa only [rootMark, element, map_mul] using congrArg (D.a10ModelEmbedding e) h

public theorem rootMark_commuting : Commute m₀ m₂ ∧ Commute m₀ m₃ ∧ Commute m₂ m₃ := by
  have h : Commute (modelElement 2) (modelElement 0 * modelElement 1 * modelElement 2) ∧
    Commute (modelElement 2) (modelElement 7) ∧
    Commute (modelElement 0 * modelElement 1 * modelElement 2) (modelElement 7) := by
    change _ * _ = _ * _ ∧ _ * _ = _ * _ ∧ _ * _ = _ * _
    decide +kernel
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · change mu' D e * (pi D e * mu D e * mu' D e) = (pi D e * mu D e * mu' D e) * mu' D e
    simpa only [map_mul, element] using (h.1.map (D.a10ModelEmbedding e)).eq
  · exact (h.2.1.map (D.a10ModelEmbedding e)).eq
  · change (pi D e * mu D e * mu' D e) * xi D e = xi D e * (pi D e * mu D e * mu' D e)
    simpa only [map_mul, element] using (h.2.2.map (D.a10ModelEmbedding e)).eq

public theorem rootMark_distinct : m₀ ≠ m₂ ∧ m₀ ≠ m₃ ∧ m₂ ≠ m₃ := by
  have h : modelElement 2 ≠ modelElement 0 * modelElement 1 * modelElement 2 ∧
    modelElement 2 ≠ modelElement 7 ∧
    modelElement 0 * modelElement 1 * modelElement 2 ≠ modelElement 7 := by decide +kernel
  constructor
  · intro he
    apply h.1
    apply D.a10ModelEmbedding_injective e
    simpa [rootMark, element, map_mul] using congrArg (fun x : (F.W ⊔ zpowers (mu' D e) : Subgroup G) => (x : G)) he
  constructor
  · intro he
    apply h.2.1
    apply D.a10ModelEmbedding_injective e
    exact congrArg (fun x : (F.W ⊔ zpowers (mu' D e) : Subgroup G) => (x : G)) he
  · intro he
    apply h.2.2
    apply D.a10ModelEmbedding_injective e
    simpa [rootMark, element, map_mul] using congrArg (fun x : (F.W ⊔ zpowers (mu' D e) : Subgroup G) => (x : G)) he

public theorem commute_v_of_beta_mem (alpha : G)
    (hbeta : tau' D e * alpha * tau' D e ∈ F.W) : Commute alpha L.v := by
  let t := MulAut.conj (tau' D e)
  have hroot : t (L.u * L.v) = L.v⁻¹ := by
    simpa only [t, MulAut.conj_apply, coordinate_inv D e 4 (by decide)] using tau'_root D e L
  have ha : t (tau' D e * alpha * tau' D e) = alpha := by
    simp only [t, MulAut.conj_apply, coordinate_inv D e 4 (by decide)]
    have ht : tau' D e * tau' D e = 1 := by
      simpa only [pow_two] using element_square D e 4 (by decide)
    simp only [mul_assoc, ht, mul_one]
    rw [← mul_assoc, ht, one_mul]
  have h : Commute (L.u * L.v) (tau' D e * alpha * tau' D e) :=
    (show Commute (tau' D e * alpha * tau' D e) (L.u * L.v) from
      mem_centralizer_singleton_iff.mp (F.W_le_centralizer D e L hbeta)).symm
  have h' := h.map t.toMonoidHom
  change Commute (t (L.u * L.v)) (t (tau' D e * alpha * tau' D e)) at h'
  rw [hroot, ha] at h'
  exact (Commute.inv_left_iff.mp h').symm

include a in
public theorem RootTranspositionActor.triple_centralizer_not_five [Finite G]
    (s : (F.W ⊔ zpowers (mu' D e) : Subgroup G) ≃* Perm (Fin 7)) :
    ¬ 5 ∣ Nat.card (centralizer ({s (m₀ * m₂ * m₃)} : Set (Perm (Fin 7)))) := by
  let f : Perm (Fin 7) →* G := (F.W ⊔ zpowers (mu' D e) : Subgroup G).subtype.comp
    s.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp s.symm.injective
  let t := s (m₀ * m₂ * m₃)
  have ht : f t = pi D e * mu D e * xi D e := by
    change (s.symm (s (m₀ * m₂ * m₃)) : G) = _
    rw [s.symm_apply_apply]
    exact rootMark_triple_val D e L F
  let j : centralizer ({t} : Set (Perm (Fin 7))) →* centralizer ({f t} : Set G) :=
    (f.comp (Subgroup.subtype (centralizer ({t} : Set (Perm (Fin 7)))))).codRestrict _ (fun y => by
      apply mem_centralizer_singleton_iff.mpr
      exact (show Commute (y : Perm (Fin 7)) t from
        mem_centralizer_singleton_iff.mp y.property).map f)
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply hf
    exact congrArg (fun z : centralizer ({f t} : Set G) => (z : G)) he
  have hd := card_dvd_of_injective j hj
  rw [ht, NoncentralAnalysis.Fusion.centralizer_card_of_isConj D (RootTranspositionActor.pi_fusion D e L F a)] at hd
  intro h
  have hbad : 5 ∣ 384 := h.trans hd
  norm_num at hbad

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
