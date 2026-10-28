module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1AmalgamRigidity.Overlap
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer
public import Theory.GroupTheory.CentralDisplacementOddIndex
import Mathlib.Tactic.Group

/-!
# Assembly of the actual max1-centralizer rigidity argument

After the first correction fixes E pointwise, a centralizer correction has
right displacement in the marked line ⟨v⟩ on C. This implies that its
conjugator normalizes E, hence lies in M. The commutator-image criterion
puts the conjugator in E. Relative rigidity on M then gives conjugation
by v^epsilon and fixes H pointwise. Odd index of D in C kills the central
displacement homomorphism. Generation by C and M identifies the global
automorphism, and undoing both corrections supplies an actual conjugator.

The two correction hypotheses are explicit in this conditional assembly.
They are not claims of generation or full Janko innerness. The owning
`Max1AmalgamRigidity` producer must discharge them before exposing an
endpoint whose only additional premise is C ⊔ M = ⊤.

Source context: GLS3 Table 5.3i, printed p.270. Every local input here is
about the literal ATLAS model and the marked pair from `Core`.
-/

set_option backward.isDefEq.respectTransparency true
public section

namespace Janko4.Max1AmalgamRigidity
open Subgroup
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel Cardinality.localX Cardinality.localY Cardinality.localKernelSeed

theorem normalizer_E_eq : normalizer (E : Set Model) = M := by
  apply le_antisymm LocalStructure.normalizer_embedded_localKernel_le_max1
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    K.le_normalizer_map M.subtype

private theorem map_eq_of_maps_to {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) (alpha : MulAut G) (h : ∀ g ∈ U, alpha g ∈ U) :
    U.map alpha.toMonoidHom = U := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g, hg, rfl⟩
    exact h g hg
  · exact (Nat.card_congr (alpha.subgroupMap U).toEquiv).le

private theorem map_M_of_fixes_E (alpha : MulAut Model)
    (he : ∀ e ∈ E, alpha e = e) : M.map alpha.toMonoidHom = M := by
  have hE : E.map alpha.toMonoidHom = E :=
    map_eq_of_maps_to E alpha (fun e he' => (he e he').symm ▸ he')
  have hn := E.map_equiv_normalizer_eq alpha
  rwa [hE, normalizer_E_eq] at hn

private theorem map_C_of_fixes_v (alpha : MulAut Model) (hv : alpha v = v) :
    C.map alpha.toMonoidHom = C := by
  apply map_eq_of_maps_to C alpha
  intro t ht
  apply mem_centralizer_singleton_iff.mpr
  have h := congrArg alpha (mem_centralizer_singleton_iff.mp ht)
  simpa only [map_mul, hv] using h

/-- A pointwise kernel fixer is inner once its centralizer restriction can
be corrected to have displacement in the marked central binary line. -/
theorem inner_of_fixes_kernel_of_centralizer_correction
    (hgen : C ⊔ M = ⊤) (alpha : MulAut Model)
    (hfix : ∀ e ∈ E, alpha e = e)
    (c : C)
    (hdisp : ∀ t ∈ C,
      t⁻¹ * (MulAut.conj (c : Model)⁻¹ * alpha) t ∈ zpowers v) :
    ∃ g : Model, alpha = MulAut.conj g := by
  let beta : MulAut Model := MulAut.conj (c : Model)⁻¹ * alpha
  have hvC : v ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hline : zpowers v ≤ E := zpowers_le.mpr v_mem_E
  have hbetaE (e : Model) (he : e ∈ E) : beta e ∈ E := by
    have hd := E.mul_mem he (hline (hdisp e (E_le_C he)))
    simpa only [mul_inv_cancel_left] using hd
  have hcN : (c : Model)⁻¹ ∈ normalizer (E : Set Model) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply map_eq_of_maps_to E (MulAut.conj (c : Model)⁻¹)
    intro e he
    have hb := hbetaE e he
    change (c : Model)⁻¹ * alpha e * ((c : Model)⁻¹)⁻¹ ∈ E at hb
    change (c : Model)⁻¹ * e * ((c : Model)⁻¹)⁻¹ ∈ E
    simpa only [hfix e he] using hb
  have hcM : (c : Model) ∈ M := by
    rw [← normalizer_E_eq]
    simpa only [inv_inv] using (normalizer (E : Set Model)).inv_mem hcN
  let cm : M := ⟨c, hcM⟩
  have hcmK : cm ∈ K := by
    apply Max1RelativeRigidity.mem_kernel_of_commutator_image cm
    intro e
    have he : ((e : M) : Model) ∈ E := mem_map.mpr ⟨e, e.property, rfl⟩
    apply (mem_map_iff_mem M.subtype_injective).mp
    rw [MonoidHom.map_zpowers]
    change (c : Model)⁻¹ * ((e : M) : Model) * (c : Model) *
      ((e : M) : Model)⁻¹ ∈ zpowers v
    have hb : beta ((e : M) : Model) =
        (c : Model)⁻¹ * ((e : M) : Model) * (c : Model) := by
      change (c : Model)⁻¹ * alpha ((e : M) : Model) * ((c : Model)⁻¹)⁻¹ = _
      rw [hfix _ he, inv_inv]
    rw [← hb, (E_commute (hbetaE _ he) (E.inv_mem he)).eq]
    exact hdisp _ (E_le_C he)
  have hcE : (c : Model) ∈ E := mem_map.mpr ⟨cm, hcmK, rfl⟩
  have hbetaFix (e : Model) (he : e ∈ E) : beta e = e := by
    change (c : Model)⁻¹ * alpha e * ((c : Model)⁻¹)⁻¹ = e
    rw [hfix e he, inv_inv, (E_commute (E.inv_mem hcE) he).eq]
    group
  have hbetaM := map_M_of_fixes_E beta hbetaFix
  let phi : MulAut M := (beta.subgroupMap M).trans (MulEquiv.subgroupCongr hbetaM)
  have hphi (m : M) : (phi m : Model) = beta m := rfl
  obtain ⟨epsilon, hepsilon⟩ := Max1RelativeRigidity.relative_cocycle_rigidity phi
    (fun e => M.subtype_injective (hbetaFix e (mem_map.mpr ⟨e, e.property, rfl⟩)))
    (by
      intro m hm
      apply (mem_map_iff_mem M.subtype_injective).mp
      rw [MonoidHom.map_zpowers]
      exact hdisp m (mem_centralizer_singleton_iff.mpr (congrArg M.subtype hm.eq)))
  have hbetaOnM (m : Model) (hm : m ∈ M) :
      beta m = v ^ epsilon.val * m * (v ^ epsilon.val)⁻¹ := by
    exact congrArg M.subtype (DFunLike.congr_fun hepsilon ⟨m, hm⟩)
  have hbetaOnH (h : Model) (hh : h ∈ H) : beta h = h := by
    obtain ⟨hm, hc⟩ := mem_H_iff.mp hh
    rw [hbetaOnM h hm]
    have hcomm : Commute h v := mem_centralizer_singleton_iff.mp hc
    rw [← (hcomm.pow_right epsilon.val).eq]
    group
  have hbetaC := map_C_of_fixes_v beta (hbetaFix v v_mem_E)
  let psi : MulAut C := (beta.subgroupMap C).trans (MulEquiv.subgroupCongr hbetaC)
  let vc : C := ⟨v, hvC⟩
  have hpsi : psi = 1 := by
    apply MulAut.eq_one_of_central_displacement_of_odd_index vc
      (Subtype.ext v_sq)
      (by
        rw [mem_center_iff]
        intro t
        exact Subtype.ext (mem_centralizer_singleton_iff.mp t.property))
      psi
    · intro t
      apply (mem_map_iff_mem C.subtype_injective).mp
      rw [MonoidHom.map_zpowers]
      exact hdisp t t.property
    · exact D_index_odd
    · intro t ht
      exact Subtype.ext (hbetaOnH t ht)
  have hbetaOnC (t : Model) (ht : t ∈ C) : beta t = t :=
    congrArg C.subtype (DFunLike.congr_fun hpsi ⟨t, ht⟩)
  have hinner : beta = MulAut.conj (v ^ epsilon.val) := by
    let F := beta.toMonoidHom.eqLocus (MulAut.conj (v ^ epsilon.val)).toMonoidHom
    have hC : C ≤ F := by
      intro t ht
      change beta t = v ^ epsilon.val * t * (v ^ epsilon.val)⁻¹
      rw [hbetaOnC t ht]
      have hcomm : Commute t v := mem_centralizer_singleton_iff.mp ht
      rw [← (hcomm.pow_right epsilon.val).eq]
      group
    have hM : M ≤ F := hbetaOnM
    have ht : (⊤ : Subgroup Model) ≤ F := hgen ▸ sup_le hC hM
    exact MulEquiv.ext (fun t => ht (mem_top t))
  refine ⟨(c : Model) * v ^ epsilon.val, ?_⟩
  have halpha : alpha = MulAut.conj (c : Model) * beta := by
    dsimp only [beta]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [halpha, hinner, ← map_mul]

/-- Conditional assembly from the two independent local corrections. The
generation premise remains separate; this theorem does not construct it. -/
theorem conj_surjective_of_local_corrections
    (hfirst : ∀ alpha : MulAut Model, ∃ g : Model,
      ∀ e ∈ E, (MulAut.conj g⁻¹ * alpha) e = e)
    (hlocal : ∀ alpha : MulAut Model, alpha v = v → ∃ c : C,
      ∀ t ∈ C, t⁻¹ * (MulAut.conj (c : Model)⁻¹ * alpha) t ∈ zpowers v)
    (hgen : C ⊔ M = ⊤) :
    Function.Surjective (MulAut.conj : Model →* MulAut Model) := by
  intro alpha
  obtain ⟨g, hg⟩ := hfirst alpha
  let delta := MulAut.conj g⁻¹ * alpha
  obtain ⟨c, hc⟩ := hlocal delta (hg v v_mem_E)
  obtain ⟨k, hk⟩ := inner_of_fixes_kernel_of_centralizer_correction hgen delta hg c hc
  refine ⟨g * k, ?_⟩
  have halpha : alpha = MulAut.conj g * delta := by
    dsimp only [delta]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [halpha, hk, map_mul]

end Janko4.Max1AmalgamRigidity
