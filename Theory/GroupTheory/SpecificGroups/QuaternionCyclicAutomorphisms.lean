module

public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicRestrictions
public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicCentralSign
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Automorphisms and the two-residual of Q₈ ◦ C₄

Restriction to the characteristic quaternion factor and the sign on the central
generator identify the full automorphism group with `Aut(Q₈) × C₂`. Agreement
on both coordinates implies agreement on the generating factors. Surjectivity
follows by adjusting a lift of the central sign with a quaternion extension.

The two-residual has trivial central sign. Consequently each of its elements
is the extension of its quaternion restriction, giving a literal equality of
subgroups in the original automorphism group. This preserves the embedded
action and does not require the separate identification with `A₄`.

Source: the Q₈ ◦ C₄ calculation in the proof of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 14.2.21, printed p.988
(PDF p.1005). This module supplies intrinsic automorphism and residual
calculations; the local-group image comparison belongs to the application.
-/

public section

namespace QuaternionCyclic

/-- Equal central signs mean equal actions on the central generator. -/
theorem sign_eq_iff_r_eq (e f : MulAut Model) :
    centralSign e = centralSign f ↔ e r = f r := by
  constructor
  · intro h
    by_cases he : e r = r
    · have hf := (centralSign_eq_one_iff f).mp
        (h.symm.trans ((centralSign_eq_one_iff e).mpr he))
      exact he.trans hf.symm
    · have hf : f r ≠ r := by
        intro hf
        exact he ((centralSign_eq_one_iff e).mp
          (h.trans ((centralSign_eq_one_iff f).mpr hf)))
      exact ((aut_r_eq_or_inv e).resolve_left he).trans
        ((aut_r_eq_or_inv f).resolve_left hf).symm
  · intro h
    simp only [centralSign_apply, h]

/-- The actual restriction and central-sign homomorphisms, paired together. -/
noncomputable def autCoordinatesHom : MulAut Model →*
    (MulAut (QuaternionGroup 2) × Multiplicative (ZMod 2)) :=
  restrictionHom.prod centralSign

/-- Restriction and central sign are independent and determine the automorphism. -/
theorem autCoordinatesHom_bijective : Function.Bijective autCoordinatesHom := by
  constructor
  · intro e f h
    exact aut_ext_restriction_r (congrArg Prod.fst h)
      ((sign_eq_iff_r_eq e f).mp (congrArg Prod.snd h))
  · rintro ⟨e, s⟩
    obtain ⟨f, hf⟩ := centralSign_surjective s
    refine ⟨extendAutHom (e * (restrictionHom f)⁻¹) * f, ?_⟩
    apply Prod.ext
    · change restrictionHom (extendAutHom (e * (restrictionHom f)⁻¹) * f) = e
      simp only [map_mul, restrictionHom_extendAutHom, inv_mul_cancel_right]
    · change centralSign (extendAutHom (e * (restrictionHom f)⁻¹) * f) = s
      rw [map_mul, centralSign_extendAutHom, one_mul, hf]

/-- The intrinsic direct-product decomposition of the automorphism group. -/
noncomputable def autEquiv : MulAut Model ≃*
    (MulAut (QuaternionGroup 2) × Multiplicative (ZMod 2)) :=
  MulEquiv.ofBijective autCoordinatesHom autCoordinatesHom_bijective

/-- The coordinates retain the supplied restriction and central-sign maps. -/
@[simp] theorem autEquiv_apply (e : MulAut Model) :
    autEquiv e = (restrictionHom e, centralSign e) := by
  apply Prod.ext <;> rfl

/-- The first coordinate acts on the actual embedded quaternion factor. -/
theorem autEquiv_quaternion (e : MulAut Model) (q : QuaternionGroup 2) :
    quaternionEmbedding ((autEquiv e).1 q) = e (quaternionEmbedding q) :=
  restrictionHom_quaternion e q

/-- The second coordinate is trivial exactly when the central generator is fixed. -/
@[simp] theorem autEquiv_sign_eq_one_iff (e : MulAut Model) :
    (autEquiv e).2 = 1 ↔ e r = r := centralSign_eq_one_iff e

/-- The second coordinate specifies the full action on the central generator. -/
theorem autEquiv_r (e : MulAut Model) :
    e r = if (autEquiv e).2 = 1 then r else r⁻¹ := by
  by_cases h : e r = r
  · rw [if_pos ((autEquiv_sign_eq_one_iff e).mpr h)]
    exact h
  · rw [if_neg (fun hs => h ((autEquiv_sign_eq_one_iff e).mp hs))]
    exact (aut_r_eq_or_inv e).resolve_left h

/-- Quaternion extension is the inclusion of the first direct factor. -/
@[simp] theorem autEquiv_extendAutHom (e : MulAut (QuaternionGroup 2)) :
    autEquiv (extendAutHom e) = (e, 1) := by
  rw [autEquiv_apply, restrictionHom_extendAutHom, centralSign_extendAutHom]

/-- The inverse equivalence on the first direct factor is the supplied extension. -/
@[simp] theorem autEquiv_symm_one (e : MulAut (QuaternionGroup 2)) :
    autEquiv.symm (e, 1) = extendAutHom e := by
  apply autEquiv.injective
  rw [autEquiv.apply_symm_apply, autEquiv_extendAutHom]

/-- An automorphism fixing the central generator is its quaternion extension. -/
theorem extend_restriction_of_sign_one (e : MulAut Model)
    (he : centralSign e = 1) : extendAutHom (restrictionHom e) = e := by
  apply aut_ext_restriction_r (restrictionHom_extendAutHom _)
  exact ((centralSign_eq_one_iff _).mp (centralSign_extendAutHom _)).trans
    ((centralSign_eq_one_iff e).mp he).symm

private theorem sign_residual_bot : pResidual 2 (Multiplicative (ZMod 2)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  have hp : IsPGroup 2 (Multiplicative (ZMod 2)) := by
    intro x
    refine ⟨1, ?_⟩
    have h : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
    exact h x
  exact sInf_le ⟨inferInstance, hp.to_quotient ⊥⟩

/-- The two-residual acts trivially on the central cyclic factor. -/
theorem pResidual_le_centralSign_ker :
    pResidual 2 (MulAut Model) ≤ centralSign.ker := by
  intro e he
  have h := Subgroup.map_pResidual_le 2 centralSign
    (Subgroup.mem_map.mpr ⟨e, he, rfl⟩)
  rw [sign_residual_bot] at h
  exact h

/-- The two-residual is exactly the extension of the quaternion two-residual. -/
theorem pResidual_eq_map_extendAutHom :
    pResidual 2 (MulAut Model) =
      (pResidual 2 (MulAut (QuaternionGroup 2))).map extendAutHom := by
  apply le_antisymm ?_ (Subgroup.map_pResidual_le 2 extendAutHom)
  intro e he
  refine Subgroup.mem_map.mpr ⟨restrictionHom e, ?_, ?_⟩
  · exact Subgroup.map_pResidual_le 2 restrictionHom
      (Subgroup.mem_map.mpr ⟨e, he, rfl⟩)
  · exact extend_restriction_of_sign_one e (pResidual_le_centralSign_ker he)

end QuaternionCyclic

end
