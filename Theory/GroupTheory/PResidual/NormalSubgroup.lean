module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Recognition of a normal p-perfect subgroup as the p-residual

A p-perfect subgroup lies in the ambient p-residual, by functoriality of
residuals. If it is normal with p-group quotient, the reverse inclusion
follows from the definition. In particular, adjoining a p-subgroup to a
normal p-perfect subgroup does not change its residual. The resulting
characteristic subgroup is the induction step in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma A.4.2(2), printed p. 57.
-/

namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}

/-- Every p-perfect subgroup lies in the ambient p-residual. -/
public theorem le_pResidual_of_isPPerfect (H : Subgroup G) (hH : IsPPerfect p H) :
    H ≤ pResidual p G := by
  have h := map_pResidual_le p H.subtype
  rw [(pResidual_eq_top_iff p H).mpr hH] at h
  intro x hx
  exact h ⟨⟨x, hx⟩, trivial, rfl⟩

/-- A normal p-perfect subgroup with p-group quotient is the p-residual. -/
public theorem pResidual_eq_of_isPPerfect (H : Subgroup G) [H.Normal]
    (hH : IsPPerfect p H) (hq : IsPGroup p (G ⧸ H)) :
    pResidual p G = H :=
  le_antisymm (sInf_le ⟨inferInstance, hq⟩) (le_pResidual_of_isPPerfect H hH)

/-- Such a normal subgroup is in fact characteristic. -/
public theorem characteristic_of_isPPerfect_quotient (H : Subgroup G) [H.Normal]
    (hH : IsPPerfect p H) (hq : IsPGroup p (G ⧸ H)) : H.Characteristic := by
  rw [← pResidual_eq_of_isPPerfect H hH hq]
  infer_instance

/-- A p-subgroup supplement makes the quotient a p-group. -/
public theorem isPGroup_quotient_of_sup_eq_top (H R : Subgroup G) [H.Normal]
    (hR : IsPGroup p R) (hsup : H ⊔ R = ⊤) : IsPGroup p (G ⧸ H) := by
  let q := QuotientGroup.mk' H
  have hrange : R.map q = ⊤ := by
    have h := congrArg (fun K : Subgroup G => K.map q) hsup
    simpa [map_sup, q, map_top_of_surjective _ (QuotientGroup.mk'_surjective H)] using h
  exact hR.of_surjective (q.comp R.subtype) (MonoidHom.range_eq_top.mp (by
    simpa [MonoidHom.range_comp] using hrange))

/-- Adjoining a p-subgroup to a normal p-perfect subgroup preserves the residual. -/
public theorem pResidual_eq_of_isPPerfect_sup (H R : Subgroup G) [H.Normal]
    (hH : IsPPerfect p H) (hR : IsPGroup p R) (hsup : H ⊔ R = ⊤) :
    pResidual p G = H :=
  pResidual_eq_of_isPPerfect H hH (isPGroup_quotient_of_sup_eq_top H R hR hsup)
end Subgroup
