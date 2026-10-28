module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Normality through faithful quotient representations

If a subgroup containing F maps to a normal subgroup under a faithful
representation of M/F, it is normal in M. Pull back first along the
representation and then along the quotient map. The same normal subgroup
restricts to every overgroup, retaining its full image in the ambient group.

Application: the point-stabilizer normality step in Aschbacher--Smith,
*The Classification of Quasithin Groups*, Lemma 14.2.21, printed p.989.
-/

namespace Subgroup

/-- Normality is detected by a faithful representation of a quotient. -/
public theorem normal_of_faithful_quotient_image {M L : Type*} [Group M] [Group L]
    (F Q : Subgroup M) [F.Normal] (hFQ : F ≤ Q)
    (ρ : M ⧸ F →* L) (hρ : Function.Injective ρ)
    (N : Subgroup L) [N.Normal]
    (hQN : (Q.map (QuotientGroup.mk' F)).map ρ = N) : Q.Normal := by
  let K := Q.map (QuotientGroup.mk' F)
  have hK : K = N.comap ρ := by
    rw [← hQN]
    exact (Subgroup.comap_map_eq_self (by
      rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hρ]
      exact bot_le)).symm
  have hKN : K.Normal := by rw [hK]; infer_instance
  have hQ : Q = K.comap (QuotientGroup.mk' F) := by
    exact (Subgroup.comap_map_eq_self (by simpa using hFQ)).symm
  rw [hQ]
  infer_instance


/-- A normal subgroup remains normal in every overgroup, with the same
ambient image. -/
public theorem normal_subgroupOf_and_map_eq
    {L : Type*} [Group L] (N M : Subgroup L) [N.Normal] (hNM : N ≤ M) :
    (N.subgroupOf M).Normal ∧ (N.subgroupOf M).map M.subtype = N :=
  ⟨inferInstance, map_subgroupOf_eq_of_le hNM⟩

end Subgroup
