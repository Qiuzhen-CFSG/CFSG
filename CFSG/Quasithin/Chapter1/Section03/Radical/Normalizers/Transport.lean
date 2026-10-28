module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Quotient

/-!
# Transport of the radical construction to local overgroups

Faithful embeddings commute with Ξ_p: transport the p-core of the two-core
quotient, its first omega subgroup, the full preimage, and finally O².
This identifies the radical constructed in LT with the one in G, so the
normality argument can be carried out with L normal only in LT.

Source: Aschbacher–Smith, proof of Proposition 1.3.8, printed pp.512–513.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
variable {G H : Type*} [Group G] [Group H]
private theorem omega_map_equiv (p k : ℕ) (e : G ≃* H) :
    (omega G (p := p) k).map e.toMonoidHom = omega H (p := p) k := by
  rw [omega, omega, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using congrArg e hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    simpa using congrArg e.symm hx

private theorem omega_core_map_equiv (p : ℕ) (e : G ≃* H) :
    (((omega (pCore p G) (p := p) 1).map (pCore p G).subtype).map e.toMonoidHom) =
      (omega (pCore p H) (p := p) 1).map (pCore p H).subtype := by
  have hp : (pCore p G).map (e : G →* H) = pCore p H := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using pCore_map_iso p e
  let ep : pCore p G ≃* pCore p H :=
    (e.subgroupMap (pCore p G)).trans (MulEquiv.subgroupCongr hp)
  have he := congrArg (map (pCore p H).subtype) (omega_map_equiv p 1 ep)
  have hc : (pCore p H).subtype.comp ep.toMonoidHom =
      e.toMonoidHom.comp (pCore p G).subtype := by
    ext x
    change ((ep x : pCore p H) : H) = e x
    dsimp only [ep]
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    exact e.coe_subgroupMap_apply (pCore p G) x
  simpa only [map_map, hc] using he

private theorem preimage_map_equiv {L : Subgroup G} {K : Subgroup H}
    (p : ℕ) (e : L ≃* K) :
    (xiPPreimage p L).map e.toMonoidHom = xiPPreimage p K := by
  let eq : XiQuotient L ≃* XiQuotient K :=
    QuotientGroup.congr (pCore 2 L) (pCore 2 K) e (pCore_map_iso 2 e)
  have he : (xiOmegaCore p L).map eq.toMonoidHom = xiOmegaCore p K :=
    omega_core_map_equiv p eq
  have hc (x : L) : eq (QuotientGroup.mk' (pCore 2 L) x) =
      QuotientGroup.mk' (pCore 2 K) (e x) := QuotientGroup.congr_mk' _ _ e _ x
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change QuotientGroup.mk' (pCore 2 K) (e y) ∈ xiOmegaCore p K
    rw [← he, ← hc]
    exact mem_map.mpr ⟨_, hy, rfl⟩
  · intro hx
    refine mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change QuotientGroup.mk' (pCore 2 L) (e.symm x) ∈ xiOmegaCore p L
    have hh : eq (QuotientGroup.mk' (pCore 2 L) (e.symm x)) ∈ xiOmegaCore p K := by
      rw [hc, e.apply_symm_apply]
      exact hx
    rw [← he] at hh
    simpa only [e.symm_apply_apply, eq.symm_apply_apply] using (mem_map_equiv).mp hh

variable [Finite G]
/-- Faithful changes of ambient group preserve the actual Ξ_p construction. -/
public theorem XiP_map_injective (p : ℕ) (L : Subgroup G) (f : G →* H)
    (hf : Function.Injective f) : (XiP p L).map f = XiP p (L.map f) := by
  let e := L.equivMapOfInjective f hf
  have he : (xiPIn p L).map e.toMonoidHom = xiPIn p (L.map f) := by
    unfold xiPIn
    rw [map_embedded_pResidual, preimage_map_equiv p e]
  have hh := congrArg (map (L.map f).subtype) he
  have hc : (L.map f).subtype.comp e.toMonoidHom = f.comp L.subtype := by
    ext x
    simp [e]
  simpa only [XiP, map_map, hc] using hh
end CFSG.Quasithin.Chapter1.RadicalNormalizers
