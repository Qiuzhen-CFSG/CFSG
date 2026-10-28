module

public import Theory.GroupTheory.SetStrongClosure
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Strongly closed sets under surjective maps

The image of a strongly closed subset of a Sylow subgroup is strongly closed
in the image Sylow subgroup. No hypothesis on the kernel is needed. Lift a
conjugator and use Sylow conjugacy inside the preimage of the image Sylow.
The adjusting conjugator has an image in that Sylow; a second conjugation
inside the original Sylow removes this adjustment.

This is the set version of the usual quotient fusion argument, used for the
unitary terminal case of Aschbacher (1975), Lemma 3.4, pp.94–96.
-/

open Subgroup
open scoped Pointwise
open MulAction

namespace Theory.GroupTheory

/-- Strong closure of a set passes through any surjective homomorphism. -/
public theorem IsStronglyClosedSet.image {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) {U : Set G}
    (hc : IsStronglyClosedSet U (S : Subgroup G) ⊤)
    (q : G →* H) (hq : Function.Surjective q) :
    IsStronglyClosedSet (q '' U) ((S : Subgroup G).map q) ⊤ := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_map_of_mem q (hc.1 hx)
  · rintro _ ⟨x, hx, rfl⟩ b _ hb
    obtain ⟨g, rfl⟩ := hq b
    let K := ((S : Subgroup G).map q).comap q
    let P := (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom
    have hSK : (S : Subgroup G) ≤ K := le_comap_map q S
    have hPK : P ≤ K := by
      dsimp only [P]
      rw [MonoidHom.map_zpowers]
      apply zpowers_le.mpr
      simpa [K, MulAut.conj_apply] using hb
    have hP : IsPGroup p P :=
      (S.isPGroup'.to_le (zpowers_le.mpr (hc.1 hx))).map _
    have hPKp : IsPGroup p (P.subgroupOf K) :=
      hP.comap_of_injective K.subtype K.subtype_injective
    obtain ⟨T, hPT⟩ := hPKp.exists_le_sylow
    obtain ⟨k, hk⟩ := exists_smul_eq K T (S.subtype hSK)
    have hyP : g⁻¹ * x * g ∈ P := by
      simp [P]
    have hyK : g⁻¹ * x * g ∈ K := hPK hyP
    have hyT : (⟨g⁻¹ * x * g, hyK⟩ : K) ∈ (T : Subgroup K) :=
      hPT hyP
    have hyS : (k : G) * (g⁻¹ * x * g) * (k : G)⁻¹ ∈ (S : Subgroup G) := by
      have hm : k * (⟨g⁻¹ * x * g, hyK⟩ : K) * k⁻¹ ∈
          (S.subtype hSK : Subgroup K) := by
        rw [← hk]
        exact mem_map_of_mem (MulAut.conj k).toMonoidHom hyT
      exact hm
    have hyU : (k : G) * (g⁻¹ * x * g) * (k : G)⁻¹ ∈ U := by
      have hh := hc.2 x hx (g * (k : G)⁻¹) (mem_top _) (by
        simpa [mul_assoc] using hyS)
      simpa [mul_assoc] using hh
    obtain ⟨s, hs, hqs⟩ := k.property
    have hzS : s⁻¹ * ((k : G) * (g⁻¹ * x * g) * (k : G)⁻¹) * s ∈
        (S : Subgroup G) := mul_mem (mul_mem (inv_mem hs) hyS) hs
    refine ⟨_, hc.2 _ hyU s (mem_top _) hzS, ?_⟩
    simp only [map_mul, map_inv, hqs]
    group

end Theory.GroupTheory
