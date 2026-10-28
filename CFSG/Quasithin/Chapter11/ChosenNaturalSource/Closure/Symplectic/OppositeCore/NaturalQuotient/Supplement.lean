module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Pair

/-!
# The point-transitivity supplement in the opposite-core argument

The source transitivity concerns conjugates of V₁ inside V which are not
contained in V₃. If M₁ preserves V and V₃, its orbit of the chosen opposite
point stays in this set. An L₁-element has the same image on that point;
the quotient of the two elements belongs to the literal stabilizer
N_M₁(V₁ʸ). This proves M₁=L₁ N_M₁(V₁ʸ).
The transitivity and flag invariance are preceding geometric inputs.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

private theorem map_conj_mul {G : Type*} [Group G] (A : Subgroup G) (g l : G) :
    A.map (MulAut.conj (g * l)).toMonoidHom =
      (A.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  change (g * l) * x * (g * l)⁻¹ = g * (l * x * l⁻¹) * g⁻¹
  group

private theorem supplement_of_orbit {G : Type*} [Group G] (M L U : Subgroup G)
    (hLM : L ≤ M)
    (htrans : ∀ g ∈ M, ∃ l ∈ L,
      U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj l).toMonoidHom) :
    M = L ⊔ (M ⊓ normalizer (U : Set G)) := by
  apply le_antisymm _ (sup_le hLM inf_le_left)
  intro g hg
  obtain ⟨l,hl,he⟩ := htrans g hg
  have hs : l⁻¹ * g ∈ M ⊓ normalizer (U : Set G) := by
    refine ⟨M.mul_mem (M.inv_mem (hLM hl)) hg, ?_⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    change U.map (MulAut.conj (l⁻¹ * g)).toMonoidHom = U
    rw [map_conj_mul, he, ← map_conj_mul, inv_mul_cancel]
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      change 1 * x * 1⁻¹ = x
      simp
    rw [hid, map_id]
  have hprod := (L ⊔ (M ⊓ normalizer (U : Set G))).mul_mem
    (mem_sup_left hl) (mem_sup_right hs)
  simpa only [mul_inv_cancel_left] using hprod

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The actual source Frattini supplement, obtained from point transitivity.
The orbit hypothesis is on conjugate subgroups, not an arbitrary family tag. -/
theorem point_stabilizer_supplement (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hti : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hM3 : E.M₁ ≤ normalizer (E.V₃ : Set G))
    (hout : ¬ E.V₁.map (MulAut.conj y).toMonoidHom ≤ E.V₃)
    (htrans : ∀ A B : Subgroup G,
      (∃ g : G, A = E.V₁.map (MulAut.conj g).toMonoidHom) →
      (∃ g : G, B = E.V₁.map (MulAut.conj g).toMonoidHom) →
      A ≤ V → B ≤ V → ¬ A ≤ E.V₃ → ¬ B ≤ E.V₃ →
      ∃ l ∈ E.L₁, B = A.map (MulAut.conj l).toMonoidHom) :
    E.M₁ = E.L₁ ⊔ oppositePointStabilizer E y := by
  have hLM : E.L₁ ≤ E.M₁ := le_inf (E.L₁_le.trans L.le_normalizer)
    ((residualIn_le _).trans inf_le_right)
  have hMV := M₁_normalizes_seed_of_TI E m hti
  have hpointV : E.V₁.map (MulAut.conj y).toMonoidHom ≤ V :=
    (map_mono (f := (MulAut.conj y).toMonoidHom) E.V₁_le).trans
      (mem_normalizer_iff_map_conj_eq.mp (D.normalizes hy)).le
  apply supplement_of_orbit _ _ _ hLM
  intro g hg
  have hVg : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (hMV hg)
  have h3g : E.V₃.map (MulAut.conj g⁻¹).toMonoidHom = E.V₃ :=
    mem_normalizer_iff_map_conj_eq.mp (hM3 (E.M₁.inv_mem hg))
  have hBout : ¬ (E.V₁.map (MulAut.conj y).toMonoidHom).map
      (MulAut.conj g).toMonoidHom ≤ E.V₃ := by
    intro hle
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rw [← map_conj_mul, inv_mul_cancel, h3g] at hh
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      change 1 * x * 1⁻¹ = x
      simp
    rw [hid, map_id] at hh
    exact hout hh
  exact htrans _ _ ⟨y,rfl⟩ ⟨g*y, (map_conj_mul _ g y).symm⟩
    hpointV ((map_mono hpointV).trans hVg.le) hout hBout

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
