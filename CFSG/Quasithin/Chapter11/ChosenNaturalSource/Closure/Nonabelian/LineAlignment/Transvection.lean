module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel

/-!
# Involutions on an invariant field plane

For a linear involution in characteristic two, its displacement has square zero.
On a two-dimensional plane with an invariant line, the kernel contains that line;
rank-nullity then puts the whole displacement in it. The original-group consumer
in Movement.lean uses scalar multiples of a nonzero displacement to fill the line.

Source: Aschbacher--Smith, 11.5.3(3), printed p.780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
namespace PlaneDisplacement
variable {F N : Type*} [Field F] [AddCommGroup N] [Module F N]

theorem square_zero_range_le_line [FiniteDimensional F N]
    (d : Module.End F N) (hd : ∀ v, d (d v) = 0)
    (p : Submodule F N) (hp : Module.finrank F p = 1)
    (hinv : ∀ v ∈ p, d v ∈ p) (hdim : Module.finrank F N = 2) :
    LinearMap.range d ≤ p := by
  have hpker : p ≤ LinearMap.ker d := by
    intro v hv
    change d v = 0
    by_contra hdv
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hp (hinv v hv) hdv
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hv)
    apply hdv
    rw [← ht, map_smul, hd, smul_zero]
  by_cases hd0 : d = 0
  · simp [hd0]
  · have hr : 0 < Module.finrank F (LinearMap.range d) := by
      by_contra hh
      have hz : Module.finrank F (LinearMap.range d) = 0 := by omega
      exact hd0 (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
    have hdim' := d.finrank_range_add_finrank_ker
    have hker : Module.finrank F (LinearMap.ker d) = 1 := by
      have h := Submodule.finrank_mono hpker
      omega
    have he : p = LinearMap.ker d := Submodule.eq_of_le_of_finrank_eq hpker (hp.trans hker.symm)
    rw [he]
    rintro _ ⟨v, rfl⟩
    exact hd v

theorem displacement_mem_point [FiniteDimensional F N] [Module (ZMod 2) N]
    (e : Module.End F N) (he : ∀ v, e (e v) = v)
    (P p : Submodule F N) (hP : Module.finrank F P = 2)
    (hp : Module.finrank F p = 1) (hpP : p ≤ P)
    (hinvP : ∀ v ∈ P, e v ∈ P) (hinvp : ∀ v ∈ p, e v ∈ p)
    (v : N) (hv : v ∈ P) : e v - v ∈ p := by
  let d : P →ₗ[F] P :=
    { toFun v := ⟨e v.val - v.val, P.sub_mem (hinvP _ v.property) v.property⟩
      map_add' v w := by
        apply Subtype.ext
        change e ((v : N) + (w : N)) - ((v : N) + (w : N)) =
          (e v - v) + (e w - w)
        rw [map_add, sub_add_sub_comm]
      map_smul' t v := by
        apply Subtype.ext
        change e (t • (v : N)) - t • (v : N) = t • (e v - v)
        rw [map_smul, smul_sub] }
  have hd (v : P) : d (d v) = 0 := by
    apply Subtype.ext
    change e (e v.val - v.val) - (e v.val - v.val) = 0
    rw [map_sub, he]
    calc
      v.val - e v.val - (e v.val - v.val) = (v.val + v.val) - (e v.val + e v.val) := by abel
      _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, sub_self]
  have hp' : Module.finrank F (p.comap P.subtype) = 1 :=
    (Submodule.comapSubtypeEquivOfLe hpP).finrank_eq.trans hp
  have h := square_zero_range_le_line d hd (p.comap P.subtype) hp'
    (fun v hv => p.sub_mem (hinvp _ hv) hv) hP
  exact h ⟨⟨v, hv⟩, rfl⟩

end PlaneDisplacement
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
