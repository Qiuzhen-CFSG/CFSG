module
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.Gaschutz

/-!
# Splitting extensions with a regular permutation kernel

Choose a section s of the quotient map. At a coordinate x, evaluate the
kernel element s(x)⁻¹ g s(q(g)⁻¹x) at the identity coordinate. The middle
section factors cancel on multiplication, giving a crossed retraction.
Its kernel is an actual complement. No cohomology classification is used.
Gaschütz then gives splitting from a regular restriction over a subgroup
whose inverse image has index coprime to the kernel order.

Source application: the natural binary A₅ extension in Aschbacher–Smith
2.4.29, where the regular restriction is its Sylow four-group.
-/

public section
namespace Subgroup
variable {G Q A : Type*} [Group G] [Group Q] [CommGroup A]

/-- A kernel with regular permutation coordinates has a complement. -/
theorem exists_complement_of_regular_kernel (q : G →* Q) (hq : Function.Surjective q)
    (e : q.ker ≃* (Q → A))
    (he : ∀ (g : G) (v : q.ker) (x : Q),
      e (MulAut.conjNormal g v) x = e v ((q g)⁻¹ * x)) :
    ∃ K : Subgroup G, q.ker.IsComplement' K := by
  classical
  let s : Q → G := Function.surjInv hq
  have hs (x : Q) : q (s x) = x := Function.surjInv_eq hq x
  let v (g : G) (x : Q) : q.ker := ⟨(s x)⁻¹ * g * s ((q g)⁻¹ * x), by
    change q ((s x)⁻¹ * g * s ((q g)⁻¹ * x)) = 1
    rw [map_mul, map_mul, map_inv, hs, hs]
    group⟩
  have hv (g h : G) (x : Q) :
      v (g * h) x = v g x * v h ((q g)⁻¹ * x) := by
    apply Subtype.ext
    dsimp [v]
    rw [map_mul, mul_inv_rev]
    group
  let f : G → q.ker := fun g => e.symm (fun x => e (v g x) 1)
  have hf (g h : G) : f (g * h) = f g * MulAut.conjNormal g (f h) := by
    apply e.injective
    ext x
    simp only [f, e.apply_symm_apply, map_mul, Pi.mul_apply, he]
    rw [hv, map_mul]
    rfl
  have hfV (a : q.ker) : f a = a := by
    apply e.injective
    ext x
    simp only [f, e.apply_symm_apply]
    have hval : v a x = MulAut.conjNormal (s x)⁻¹ a := by
      apply Subtype.ext
      dsimp [v]
      rw [show q a = 1 from a.property]
      simp only [inv_one, one_mul, inv_inv]
    rw [hval, he, map_inv, hs, inv_inv, mul_one]
  have hf1 : f 1 = 1 := by simpa using hfV 1
  let K : Subgroup G :=
    { carrier := {x | f x = 1}
      one_mem' := hf1
      mul_mem' := by
        intro x y hx hy
        change f (x * y) = 1
        rw [hf, hx, hy, map_one, one_mul]
      inv_mem' := by
        intro x hx
        change f x⁻¹ = 1
        have hh := hf x⁻¹ x
        rw [inv_mul_cancel, hf1, hx, map_one, mul_one] at hh
        exact hh.symm }
  refine ⟨K, isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_⟩
  · apply disjoint_def.mpr
    intro x hx hxK
    have hh : f x = 1 := hxK
    have hval := hfV ⟨x, hx⟩
    have hz : (⟨x, hx⟩ : q.ker) = 1 := hval.symm.trans hh
    exact congrArg Subtype.val hz
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    refine ⟨f x, (f x).property, (f x : G)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
    change f ((f x : G)⁻¹ * x) = 1
    have hh := hf (f x) ((f x : G)⁻¹ * x)
    rw [mul_inv_cancel_left, hfV] at hh
    have hz : MulAut.conjNormal (f x : G) (f ((f x : G)⁻¹ * x)) = 1 :=
      mul_eq_left.mp hh.symm
    exact (MulAut.conjNormal (f x : G)).injective (hz.trans (map_one _).symm)

/-- A regular restriction over a coprime-index quotient subgroup splits the original extension. -/
theorem exists_complement_of_regular_preimage [Finite G]
    (q : G →* Q) (hq : Function.Surjective q) (T : Subgroup Q)
    (e : q.ker ≃* (T → A))
    (he : ∀ (g : T.comap q) (v : q.ker) (x : T),
      e (MulAut.conjNormal (g : G) v) x =
        e v ((⟨q g, g.property⟩ : T)⁻¹ * x))
    (hcoprime : (Nat.card q.ker).Coprime (T.comap q).index) :
    ∃ K : Subgroup G, q.ker.IsComplement' K := by
  let H := T.comap q
  let r : H →* T :=
    { toFun := fun g => ⟨q g, g.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun g h => Subtype.ext (map_mul q (g : G) (h : G)) }
  have hr : Function.Surjective r := by
    intro t
    obtain ⟨g, hg⟩ := hq t
    exact ⟨⟨g, show q g ∈ T from hg.symm ▸ t.property⟩, Subtype.ext hg⟩
  have hker : r.ker = q.ker.subgroupOf H := by
    ext g
    change (⟨q g, g.property⟩ : T) = 1 ↔ q g = 1
    exact Subtype.ext_iff
  have hle : q.ker ≤ H := by
    intro g hg
    change q g ∈ T
    rw [show q g = 1 from hg]
    exact T.one_mem
  let ek : r.ker ≃* q.ker := (MulEquiv.subgroupCongr hker).trans (subgroupOfEquivOfLe hle)
  have hract (g : H) (a : r.ker) :
      ek (MulAut.conjNormal g a) = MulAut.conjNormal (g : G) (ek a) := by
    apply Subtype.ext
    rfl
  obtain ⟨K, hK⟩ := exists_complement_of_regular_kernel r hr (ek.trans e) (by
    intro g a x
    change e (ek (MulAut.conjNormal g a)) x = e (ek a) ((r g)⁻¹ * x)
    rw [hract]
    exact he g (ek a) x)
  have : IsMulCommutative q.ker := ⟨⟨fun x y => e.injective (by simp [mul_comm])⟩⟩
  apply exists_complement_of_coprime_overgroup q.ker H hle hcoprime
  exact ⟨K, hker ▸ hK⟩

end Subgroup
