module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.CardFourAutomorphismStabilizer

/-!
# A power fiber distinguishing a coset in a quotient of order four

Let a finite two-group surject onto a group of order four, with kernel
contained in its Frattini subgroup. Suppose the elements whose nth powers
are nontrivial form exactly one nonidentity fiber. Then its automorphism
group is a two-group.

The distinguished fiber is intrinsic. Its translation stabilizer is the
kernel, so that kernel is characteristic. The quotient action fixes the
distinguished nonidentity element and therefore has order at most two.
Burnside's Frattini kernel theorem controls the remaining automorphisms.
This is a direct consequence of the two imported general results; the
application to Ree groups uses the eighth-power fiber.
-/

namespace MonoidHom

/-- A nonempty fiber defined intrinsically by a power test has characteristic kernel. -/
public theorem ker_characteristic_of_power_fiber
    {G Q : Type*} [Group G] [Group Q] (q : G →* Q)
    (hq : Function.Surjective q) (z : Q) (n : ℕ)
    (hfiber : ∀ x : G, x ^ n ≠ 1 ↔ q x = z) : q.ker.Characteristic := by
  obtain ⟨t, ht⟩ := hq z
  have hpres (f : MulAut G) (x : G) : q (f x) = z ↔ q x = z := by
    rw [← hfiber, ← hfiber, ← map_pow]
    exact not_congr f.map_eq_one_iff
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro f x hx
  change q (f x) = 1
  have hxt : q (x * t) = z := by rw [map_mul, mem_ker.mp hx, one_mul, ht]
  have hfx := (hpres f (x * t)).mpr hxt
  rw [map_mul, map_mul, (hpres f t).mpr ht] at hfx
  exact mul_right_cancel (hfx.trans (one_mul z).symm)

/-- A distinguished power fiber in a four-element quotient below the Frattini
quotient forces all automorphisms to form a two-group. -/
public theorem isPGroup_mulAut_of_four_quotient_power_fiber
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (hG : IsPGroup 2 G) (q : G →* Q) (hq : Function.Surjective q)
    (hQ : Nat.card Q = 4) (hker : q.ker ≤ frattini G)
    (z : Q) (hz : z ≠ 1) (n : ℕ)
    (hfiber : ∀ x : G, x ^ n ≠ 1 ↔ q x = z) : IsPGroup 2 (MulAut G) := by
  let : q.ker.Characteristic := q.ker_characteristic_of_power_fiber hq z n hfiber
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let ρ := Subgroup.quotientAut q.ker
  obtain ⟨t, ht⟩ := hq z
  let v := QuotientGroup.mk' q.ker t
  have hev : e v = z := ht
  have hv : v ≠ 1 := by
    intro h
    exact hz (hev.symm.trans (h ▸ map_one e))
  have hfix : ∀ f ∈ ρ.range, f v = v := by
    rintro _ ⟨f, rfl⟩
    apply e.injective
    change e (Subgroup.quotientAut q.ker f (QuotientGroup.mk' q.ker t)) = e v
    rw [Subgroup.quotientAut_apply_mk]
    change q (f t) = q t
    rw [ht, ← hfiber, ← map_pow]
    exact fun h => ((hfiber t).mpr ht) (f.map_eq_one_iff.mp h)
  have hcard : Nat.card ρ.range ≤ 2 :=
    card_mulAut_subgroup_le_two_of_fixed_point
      ((Nat.card_congr e.toEquiv).trans hQ) v hv ρ.range hfix
  have hrange : IsPGroup 2 ρ.range := by
    have hpos : 0 < Nat.card ρ.range := Nat.card_pos
    have hc : Nat.card ρ.range = 1 ∨ Nat.card ρ.range = 2 := by omega
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rcases hc with h | h <;> simp only [h, pow_one, one_dvd, dvd_refl]
  have hkernel : IsPGroup 2 ρ.ker := by
    apply (Subgroup.isPGroup_quotientAut_frattini_kernel hG).to_le
    intro f hf
    apply MulEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) x
    rw [Subgroup.quotientAut_apply_mk]
    apply QuotientGroup.eq.mpr
    apply hker
    apply QuotientGroup.eq.mp
    have hh := DFunLike.congr_fun hf (QuotientGroup.mk' q.ker x)
    change Subgroup.quotientAut q.ker f (QuotientGroup.mk' q.ker x) =
      QuotientGroup.mk' q.ker x at hh
    rw [Subgroup.quotientAut_apply_mk] at hh
    exact hh
  have hpre := hrange.comap_of_ker_isPGroup ρ hkernel
  have htop : ρ.range.comap ρ = ⊤ := by ext f; simp
  rw [htop] at hpre
  exact hpre.of_surjective (⊤ : Subgroup (MulAut G)).subtype (by
    intro f
    exact ⟨⟨f, Subgroup.mem_top f⟩, rfl⟩)

end MonoidHom
