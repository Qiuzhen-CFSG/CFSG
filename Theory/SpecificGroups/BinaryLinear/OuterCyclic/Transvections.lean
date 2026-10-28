module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections

/-!
# Automorphisms preserve binary transvections

A nonidentity transvection has the form x ↦ x + f(x)w with w and f nonzero
and f(w)=0. Any two such elements are conjugate: first align w, then use
a transvection to align the two nonzero linear forms. Over the binary field
two nonzero linear forms have a common vector on which they both equal one.

A point radical lies in a Sylow two-subgroup, whose center is nontrivial.
The existing central-Sylow calculation identifies a nonidentity central
element as a transvection. Conjugacy therefore realizes every transvection
as a central element of some Sylow subgroup. Automorphisms preserve that
intrinsic property, so they preserve transvections.

This supplies a characteristic set for reconstructing the point/hyperplane
geometry in the binary specialization of GLS3, Theorem 2.5.12 and §2.7
(`refs/KGroup/GLS3/chapter2.tex`). It does not yet classify the automorphisms.
The Sylow calculation is the one used in Aschbacher–Smith 2.3.9(7),
printed pp.525–526 of `refs/quasithin.pdf`.
-/

@[expose] public section

namespace BinaryLinear.OuterCyclic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Nonidentity rank-one transvections on the actual binary vector space. -/
def IsTransvection (t : BinaryLinear.GL V) : Prop :=
  ∃ w : V, ∃ f : V →ₗ[ZMod 2] ZMod 2,
    w ≠ 0 ∧ f ≠ 0 ∧ ∃ hfw : f w = 0, t = transvection w f hfw

private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

theorem transvection_ne_one {w : V} {f : V →ₗ[ZMod 2] ZMod 2}
    (hw : w ≠ 0) (hf : f ≠ 0) (hfw : f w = 0) : transvection w f hfw ≠ 1 := by
  intro h
  have he (v : V) := congrArg (fun g : BinaryLinear.GL V => g v) h
  have hfz : f = 0 := by
    ext v
    have hv : f v • w = 0 := add_eq_left.mp (he v)
    exact (smul_eq_zero.mp hv).resolve_right hw
  exact hf hfz

theorem IsTransvection.ne_one {t : BinaryLinear.GL V} (ht : IsTransvection t) : t ≠ 1 := by
  obtain ⟨w, f, hw, hf, hfw, rfl⟩ := ht
  exact transvection_ne_one hw hf hfw

private theorem exists_linearEquiv_apply_eq [FiniteDimensional (ZMod 2) V]
    {w u : V} (hw : w ≠ 0) (hu : u ≠ 0) :
    ∃ e : BinaryLinear.GL V, e w = u := by
  let d := (LinearEquiv.coord (ZMod 2) V w hw).trans
    (LinearEquiv.coord (ZMod 2) V u hu).symm
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq d
  refine ⟨e, ?_⟩
  have h := he ⟨w, Submodule.mem_span_singleton_self w⟩
  have hd : d ⟨w, Submodule.mem_span_singleton_self w⟩ =
      ⟨u, Submodule.mem_span_singleton_self u⟩ := by
    apply (LinearEquiv.coord (ZMod 2) V u hu).injective
    simp [d, LinearEquiv.coord_self]
  rw [hd] at h
  exact h.symm

private theorem exists_common_value_one {f k : V →ₗ[ZMod 2] ZMod 2}
    (hf : f ≠ 0) (hk : k ≠ 0) : ∃ v : V, f v = 1 ∧ k v = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    ext x
    simpa using (not_exists.mp h x)
  obtain ⟨y, hy⟩ : ∃ y, k y ≠ 0 := by
    by_contra h
    apply hk
    ext y
    simpa using (not_exists.mp h y)
  by_cases hkx : k x = 0
  · by_cases hfy : f y = 0
    · exact ⟨x + y, by simp [scalar_one hx, hfy], by simp [hkx, scalar_one hy]⟩
    · exact ⟨y, scalar_one hfy, scalar_one hy⟩
  · exact ⟨x, scalar_one hx, scalar_one hkx⟩

/-- All nonidentity transvections on a finite-dimensional binary space are conjugate. -/
theorem transvections_conjugate [FiniteDimensional (ZMod 2) V]
    {s t : BinaryLinear.GL V} (hs : IsTransvection s) (ht : IsTransvection t) :
    ∃ e : BinaryLinear.GL V, MulAut.conj e s = t := by
  obtain ⟨w, f, hw, hf, hfw, rfl⟩ := hs
  obtain ⟨u, k, hu, hk, hku, rfl⟩ := ht
  obtain ⟨e, he⟩ := exists_linearEquiv_apply_eq hw hu
  let l := k.comp e.toLinearMap
  have hl : l ≠ 0 := by
    intro hl0
    apply hk
    ext v
    have h := congrArg (fun a : V →ₗ[ZMod 2] ZMod 2 => a (e.symm v)) hl0
    simpa [l] using h
  obtain ⟨v, hfv, hlv⟩ := exists_common_value_one hf hl
  have hflv : (f + l) v = 0 := by
    simp only [LinearMap.add_apply, hfv, hlv]
    decide
  let c := transvection v (f + l) hflv
  have hcw : c w = w := by
    change w + (f + l) w • v = w
    simp [l, hfw, he, hku]
  have hlc (x : V) : l (c x) = f x := by
    change l (x + (f + l) x • v) = f x
    simp only [map_add, map_smul, LinearMap.add_apply, hlv, smul_eq_mul, mul_one]
    have hself : l x + l x = 0 :=
      (by decide : ∀ a : ZMod 2, a + a = 0) (l x)
    calc
      l x + (f x + l x) = f x + (l x + l x) := by abel
      _ = f x := by rw [hself, add_zero]
  refine ⟨e * c, ?_⟩
  apply mul_inv_eq_iff_eq_mul.mpr
  apply LinearEquiv.ext
  intro x
  change e (c (x + f x • w)) = e (c x) + k (e (c x)) • u
  simp only [map_add, map_smul, hcw, he]
  rw [show k (e (c x)) = f x from hlc x]

theorem isTransvection_of_central_sylow [Finite V]
    (hV : 2 ∣ Nat.card V) (hdim : 1 < Module.finrank (ZMod 2) V)
    (P : Sylow 2 (BinaryLinear.GL V)) {t : BinaryLinear.GL V} (ht : t ≠ 1)
    (hc : ∀ x : BinaryLinear.GL V, x ∈ P → x * t = t * x) :
    IsTransvection t := by
  obtain ⟨w, f, hw, hf, hfw, he⟩ := central_sylow_eq_transvection hV hdim P ht hc
  exact ⟨w, f, hw, hf, hfw, LinearEquiv.ext he⟩

/-- Every automorphism preserves transvections, via their central-Sylow realization. -/
theorem isTransvection_map [Finite V] [FiniteDimensional (ZMod 2) V]
    (hV : 2 ∣ Nat.card V) (hdim : 1 < Module.finrank (ZMod 2) V)
    (a : MulAut (BinaryLinear.GL V)) {t : BinaryLinear.GL V} (ht : IsTransvection t) :
    IsTransvection (a t) := by
  let : Finite (BinaryLinear.GL V) :=
    Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  obtain ⟨w, f, hw, hf, hfw, rfl⟩ := ht
  have ht1 := transvection_ne_one hw hf hfw
  let W := Submodule.span (ZMod 2) {w}
  have htW : transvection w f hfw ∈ radical W :=
    transvection_mem (Submodule.mem_span_singleton_self w)
      (Submodule.span_le.mpr (by simpa using hfw))
  obtain ⟨P, hP⟩ := (radical_two W).exists_le_sylow
  let : Nontrivial P := (Subgroup.nontrivial_iff_exists_ne_one (P : Subgroup _)).mpr
    ⟨transvection w f hfw, hP htW, ht1⟩
  let : Nontrivial (Subgroup.center P) := P.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  have hz1 : (z.val.val : BinaryLinear.GL V) ≠ 1 := by
    intro he
    exact hz (Subtype.ext (Subtype.ext he))
  have hzc : ∀ x : BinaryLinear.GL V, x ∈ P → x * z.val.val = z.val.val * x := by
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property (⟨x, hx⟩ : P))
  have hzt := isTransvection_of_central_sylow hV hdim P hz1 hzc
  obtain ⟨g, hg⟩ := transvections_conjugate hzt ⟨w, f, hw, hf, hfw, rfl⟩
  let b : MulAut (BinaryLinear.GL V) := a * MulAut.conj g
  have hbz : b z.val.val = a (transvection w f hfw) := congrArg a hg
  rw [← hbz]
  apply isTransvection_of_central_sylow hV hdim
    (P.mapSurjective (f := b.toMonoidHom) b.surjective)
  · exact fun h => hz1 (b.injective (h.trans b.map_one.symm))
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (map_mul b y z.val.val).symm.trans
      ((congrArg b (hzc y hy)).trans (map_mul b z.val.val y))

theorem isTransvection_map_iff [Finite V] [FiniteDimensional (ZMod 2) V]
    (hV : 2 ∣ Nat.card V) (hdim : 1 < Module.finrank (ZMod 2) V)
    (a : MulAut (BinaryLinear.GL V)) (t : BinaryLinear.GL V) :
    IsTransvection (a t) ↔ IsTransvection t := by
  constructor
  · intro h
    simpa using isTransvection_map hV hdim a.symm h
  · exact isTransvection_map hV hdim a

/-- The characteristic-transvection theorem for the coordinate linear groups. -/
theorem isTransvection_map_linear {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (LinearGroup n)) (t : LinearGroup n) :
    IsTransvection (a t) ↔ IsTransvection t := by
  apply isTransvection_map_iff
  · change 2 ∣ Nat.card (Fin n → ZMod 2)
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, ZMod.card]
    exact dvd_pow_self 2 (by omega)
  · simpa [Space] using (show 1 < n by omega)

end BinaryLinear.OuterCyclic
