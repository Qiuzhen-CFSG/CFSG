module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Prime subgroups through coprime kernels

A homomorphism with kernel of order coprime to p is injective on every
p-subgroup. If it is surjective, elementary abelian p-subgroups of the
codomain lift isomorphically: take a Sylow subgroup of their inverse image.
For a normal p-subgroup, injectivity also makes centralizers lift exactly.

These elementary quotient facts supply the odd-core reduction in the
binary case of GLS, Number 2, Proposition 22.4. They require neither
solvability nor any classification hypotheses.
-/

namespace Subgroup

/-- A homomorphism with coprime kernel is injective on a prime subgroup. -/
public theorem injective_comp_subtype_of_coprime_ker
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H)
    (hker : Nat.Coprime p (Nat.card f.ker))
    (P : Subgroup G) (hP : IsPGroup p P) :
    Function.Injective (f.comp P.subtype) := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hd : Disjoint P f.ker := disjoint_of_coprime_natCard (by
    rw [hn]
    exact hker.pow_left n)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  exact Subtype.ext (hd.le_bot ⟨x.property, hx⟩)

/-- Elementary abelian prime subgroups lift with the same order through a
surjective homomorphism with coprime kernel. -/
public theorem exists_elementaryAbelian_map_eq_of_surjective_coprime
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker))
    (D : Subgroup H) [IsElementaryAbelian p D] :
    ∃ A : Subgroup G, IsElementaryAbelian p A ∧
      A.map f = D ∧ Nat.card A = Nat.card D := by
  let K := D.comap f
  let q : K →* D := f.subgroupComap D
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective D hf
  let S : Sylow p K := Sylow.nonempty.some
  have hStop : (S.mapSurjective hq : Subgroup D) = ⊤ := by
    apply top_unique
    exact ((IsElementaryAbelian.isPGroup p D).to_subgroup ⊤).le_sylow_of_normal _
  let A := (S : Subgroup K).map K.subtype
  have hA : IsPGroup p A := S.isPGroup'.map K.subtype
  have hmap : A.map f = D := by
    have hh := congrArg (Subgroup.map D.subtype) hStop
    change ((S : Subgroup K).map q).map D.subtype = (⊤ : Subgroup D).map D.subtype at hh
    rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
    change (S : Subgroup K).map (f.comp K.subtype) = D at hh
    simpa only [A, map_map] using hh
  let e : A ≃* D := (MulEquiv.ofBijective (f.subgroupMap A) ⟨by
    intro x y h
    exact injective_comp_subtype_of_coprime_ker f hker A hA
      (congrArg Subtype.val h), f.subgroupMap_surjective A⟩).trans
        (MulEquiv.subgroupCongr hmap)
  have he : IsElementaryAbelian p A := {
    toIsMulCommutative := ⟨⟨fun x y => e.injective (by
      simp only [map_mul]
      exact mul_comm' _ _)⟩⟩
    exponent_dvd_p := by
      rw [Monoid.exponent_eq_of_mulEquiv e]
      exact IsElementaryAbelian.exponent_dvd_p p D }
  exact ⟨A, he, hmap, Nat.card_congr e.toEquiv⟩

/-- The centralizer of a normal prime subgroup lifts through a coprime kernel. -/
public theorem map_centralizer_eq_of_surjective_coprime
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker))
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup p Q) :
    (centralizer (Q : Set G)).map f = centralizer (Q.map f : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ f)
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  refine mem_map.mpr ⟨x, ?_, rfl⟩
  intro q hq
  have hconj : x * q * x⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem q hq x
  have heq : (⟨x * q * x⁻¹, hconj⟩ : Q) = ⟨q, hq⟩ := by
    apply injective_comp_subtype_of_coprime_ker f hker Q hQ
    change f (x * q * x⁻¹) = f q
    rw [map_mul, map_mul, map_inv, ← hy (f q) (mem_map_of_mem f hq)]
    simp only [mul_inv_cancel_right]
  have hh := congrArg Subtype.val heq
  exact ((mul_inv_eq_iff_eq_mul).mp hh).symm

/-- If the image of a prime subgroup is normal modulo a coprime kernel,
a conjugate lying in the same prime overgroup equals the original subgroup.
Normality is required only in the codomain. -/
public theorem map_conj_eq_of_normal_map_of_le_prime_group {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H)
    (hker : Nat.Coprime p (Nat.card f.ker))
    (P A : Subgroup G) (hP : IsPGroup p P) (hAP : A ≤ P)
    [(A.map f).Normal] (g : G)
    (hg : A.map (MulAut.conj g).toMonoidHom ≤ P) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj g).injective])
  rintro x ⟨a, ha, rfl⟩
  have hmap : f (g * a * g⁻¹) ∈ A.map f := by
    simpa only [map_mul, map_inv] using
      (inferInstance : (A.map f).Normal).conj_mem (f a) (mem_map_of_mem f ha) (f g)
  obtain ⟨b, hb, he⟩ := hmap
  have hc : g * a * g⁻¹ ∈ P := hg (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
  have heq : (⟨b, hAP hb⟩ : P) = ⟨g * a * g⁻¹, hc⟩ :=
    injective_comp_subtype_of_coprime_ker f hker P hP he
  have hba : b = g * a * g⁻¹ := congrArg Subtype.val heq
  change g * a * g⁻¹ ∈ A
  exact hba ▸ hb

end Subgroup
