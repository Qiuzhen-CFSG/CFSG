module
public import Theory.ElementaryAbelian.Basic

/-!
# Uniqueness of elementary abelian lifts detected by one actor

Suppose a homomorphism has elementary abelian kernel V, and A and B are
elementary abelian subgroups with the same image. If both contain their fixed
subgroups in V, and C_V(A) = C_V(a) for some a in A, then B lies in A.

Choose b in B with the same image as a. The difference b⁻¹a lies in V.
All three elements square to one, so a and b commute. Their difference is
therefore fixed by a, hence by A and B, which puts a in B. Every member of B
then differs from a member of A by an element fixed by a, proving containment.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of B.2.21, printed pp.82–83.
-/

open scoped IsMulCommutative
namespace IsElementaryAbelian
variable {G H : Type*} [Group G] [Group H]

private theorem diff_mem (q : G →* H) (V : Subgroup G)
    (hk : q.ker = V) {a b : G} (he : q a = q b) : a⁻¹ * b ∈ V := by
  rw [← hk, MonoidHom.mem_ker]
  simp [he]

private theorem fixed_le_of_map_eq (q : G →* H) (V A B : Subgroup G)
    [IsElementaryAbelian 2 V] (hk : q.ker = V) (he : A.map q = B.map q) :
    V ⊓ Subgroup.centralizer (A : Set G) ≤
      V ⊓ Subgroup.centralizer (B : Set G) := by
  rintro x ⟨hxV, hxA⟩
  refine ⟨hxV, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro b hb
  have hqb : q b ∈ A.map q := he ▸ Subgroup.mem_map_of_mem q hb
  obtain ⟨a, ha, hab⟩ := hqb
  have hd := diff_mem q V hk hab
  have hax : Commute a x := Subgroup.mem_centralizer_iff.mp hxA a ha
  have hdx : Commute (a⁻¹ * b) x := setLike_mul_comm hd hxV
  simpa using (hax.mul_left hdx).eq

/-- Elementary abelian lifts with the same image are nested if their fixed
subgroups are contained in them and one actor detects the full fixed subgroup. -/
public theorem le_of_same_image_of_centralizer_singleton
    (q : G →* H) (V A B : Subgroup G) [IsElementaryAbelian 2 V]
    (hk : q.ker = V)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hfa : V ⊓ Subgroup.centralizer (A : Set G) ≤ A)
    (hfb : V ⊓ Subgroup.centralizer (B : Set G) ≤ B)
    (he : A.map q = B.map q) (a : G) (ha : a ∈ A)
    (hfix : V ⊓ Subgroup.centralizer (A : Set G) =
      V ⊓ Subgroup.centralizer ({a} : Set G)) : B ≤ A := by
  have hfAB := fixed_le_of_map_eq q V A B hk he
  have hqa : q a ∈ B.map q := he ▸ Subgroup.mem_map_of_mem q ha
  obtain ⟨b, hb, hba⟩ := hqa
  have hv : b⁻¹ * a ∈ V := diff_mem q V hk hba
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hb2 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b hb
  have hv2 : (b⁻¹ * a) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hv
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ha2)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hb2)
  have hvi : (b⁻¹ * a)⁻¹ = b⁻¹ * a :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hv2)
  have hab : Commute a b := by
    change a * b = b * a
    simpa [mul_inv_rev, hai, hbi] using hvi
  have hvfix : b⁻¹ * a ∈ V ⊓ Subgroup.centralizer (A : Set G) := by
    rw [hfix]
    refine ⟨hv, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    exact (hab.inv_right.mul_right (Commute.refl a)).eq
  have haB : a ∈ B := by
    have := B.mul_mem hb (hfb (hfAB hvfix))
    simpa using this
  intro x hxB
  have hqx : q x ∈ A.map q := he ▸ Subgroup.mem_map_of_mem q hxB
  obtain ⟨y, hy, hyx⟩ := hqx
  have hvx : y⁻¹ * x ∈ V := diff_mem q V hk hyx
  have hc : Commute a (y⁻¹ * x) :=
    (show Commute a y from setLike_mul_comm ha hy).inv_right.mul_right
      (show Commute a x from setLike_mul_comm haB hxB)
  have hvxfix : y⁻¹ * x ∈ V ⊓ Subgroup.centralizer (A : Set G) := by
    rw [hfix]
    exact ⟨hvx, Subgroup.mem_centralizer_iff.mpr (by
      intro z hz
      have hza : z = a := Set.mem_singleton_iff.mp hz
      subst z
      exact hc.eq)⟩
  have := A.mul_mem hy (hfa hvxfix)
  simpa using this

end IsElementaryAbelian
