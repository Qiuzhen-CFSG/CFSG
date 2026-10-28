module

public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.NormNum

/-!
# Determinant reduction for ternary automizers with fused involutions

Let a finite group have elementary Sylow two-subgroups, order divisible by
four, and one conjugacy class of involutions. Every homomorphism to a
commutative group of order two is trivial: its restriction to a Sylow subgroup
has a nonidentity kernel element, fusion puts every involution in the kernel,
and the Sylow index excludes a remaining image of order two.

The elementary-group/vector-space correspondence embeds an automizer of an
elementary group of order 27 in GL₃(3). Applying the preceding result to its
determinant places that embedding in the actual matrix group SL₃(3).
This proves the linear reduction only; it does not classify its image.

Source application: Bender, *Finite groups with large subgroups* (1974),
(4.1), printed p.225, citing Janko (1966), Lemma 3.1.
-/

namespace TernaryFusedFour

/-- Fusion and an elementary Sylow subgroup of order at least four kill
any homomorphism to a commutative group of order two. -/
public theorem hom_eq_one_of_fused_involutions
    {G C : Type*} [Group G] [Finite G] [CommGroup C] [Finite C]
    (hC : Nat.card C = 2) (hfour : 4 ∣ Nat.card G)
    (hel : ∀ P : Sylow 2 G, IsElementaryAbelian 2 P)
    (hfuse : ∀ t u : G, orderOf t = 2 → orderOf u = 2 → IsConj t u)
    (f : G →* C) : ∀ g, f g = 1 := by
  classical
  let P : Sylow 2 G := Sylow.nonempty.some
  let := hel P
  have hPfour : 4 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 2) hfour
  have hPle : 4 ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos hPfour
  let fP : P →* C := f.comp (P : Subgroup G).subtype
  have hninj : ¬ Function.Injective fP := by
    intro hi
    have hle := Nat.card_le_card_of_injective fP hi
    rw [hC] at hle
    omega
  obtain ⟨t, htker, htne⟩ : ∃ t : P, fP t = 1 ∧ t ≠ 1 := by
    by_contra h
    apply hninj
    rw [injective_iff_map_eq_one]
    intro t ht
    by_contra htne
    exact h ⟨t, ht, htne⟩
  have htord : orderOf (t : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (t : G) t.property)
      (fun ht => htne (Subtype.ext ht))
  have hPker : (P : Subgroup G) ≤ f.ker := by
    intro x hx
    by_cases hxone : x = 1
    · simp [hxone]
    · have hxord : orderOf x = 2 :=
        orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hxone
      have hfx : f x = f t := isConj_iff_eq.mp (f.map_isConj (hfuse x t hxord htord))
      exact hfx.trans htker
  have hodd : ¬ 2 ∣ Nat.card f.range := by
    rw [← Subgroup.index_ker]
    exact fun h => P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hPker))
  have hdvd : Nat.card f.range ∣ 2 := hC ▸ f.range.card_subgroup_dvd_card
  have hcard : Nat.card f.range = 1 :=
    ((Nat.prime_two).eq_one_or_self_of_dvd _ hdvd).resolve_right (fun h => hodd (h ▸ dvd_rfl))
  have hbot : f.range = ⊥ := Subgroup.card_eq_one.mp hcard
  intro g
  have hg : f g ∈ f.range := ⟨g, rfl⟩
  simpa only [hbot, Subgroup.mem_bot] using hg

/-- An automizer satisfying the local conditions acts faithfully by
actual determinant-one ternary matrices. -/
public theorem exists_injective_specialLinear
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 27) (K : Subgroup (MulAut E))
    (hfour : 4 ∣ Nat.card K)
    (hel : ∀ P : Sylow 2 K, IsElementaryAbelian 2 P)
    (hfuse : ∀ t u : K, orderOf t = 2 → orderOf u = 2 → IsConj t u) :
    ∃ f : K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3), Function.Injective f := by
  obtain ⟨ρ, hρ⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 3) E (by rw [hcard]; decide)
  let r := ρ.comp K.subtype
  have hd : ∀ g : K, Matrix.GeneralLinearGroup.det (r g) = 1 :=
    hom_eq_one_of_fused_involutions (by rw [Nat.card_units, Nat.card_zmod])
      hfour hel hfuse (Matrix.GeneralLinearGroup.det.comp r)
  let f : K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) := {
    toFun := fun g => ⟨(r g).val, congrArg Units.val (hd g)⟩
    map_one' := by apply Subtype.ext; exact congrArg Units.val r.map_one
    map_mul' := by intro g h; apply Subtype.ext; exact congrArg Units.val (r.map_mul g h) }
  refine ⟨f, ?_⟩
  intro g h heq
  apply Subtype.ext
  apply hρ
  apply Units.ext
  exact congrArg Subtype.val heq

/-- Elementary Sylow two-subgroups exclude every element of order four. -/
public theorem no_order_four_of_elementary_sylow
    {G : Type*} [Group G] [Finite G]
    (hel : ∀ P : Sylow 2 G, IsElementaryAbelian 2 P) (x : G) : orderOf x ≠ 4 := by
  intro hx
  have hp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; decide)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  let := hel P
  have hx2 : x ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian x (hP (Subgroup.mem_zpowers x))
  have hd := orderOf_dvd_of_pow_eq_one hx2
  norm_num [hx] at hd

end TernaryFusedFour
