module

public import Theory.GroupTheory.Nonabelian27Normalizer.MatrixImage
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.Frattini.PGroup

/-!
# The normalizer of a nonabelian subgroup of order 27

Nonabelianness makes the Frattini subgroup nontrivial, so the elementary
Frattini quotient has at most nine elements. Its automorphism group embeds
in GL₂(3). The literal normalizer conjugation action, followed by the
canonical Frattini quotient action, has three-group kernel: its conjugation
kernel is the relative ambient centralizer, and Burnside's basis theorem
controls the remaining kernel.

The ambient Sylow-two exponent condition passes to the normalizer. The
ternary matrix image calculation then supplies a normal Sylow three-subgroup
and lifts it through the action kernel. No exponent assumption on the
order-27 subgroup is needed.

Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.1),
printed p.225. This is the reusable group-theoretic normalizer step.
-/

open Matrix
namespace Subgroup

private theorem frattini_card_bound {G : Type*} [Group G] [Finite G] (hc : Nat.card G = 27)
    (hn : ¬ IsMulCommutative G) : Nat.card (G ⧸ frattini G) ≤ 9 := by
  have hp : IsPGroup 3 G := IsPGroup.of_card (n := 3) (by simpa using hc)
  let _ : Fact (IsPGroup 3 G) := ⟨hp⟩
  have hphi : frattini G ≠ ⊥ := by
    intro he
    have hh := (frattini_eq_bot_iff_isElementaryAbelian (p := 3)).mp he
    exact hn hh.toIsMulCommutative
  have hgt : 1 < Nat.card (frattini G) := (frattini G).one_lt_card_iff_ne_bot.mpr hphi
  obtain ⟨k, hk⟩ := (hp.to_subgroup (frattini G)).exists_card_eq
  have hge : 3 ≤ Nat.card (frattini G) := by
    rw [hk] at hgt ⊢
    cases k with
    | zero => simp at hgt
    | succ k =>
      have : 0 < (3 : ℕ) ^ k := pow_pos (by decide) _
      rw [pow_succ]
      omega
  have hm := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini G)
  rw [hc] at hm
  nlinarith

/-- A nonabelian subgroup of order 27 with three-group centralizer has
normal Sylow three-subgroups in its literal ambient normalizer, provided
the ambient Sylow two-subgroups have exponent dividing two. -/
public theorem exists_normal_sylow_three_normalizer_of_nonabelian_card_27 {G : Type*} [Group G] [Finite G]
    (hs : ∀ (S : Sylow 2 G) (x : S), x ^ 2 = 1)
    (D : Subgroup G) (hc : Nat.card D = 27) (hn : ¬ IsMulCommutative D)
    (hC : IsPGroup 3 (centralizer (D : Set G))) :
    ∃ P : Sylow 3 (normalizer (D : Set G)),
      (P : Subgroup (normalizer (D : Set G))).Normal := by
  let N := normalizer (D : Set G)
  have hp : IsPGroup 3 D := IsPGroup.of_card (n := 3) (by simpa using hc)
  let _ : Fact (IsPGroup 3 D) := ⟨hp⟩
  let V := D ⧸ frattini D
  let _ : IsElementaryAbelian 3 V := isElementaryAbelian_quotient_frattini (p := 3)
  obtain ⟨i, hi⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 2) V (frattini_card_bound hc hn)
  let a : N →* MulAut V := (quotientAut (frattini D)).comp D.normalizerMonoidHom
  have hconj : IsPGroup 3 D.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact hC.comap_subtype
  have ha : IsPGroup 3 a.ker :=
    (isPGroup_quotientAut_frattini_kernel hp).comap_of_ker_isPGroup
      D.normalizerMonoidHom hconj
  have hf : IsPGroup 3 (i.comp a).ker := by
    rwa [MonoidHom.ker_comp_of_injective a i hi]
  apply Nonabelian27Normalizer.exists_normal_sylow_of_matrix_hom (G := N) _ (i.comp a) hf
  intro S x
  obtain ⟨T, hT⟩ := (S.isPGroup'.map N.subtype).exists_le_sylow
  have hxT : x.val.val ∈ (T : Subgroup G) := hT (mem_map_of_mem N.subtype x.property)
  have hh := congrArg Subtype.val (hs T ⟨x.val.val, hxT⟩)
  apply Subtype.ext
  apply Subtype.ext
  exact hh

end Subgroup
