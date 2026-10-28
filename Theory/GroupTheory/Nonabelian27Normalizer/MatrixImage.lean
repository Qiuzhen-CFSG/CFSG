module

public import Theory.SpecificGroups.GL2.ThreeResidualImages
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Normal Sylow three-subgroups from a ternary matrix action

A subgroup of GL₂(3) with elementary Sylow two-subgroups has exponent
dividing six: the cube of any matrix is a two-element. Its two-residual
is trivial, cubic, or SL₂(3), by the explicit ternary matrix generation
calculation. The last case has an element whose sixth power is nontrivial.
Thus the residual is a normal three-group with two-group quotient, and
is the Sylow three-subgroup.

Sylow images transfer the exponent-two condition along a surjection.
Pulling back the resulting normal Sylow subgroup through a three-group
kernel proves the form used for normalizer actions.

Source application: Bender, *Finite groups with large subgroups* (1974),
proof of (4.1), printed p.225, the normal Sylow assertion for N_G(Z).
-/

open Subgroup Matrix
namespace Nonabelian27Normalizer

private theorem sylow_square_image {G H : Type*} [Group G] [Group H] [Finite G]
    (hs : ∀ (S : Sylow 2 G) (x : S), x ^ 2 = 1)
    (f : G →* H) (hf : Function.Surjective f) :
    ∀ (S : Sylow 2 H) (x : S), x ^ 2 = 1 := by
  intro S x
  obtain ⟨T, rfl⟩ := Sylow.mapSurjective_surjective hf 2 S
  obtain ⟨y, hy, he⟩ := x.property
  apply Subtype.ext
  change x.val ^ 2 = 1
  rw [← he, ← map_pow]
  have hy2 : y ^ 2 = 1 := congrArg Subtype.val (hs T ⟨y, hy⟩)
  rw [hy2, map_one]

private theorem matrix_pow_six (K : Subgroup (GL (Fin 2) (ZMod 3)))
    (hs : ∀ (S : Sylow 2 K) (x : S), x ^ 2 = 1) (x : K) : x.val ^ 6 = 1 := by
  have hp : IsPGroup 2 (zpowers (x ^ 3)) :=
    IsPGroup.of_card_dvd_pow (n := 3) (by
      rw [Nat.card_zpowers]
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      change (x.val ^ 3) ^ 8 = 1
      simpa only [← pow_mul] using GeneralLinearGroup.three_pow_twentyFour x.val)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hh := congrArg (fun y : S => y.val.val) (hs S ⟨x ^ 3, hS (mem_zpowers _)⟩)
  change (x.val ^ 3) ^ 2 = 1 at hh
  simpa only [← pow_mul] using hh

private theorem matrix_normal_sylow (K : Subgroup (GL (Fin 2) (ZMod 3)))
    (hsix : ∀ x : K, x.val ^ 6 = 1) :
    ∃ P : Sylow 3 K, (P : Subgroup K).Normal := by
  let R := pResidual 2 K
  let I := R.map K.subtype
  let e : R ≃* I := R.equivMapOfInjective K.subtype K.subtype_injective
  have hpI : IsPPerfect 2 I :=
    (isPPerfect_pResidual (G := K) 2).of_surjective e.toMonoidHom e.surjective
  have hI : IsPGroup 3 I := by
    by_cases hi : I = ⊥
    · rw [hi]
      exact IsPGroup.of_bot
    rcases GeneralLinearGroup.three_twoPerfect_subgroup I hpI hi with hi3 | hiSL
    · exact IsPGroup.of_card (n := 1) hi3
    · obtain ⟨x, hx, hx6⟩ := GeneralLinearGroup.three_special_exists_pow_six_ne
      have hxI : x ∈ I := hiSL.symm ▸ hx
      exact (hx6 (hsix ⟨x, map_subtype_le R hxI⟩)).elim
  have hR : IsPGroup 3 R := hI.of_equiv e.symm
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := K)
  have heq : (P : Subgroup K) = R := by
    apply le_antisymm _ (hR.le_sylow_of_normal P)
    let q := QuotientGroup.mk' R
    have hq2 : IsPGroup 2 (K ⧸ R) := isPGroup_quotient_pResidual 2
    have hbot : (P : Subgroup K).map q = ⊥ := disjoint_top.mp
      (IsPGroup.disjoint_of_coprime (P.isPGroup'.map q) (hq2.to_subgroup ⊤) (by decide))
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    exact mem_bot.mp (hbot ▸ (mem_map_of_mem q hx))
  exact ⟨P, heq ▸ inferInstance⟩

/-- A homomorphism to the ternary two-dimensional matrix group with
three-group kernel gives a normal Sylow three-subgroup when the Sylow
two-subgroups of the domain have exponent dividing two. -/
public theorem exists_normal_sylow_of_matrix_hom {G : Type*} [Group G] [Finite G]
    (hs : ∀ (S : Sylow 2 G) (x : S), x ^ 2 = 1)
    (f : G →* GL (Fin 2) (ZMod 3)) (hker : IsPGroup 3 f.ker) :
    ∃ P : Sylow 3 G, (P : Subgroup G).Normal := by
  have himage := sylow_square_image hs f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P, hPN⟩ := matrix_normal_sylow f.range (matrix_pow_six f.range himage)
  have hk : IsPGroup 3 f.rangeRestrict.ker := by rwa [MonoidHom.ker_rangeRestrict]
  have hr : (P : Subgroup f.range) ≤ f.rangeRestrict.range := by
    rw [MonoidHom.range_eq_top.mpr f.rangeRestrict_surjective]
    exact le_top
  exact ⟨P.comapOfKerIsPGroup f.rangeRestrict hk hr, hPN.comap f.rangeRestrict⟩

end Nonabelian27Normalizer
