module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.PGroupCore

/-!
# Obstructions to intrinsic radicality

For a centric subgroup `U`, a normalizer element inducing an inner automorphism
already belongs to `U`: after an inner correction it centralizes `U`.
Consequently, if `Aut_G(U) ∩ O_p(Aut(U)) ≤ Inn(U)`, every normalizer element
acting trivially on `U / Φ(U)` belongs to `U`. This uses the proved Burnside
Frattini automorphism kernel theorem.

More generally, the same conclusion holds for a normalizer element acting
trivially on both `C / Φ(C)` and `(U / C) / Φ(U / C)`, where `C` is
characteristic in `U`. The paired action on `C` and `U / C` has p-group kernel,
and the two Frattini action kernels are p-groups. Their preimage is a normal
p-subgroup of `Aut(U)`.

Also, a centric intrinsic radical subgroup of a finite p-group whose full
automorphism group is a p-group must be the whole group. Its normalizer equals
itself, so the p-group normalizer condition applies. These give necessary
conditions for finite centric candidate calculations without assuming an
automorphism census.

Source: the normal-p-subgroup obstruction underlying Alperin fusion, also used
in `CentricRadicalCharacterFusion`; Burnside's basis kernel theorem is proved
in `PGroup.FrattiniAutomorphismKernel`.
-/

namespace Subgroup

/-- An inner action on a centric subgroup can only come from that subgroup. -/
public theorem mem_of_normalizerMonoidHom_mem_inner
    {G : Type*} [Group G] (U : Subgroup G)
    (hcent : centralizer (U : Set G) ≤ U)
    (g : normalizer (U : Set G))
    (hg : U.normalizerMonoidHom g ∈ (MulAut.conj : U →* MulAut U).range) :
    (g : G) ∈ U := by
  obtain ⟨u, hu⟩ := hg
  let uN : normalizer (U : Set G) := ⟨u, U.le_normalizer u.property⟩
  have huN : U.normalizerMonoidHom uN = MulAut.conj u := by
    ext x
    rfl
  have hk : uN⁻¹ * g ∈ U.normalizerMonoidHom.ker := by
    change U.normalizerMonoidHom (uN⁻¹ * g) = 1
    rw [map_mul, map_inv, huN, ← hu, inv_mul_cancel]
  rw [U.normalizerMonoidHom_ker] at hk
  have hz : (u : G)⁻¹ * (g : G) ∈ U := hcent hk
  simpa using U.mul_mem u.property hz

/-- An intrinsic radical centric p-subgroup contains every normalizer element
acting trivially on its Frattini quotient. -/
public theorem mem_of_intrinsic_radical_of_frattini_action_eq_one
    {G : Type*} [Group G] [Finite G] {p : ℕ} (U : Subgroup G)
    (hU : IsPGroup p U)
    (hcent : centralizer (U : Set G) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (g : normalizer (U : Set G))
    (hg : quotientAut (frattini U) (U.normalizerMonoidHom g) = 1) :
    (g : G) ∈ U := by
  apply mem_of_normalizerMonoidHom_mem_inner U hcent g
  apply hrad
  refine ⟨⟨g, rfl⟩, ?_⟩
  have hle : (quotientAut (frattini U)).ker ≤ pCore p (MulAut U) :=
    le_sSup ⟨inferInstance, isPGroup_quotientAut_frattini_kernel hU⟩
  exact hle hg

/-- A centric intrinsic radical subgroup with p-group automorphism group is
the entire ambient finite p-group. -/
public theorem eq_top_of_intrinsic_radical_of_isPGroup_mulAut
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (U : Subgroup G)
    (hcent : centralizer (U : Set G) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (ha : IsPGroup p (MulAut U)) : U = ⊤ := by
  let := hG.isNilpotent
  apply normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent U
  apply le_antisymm _ U.le_normalizer
  intro g hg
  apply mem_of_normalizerMonoidHom_mem_inner U hcent ⟨g, hg⟩
  apply hrad
  refine ⟨⟨⟨g, hg⟩, rfl⟩, ?_⟩
  have hle : (⊤ : Subgroup (MulAut U)) ≤ pCore p (MulAut U) :=
    le_sSup ⟨inferInstance, ha.to_subgroup ⊤⟩
  exact hle (mem_top _)

/-- An intrinsic radical centric p-subgroup contains every normalizer element
acting trivially on the Frattini quotients of a characteristic subgroup and
its quotient. This can detect elements missed by the action on `U / Φ(U)`. -/
public theorem mem_of_intrinsic_radical_of_characteristic_frattini_actions
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (U : Subgroup G) (hU : IsPGroup p U)
    (hcent : centralizer (U : Set G) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (C : Subgroup U) [C.Characteristic]
    (g : normalizer (U : Set G))
    (hc : quotientAut (frattini C)
      (MulAut.characteristic C (U.normalizerMonoidHom g)) = 1)
    (hq : quotientAut (frattini (U ⧸ C))
      (quotientAut C (U.normalizerMonoidHom g)) = 1) : (g : G) ∈ U := by
  let A := (quotientAut (frattini C)).ker
  let B := (quotientAut (frattini (U ⧸ C))).ker
  have ha : IsPGroup p A := isPGroup_quotientAut_frattini_kernel (hU.to_subgroup C)
  have hb : IsPGroup p B := isPGroup_quotientAut_frattini_kernel (hU.to_quotient C)
  have hab : IsPGroup p (A.prod B) := by
    apply IsPGroup.of_equiv (G := A × B) _ (A.prodEquiv B).symm
    intro x
    obtain ⟨i, hi⟩ := ha x.1
    obtain ⟨j, hj⟩ := hb x.2
    refine ⟨i + j, Prod.ext ?_ ?_⟩
    · change x.1 ^ (p ^ (i + j)) = 1
      rw [pow_add, pow_mul, hi, one_pow]
    · change x.2 ^ (p ^ (i + j)) = 1
      rw [Nat.add_comm i j, pow_add, pow_mul, hj, one_pow]
  have hpre : IsPGroup p ((A.prod B).comap (automorphismPair C)) :=
    hab.comap_of_ker_isPGroup (automorphismPair C)
      (isPGroup_automorphism_pair_kernel C (hU.to_subgroup C))
  have hle : (A.prod B).comap (automorphismPair C) ≤ pCore p (MulAut U) :=
    le_sSup ⟨inferInstance, hpre⟩
  apply mem_of_normalizerMonoidHom_mem_inner U hcent g
  apply hrad
  refine ⟨⟨g, rfl⟩, hle ?_⟩
  change automorphismPair C (U.normalizerMonoidHom g) ∈ A.prod B
  rw [automorphismPair_apply]
  exact ⟨hc, hq⟩

end Subgroup
