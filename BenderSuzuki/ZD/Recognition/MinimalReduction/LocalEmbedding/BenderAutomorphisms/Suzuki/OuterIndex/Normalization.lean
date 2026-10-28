module

public import Theory.SpecificGroups.Suzuki.SplitNormalizerGeometry

/-!
# Normalizing an arbitrary Suzuki automorphism

For the concrete Suzuki group over the field of order `2^(2*m+1)`, with
`1 ≤ m`, every automorphism can be adjusted by an inner automorphism to
preserve the standard root subgroup and split torus and fix the Weyl element.

Sylow conjugacy first normalizes the root group. Its normalizer is the Borel,
so the image of a torus generator can be conjugated into the split torus by a
root element. Finally the torus normalizer has two cosets: the Weyl image is
`t*w`, and a square root of `t` in the odd-order torus removes the factor `t`.
All normalizers here are taken in the concrete Suzuki group.

This is the normalization step toward the inner-field coverage used in GLS,
Volume 4, Chapter 4, Lemma 3.1(a,b), and Volume 3, Theorem 2.5.12(b--f).
It does not assume that coverage. The subgroup geometry comes from
Huppert--Blackburn III, XI.3.3, XI.3.10 and XI.3.12 via the imported modules.
-/

namespace BenderSuzuki.MatrixGroups
open scoped Pointwise

private theorem map_aut_mul {G : Type*} [Group G] (H : Subgroup G) (α β : MulAut G) :
    H.map (α * β).toMonoidHom = (H.map β.toMonoidHom).map α.toMonoidHom :=
  (H.map_map α.toMonoidHom β.toMonoidHom).symm

private theorem aut_mem_iff {G : Type*} [Group G] (H : Subgroup G) (α : MulAut G)
    (h : H.map α.toMonoidHom = H) (x : G) : α x ∈ H ↔ x ∈ H := by
  conv_lhs => rw [← h, Subgroup.mem_map_equiv, α.symm_apply_apply]

/-- Sylow conjugacy puts the image of the standard root group back in standard position. -/
public theorem suzukiAut_normalize_root (m : ℕ) (hm : 1 ≤ m)
    (α : MulAut (SuzukiMatrixGroup m)) :
    ∃ g : SuzukiMatrixGroup m,
      (SuzukiRootSubgroup m).map (MulAut.conj g * α).toMonoidHom =
        SuzukiRootSubgroup m := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) (α • P) P
  refine ⟨g, ?_⟩
  have h := congrArg (fun Q : Sylow 2 (SuzukiMatrixGroup m) => (Q : Subgroup (SuzukiMatrixGroup m))) hg
  change ((P : Subgroup _).map α.toMonoidHom).map (MulAut.conj g).toMonoidHom = P at h
  rw [hP] at h
  simpa only [map_aut_mul] using h

/-- A root-preserving automorphism can be adjusted by a root element to preserve the torus. -/
public theorem suzukiAut_normalize_split (m : ℕ) (hm : 1 ≤ m)
    (α : MulAut (SuzukiMatrixGroup m))
    (hU : (SuzukiRootSubgroup m).map α.toMonoidHom = SuzukiRootSubgroup m) :
    ∃ r : SuzukiRootSubgroup m,
      (SuzukiRootSubgroup m).map
        (MulAut.conj (r : SuzukiMatrixGroup m) * α).toMonoidHom = SuzukiRootSubgroup m ∧
      (SuzukiSplitTorus m).map
        (MulAut.conj (r : SuzukiMatrixGroup m) * α).toMonoidHom = SuzukiSplitTorus m := by
  have := suzukiSplitTorus_isCyclic m hm
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := SuzukiSplitTorus m)
  have htne : (t : SuzukiMatrixGroup m) ≠ 1 := by
    intro h
    have ht1 : t = 1 := Subtype.ext h
    have hsub : Subsingleton (SuzukiSplitTorus m) := by
      apply subsingleton_of_forall_eq 1
      intro x
      have hx := ht x
      simpa [ht1] using hx
    have hc : Nat.card (SuzukiSplitTorus m) = 1 := Nat.card_unique
    rw [suzukiSplitTorus_card m hm] at hc
    have hq : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have htn : (t : SuzukiMatrixGroup m) ∉ SuzukiRootSubgroup m := by
    intro h
    exact htne (Subgroup.mem_bot.mp
      ((suzukiRootSubgroup_disjoint_splitTorus m hm).le_bot ⟨h, t.property⟩))
  have hb : α t ∈ SuzukiBorelSubgroup m := by
    rw [← suzukiRootSubgroup_normalizer m hm, ← hU,
      ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem α.toMonoidHom
      (suzukiSplitTorus_le_normalizer_root m t.property)
  have hn : α t ∉ SuzukiRootSubgroup m := fun h =>
    htn ((aut_mem_iff _ α hU t).mp h)
  obtain ⟨r, hr⟩ := suzukiBorelSubgroup_conjugate_into_split m hm (α t) hb hn
  let β := MulAut.conj (r : SuzukiMatrixGroup m)⁻¹ * α
  have hβt : β t ∈ SuzukiSplitTorus m := by
    simpa [β, MulAut.mul_apply, MulAut.conj_apply] using hr
  refine ⟨r⁻¹, ?_, ?_⟩
  · rw [map_aut_mul, hU]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer ((SuzukiRootSubgroup m).inv_mem r.property))
  · change (SuzukiSplitTorus m).map β.toMonoidHom = SuzukiSplitTorus m
    apply Subgroup.eq_of_le_of_card_ge
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := ht ⟨y, hy⟩
      have hy' : (t : SuzukiMatrixGroup m) ^ n = y := congrArg Subtype.val hn
      rw [← hy', map_zpow]
      exact (SuzukiSplitTorus m).zpow_mem hβt n
    · rw [Subgroup.card_map_of_injective β.injective]

/-- Once the root group and torus are preserved, a torus conjugation fixes the Weyl element. -/
public theorem suzukiAut_normalize_weyl (m : ℕ) (hm : 1 ≤ m)
    (α : MulAut (SuzukiMatrixGroup m))
    (hU : (SuzukiRootSubgroup m).map α.toMonoidHom = SuzukiRootSubgroup m)
    (hT : (SuzukiSplitTorus m).map α.toMonoidHom = SuzukiSplitTorus m) :
    ∃ s : SuzukiSplitTorus m,
      (SuzukiRootSubgroup m).map
        (MulAut.conj (s : SuzukiMatrixGroup m) * α).toMonoidHom = SuzukiRootSubgroup m ∧
      (SuzukiSplitTorus m).map
        (MulAut.conj (s : SuzukiMatrixGroup m) * α).toMonoidHom = SuzukiSplitTorus m ∧
      (MulAut.conj (s : SuzukiMatrixGroup m) * α) (suzukiWeyl m) = suzukiWeyl m := by
  have hn : α (suzukiWeyl m) ∈ Subgroup.normalizer (SuzukiSplitTorus m) := by
    rw [← hT, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem α.toMonoidHom (suzukiWeyl_mem_splitTorus_normalizer m)
  have hnot : α (suzukiWeyl m) ∉ SuzukiSplitTorus m := fun h =>
    suzukiWeyl_not_mem_splitTorus m ((aut_mem_iff _ α hT _).mp h)
  obtain ⟨t, ht⟩ := ((suzukiSplitTorus_normalizer_forms m hm _).mp hn).resolve_left hnot
  have hodd : Odd (Nat.card (SuzukiSplitTorus m)) := by
    rw [suzukiSplitTorus_card m hm]
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide))
      (even_two.pow_of_ne_zero (by omega)) odd_one
  obtain ⟨s, hs⟩ := (powCoprime hodd.coprime_two_right).surjective t
  have hs' : (s : SuzukiMatrixGroup m) * s = t := by
    simpa only [powCoprime_apply, pow_two, Subgroup.coe_mul] using congrArg Subtype.val hs
  refine ⟨s⁻¹, ?_, ?_, ?_⟩
  · rw [map_aut_mul, hU]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (suzukiSplitTorus_le_normalizer_root m ((SuzukiSplitTorus m).inv_mem s.property))
  · rw [map_aut_mul, hT]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer ((SuzukiSplitTorus m).inv_mem s.property))
  · change (s : SuzukiMatrixGroup m)⁻¹ * α (suzukiWeyl m) *
        ((s : SuzukiMatrixGroup m)⁻¹)⁻¹ = suzukiWeyl m
    rw [ht, inv_inv, ← hs']
    have hws : suzukiWeyl m * (s : SuzukiMatrixGroup m) =
        (s : SuzukiMatrixGroup m)⁻¹ * suzukiWeyl m := by
      calc
        _ = (suzukiWeyl m * (s : SuzukiMatrixGroup m) * suzukiWeyl m) *
            suzukiWeyl m := by rw [mul_assoc, suzukiWeyl_sq, mul_one]
        _ = _ := by rw [suzukiWeyl_conj_splitTorus]
    calc
      _ = (s : SuzukiMatrixGroup m) * (suzukiWeyl m * s) := by group
      _ = _ := by rw [hws]; group

/-- Every automorphism of the concrete Suzuki group admits an inner adjustment
preserving the standard root subgroup and split torus and fixing the Weyl element. -/
public theorem suzukiAut_exists_normalized (m : ℕ) (hm : 1 ≤ m)
    (α : MulAut (SuzukiMatrixGroup m)) :
    ∃ g : SuzukiMatrixGroup m,
      let β := MulAut.conj g * α
      (SuzukiRootSubgroup m).map β.toMonoidHom = SuzukiRootSubgroup m ∧
      (SuzukiSplitTorus m).map β.toMonoidHom = SuzukiSplitTorus m ∧
      β (suzukiWeyl m) = suzukiWeyl m := by
  obtain ⟨g, hg⟩ := suzukiAut_normalize_root m hm α
  obtain ⟨r, hrU, hrT⟩ := suzukiAut_normalize_split m hm (MulAut.conj g * α) hg
  obtain ⟨s, hsU, hsT, hsw⟩ := suzukiAut_normalize_weyl m hm
    (MulAut.conj (r : SuzukiMatrixGroup m) * (MulAut.conj g * α)) hrU hrT
  refine ⟨(s : SuzukiMatrixGroup m) * (r : SuzukiMatrixGroup m) * g, ?_⟩
  simpa only [map_mul, mul_assoc] using And.intro hsU (And.intro hsT hsw)

end BenderSuzuki.MatrixGroups
