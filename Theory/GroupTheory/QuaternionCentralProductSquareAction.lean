module

public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Theory.GroupTheory.SpecificGroups.QuaternionEightSquareAut

/-!
# Outer square actions on a quaternion central product

Suppose two commuting quaternion subgroups generate a finite group and
intersect in order two. An inner twist of the square of an automorphism of
two-power order preserves both factors. If that twisted square is not inner
on the whole group, its restriction to either quaternion factor is not inner.

Automorphisms permute the two intrinsic quaternion factors. If the original
automorphism preserves them, its restrictions have inner squares: the inner
automorphisms of a quaternion group have index six. If it swaps the factors,
it transports innerness of its square from one factor to the other. Inner
actions on both commuting factors combine into conjugation by the product
of their conjugating elements. Finally, an ambient inner twist restricts to
an inner twist on each factor, by decomposing its conjugating element.

This is the quaternion central-product calculation in Janko–Thompson (1970),
§4, pp.390–391; see
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Subgroup
variable {G : Type*} [Group G]

private theorem cp_decomp (B C : Subgroup G)
    (hjoin : B ⊔ C = ⊤) (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (x : G) : ∃ b : B, ∃ c : C, (b : G) * (c : G) = x := by
  have hn : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hx : x ∈ (↑(B ⊔ C) : Set G) := by rw [hjoin]; trivial
  rw [coe_mul_of_left_le_normalizer_right B C hn] at hx
  obtain ⟨b, hb, c, hc, hbc⟩ := hx
  exact ⟨⟨b, hb⟩, ⟨c, hc⟩, hbc⟩

private theorem cp_conj_left (B C : Subgroup G)
    (hjoin : B ⊔ C = ⊤) (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (q : G) : ∃ b : B, ∀ x : B, (MulAut.conj q) (x : G) =
      (b : G) * (x : G) * (b : G)⁻¹ := by
  obtain ⟨b, c, rfl⟩ := cp_decomp B C hjoin hcomm q
  refine ⟨b, fun x => ?_⟩
  have hc : (MulAut.conj (c : G)) (x : G) = x := by
    change (c : G) * (x : G) * (c : G)⁻¹ = x
    rw [← hcomm x x.property c c.property, mul_inv_cancel_right]
  rw [map_mul, MulAut.mul_apply, hc, MulAut.conj_apply]

private theorem cp_inner (B C : Subgroup G)
    (hjoin : B ⊔ C = ⊤) (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (e : MulAut G)
    (hb : ∃ b : B, ∀ x : B, e (x : G) = (b : G) * (x : G) * (b : G)⁻¹)
    (hc : ∃ c : C, ∀ x : C, e (x : G) = (c : G) * (x : G) * (c : G)⁻¹) :
    ∃ p : G, e = MulAut.conj p := by
  obtain ⟨b, hb⟩ := hb
  obtain ⟨c, hc⟩ := hc
  refine ⟨(b : G) * (c : G), ?_⟩
  ext x
  obtain ⟨u, v, rfl⟩ := cp_decomp B C hjoin hcomm x
  have hcu : (MulAut.conj (c : G)) (u : G) = u := by
    change (c : G) * (u : G) * (c : G)⁻¹ = u
    rw [← hcomm u u.property c c.property, mul_inv_cancel_right]
  have hbw : (MulAut.conj (b : G)) ((MulAut.conj (c : G)) (v : G)) =
      (MulAut.conj (c : G)) (v : G) := by
    have hw : (MulAut.conj (c : G)) (v : G) ∈ C :=
      C.mul_mem (C.mul_mem c.property v.property) (C.inv_mem c.property)
    change (b : G) * _ * (b : G)⁻¹ = _
    rw [hcomm b b.property _ hw, mul_inv_cancel_right]
  rw [map_mul, map_mul (MulAut.conj ((b : G) * (c : G))),
    map_mul, MulAut.mul_apply, MulAut.mul_apply, hcu, hbw]
  rw [hb, hc]
  rfl

private theorem cp_untwist (B C : Subgroup G)
    (hjoin : B ⊔ C = ⊤) (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (e : MulAut G) (q : G) (he : B.map e.toMonoidHom = B)
    (hi : ∃ b : B, ∀ x : B, (MulAut.conj q * e) (x : G) =
      (b : G) * (x : G) * (b : G)⁻¹) :
    ∃ b : B, ∀ x : B, e (x : G) = (b : G) * (x : G) * (b : G)⁻¹ := by
  obtain ⟨a, ha⟩ := cp_conj_left B C hjoin hcomm q
  obtain ⟨b, hb⟩ := hi
  refine ⟨a⁻¹ * b, fun x => ?_⟩
  have hx : e (x : G) ∈ B :=
    (le_of_eq he) (mem_map_of_mem e.toMonoidHom x.property)
  have hh := hb x
  change (MulAut.conj q) (e (x : G)) = _ at hh
  rw [ha ⟨e (x : G), hx⟩] at hh
  change e (x : G) = ((a : G)⁻¹ * (b : G)) * (x : G) * ((a : G)⁻¹ * (b : G))⁻¹
  apply (MulAut.conj (a : G)).injective
  change (a : G) * e (x : G) * (a : G)⁻¹ = _
  rw [hh]
  simp only [MulAut.conj_apply]
  group

private theorem quaternion_preserving_sq_inner (B : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (e : MulAut G)
    (he : B.map e.toMonoidHom = B) (n : ℕ) (hn : e ^ (2^n) = 1) :
    ∃ b : B, ∀ x : B, (e ^ 2) (x : G) = (b : G) * (x : G) * (b : G)⁻¹ := by
  obtain ⟨model⟩ := hB
  let f : MulAut B := (e.subgroupMap B).trans (MulEquiv.subgroupCongr he)
  have hf (k : ℕ) (x : B) : ((f^k) x : G) = (e^k) (x : G) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [pow_succ', MulAut.mul_apply]
      change e ((f^k) x : G) = e ((e^k) (x : G))
      rw [ih]
  have hfn : f ^ (2^n) = 1 := by
    ext x
    rw [hf, hn]
    rfl
  obtain ⟨b, hb⟩ := QuaternionGroup.exists_conj_sq_of_two_pow_eq_one_of_equiv model f n hfn
  refine ⟨b, fun x => ?_⟩
  rw [← hf, hb]
  rfl

private theorem cp_swap_sq_inner (B C : Subgroup G) (e : MulAut G)
    (hBC : B.map e.toMonoidHom = C)
    (hi : ∃ b : B, ∀ x : B, (e ^ 2) (x : G) = (b : G) * (x : G) * (b : G)⁻¹) :
    ∃ c : C, ∀ x : C, (e ^ 2) (x : G) = (c : G) * (x : G) * (c : G)⁻¹ := by
  obtain ⟨b, hb⟩ := hi
  refine ⟨⟨e b, hBC ▸ mem_map_of_mem e.toMonoidHom b.property⟩, fun x => ?_⟩
  have hx : (x : G) ∈ B.map e.toMonoidHom := hBC.symm ▸ x.property
  obtain ⟨y, hy, hyx⟩ := hx
  have hh := congrArg e (hb ⟨y, hy⟩)
  simp only [map_mul, map_inv, pow_two, MulAut.mul_apply] at hh ⊢
  change e (e (x : G)) = e (b : G) * (x : G) * (e (b : G))⁻¹
  rw [← hyx]
  exact hh

private theorem cp_conj_map (B C : Subgroup G)
    (hjoin : B ⊔ C = ⊤) (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (q : G) : B.map (MulAut.conj q).toMonoidHom = B := by
  have : B.Normal := by
    constructor
    intro x hx g
    obtain ⟨b, hb⟩ := cp_conj_left B C hjoin hcomm g
    change (MulAut.conj g) x ∈ B
    rw [hb ⟨x, hx⟩]
    exact B.mul_mem (B.mul_mem b.property hx) (B.inv_mem b.property)
  exact Normal.map_conj_eq B q

variable [Finite G]

private theorem quaternion_square_outer_left (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (e : MulAut G) (n : ℕ) (hn : e ^ (2^n) = 1)
    (ho : ¬ ∃ p : G, e ^ 2 = MulAut.conj p) :
    ¬ ∃ b : B, ∀ x : B, (e ^ 2) (x : G) = (b : G) * (x : G) * (b : G)⁻¹ := by
  intro hi
  apply ho
  have himage (D : Subgroup G) (hD : Nonempty (D ≃* QuaternionGroup 2)) :
      D.map e.toMonoidHom = B ∨ D.map e.toMonoidHom = C := by
    obtain ⟨model⟩ := hD
    exact quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
      ⟨(e.subgroupMap D).symm.trans model⟩ (by rw [hjoin]; exact le_top)
  rcases himage B hB with hb | hb
  · have hc : C.map e.toMonoidHom = C := by
      rcases himage C hC with hc | hc
      · have heq : C = B := map_injective e.injective (hc.trans hb.symm)
        simpa only [heq] using hb
      · exact hc
    exact cp_inner B C hjoin hcomm (e ^ 2) hi
      (quaternion_preserving_sq_inner C hC e hc n hn)
  · exact cp_inner B C hjoin hcomm (e ^ 2) hi (cp_swap_sq_inner B C e hb hi)

/-- A non-inner inner twist of the square of a two-power-order automorphism
preserves the two intrinsic quaternion factors and is outer on each factor. -/
public theorem quaternion_central_product_square_action
    (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (α β : MulAut G) (q : G) (n : ℕ)
    (hβ : β ^ (2^n) = 1) (hα : α = MulAut.conj q * β ^ 2)
    (hnoninner : ¬ ∃ p : G, α = MulAut.conj p) :
    B.map α.toMonoidHom = B ∧ C.map α.toMonoidHom = C ∧
      (¬ ∃ b : B, ∀ x : B, α (x : G) = (b : G) * (x : G) * (b : G)⁻¹) ∧
      (¬ ∃ c : C, ∀ x : C, α (x : G) = (c : G) * (x : G) * (c : G)⁻¹) := by
  have hcomm' : ∀ c ∈ C, ∀ b ∈ B, c * b = b * c :=
    fun c hc b hb => (hcomm b hb c hc).symm
  have hjoin' : C ⊔ B = ⊤ := by rw [sup_comm]; exact hjoin
  have hinter' : Nat.card (C ⊓ B : Subgroup G) = 2 := by
    rw [inf_comm]; exact hinter
  have hs := quaternion_factors_invariant_of_square B C hB hC hinter hcomm β
    (by rw [hjoin]; exact map_top_of_surjective β.toMonoidHom β.surjective)
  have hcomp : β.toMonoidHom.comp β.toMonoidHom = (β ^ 2).toMonoidHom := by
    ext x
    simp [pow_two]
  rw [map_map, map_map, hcomp] at hs
  have ho : ¬ ∃ p : G, β ^ 2 = MulAut.conj p := by
    rintro ⟨p, hp⟩
    exact hnoninner ⟨q * p, by rw [hα, hp, map_mul]⟩
  have hmap (D E : Subgroup G) (hj : D ⊔ E = ⊤)
      (hc : ∀ d ∈ D, ∀ e ∈ E, d * e = e * d)
      (hd : D.map (β ^ 2).toMonoidHom = D) : D.map α.toMonoidHom = D := by
    have hcomp' : α.toMonoidHom =
        (MulAut.conj q).toMonoidHom.comp (β ^ 2).toMonoidHom := by
      rw [hα]
      rfl
    rw [hcomp', ← map_map, hd]
    exact cp_conj_map D E hj hc q
  refine ⟨hmap B C hjoin hcomm hs.1, hmap C B hjoin' hcomm' hs.2, ?_, ?_⟩
  · intro hi
    apply quaternion_square_outer_left B C hB hC hjoin hinter hcomm β n hβ ho
    apply cp_untwist B C hjoin hcomm (β ^ 2) q hs.1
    simpa only [← hα] using hi
  · intro hi
    apply quaternion_square_outer_left C B hC hB hjoin' hinter' hcomm' β n hβ ho
    apply cp_untwist C B hjoin' hcomm' (β ^ 2) q hs.2
    simpa only [← hα] using hi

end Subgroup
