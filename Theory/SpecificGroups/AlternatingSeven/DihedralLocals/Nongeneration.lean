module

public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Model

/-!
# Two S₄ overgroups of a common A₇ Sylow cannot generate A₇

Inside each S₄ choose a cubic. The fixed Sylow subgroup and that cubic are
complementary by their coprime orders, so they generate the local subgroup.
The four cubic possibilities place every pair of local subgroups in one of
the previously constructed proper stabilizers. Sylow conjugacy then removes
the choice of the fixed dihedral subgroup.

Source: Aschbacher--Smith F.6.18, printed p.310: the S₄--S₄ amalgams in A₇
generate a proper subgroup. Only nongeneration is needed here.
-/

@[expose] public section
noncomputable section
open Equiv Subgroup
namespace AlternatingSeven.DihedralLocals

private def cubicFour : Perm (Fin 4) := swap 0 1 * swap 1 2
private theorem cubicFour_order : orderOf cubicFour = 3 :=
  orderOf_eq_prime (by decide) (by decide)

local instance : Fintype (Perm (Fin 4)) := fintypePerm

private theorem symmetricFour_relations (a b : Perm (Fin 4))
    (ha : a ^ 3 = 1) (hna : a ≠ 1) (hb : b ^ 4 = 1) (hnb : b ^ 2 ≠ 1) :
    (a * b ^ 2) ^ 3 = 1 ∧ (a * b) ^ 4 = 1 := by
  decide +revert +kernel

/-- Every S₄ containing the fixed eight-group is generated inside one of the
four prescribed cubic families. The statement retains the actual embedding. -/
theorem symmetricFour_containment
    (H : Subgroup Perm7) (hT : twoGroup ≤ H) (e : H ≃* Perm (Fin 4)) :
    ∃ j : Fin 4, ∀ Q : Subgroup Perm7,
      twoGroup ≤ Q → cubic j ∈ Q → H ≤ Q := by
  let a : H := e.symm cubicFour
  have haorder : orderOf a = 3 := (e.symm.orderOf_eq cubicFour).trans cubicFour_order
  have ha3 : a ^ 3 = 1 := haorder ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by intro h; simp [h] at haorder
  let b : H := ⟨r, hT r_mem_twoGroup⟩
  have hb4 : b ^ 4 = 1 := Subtype.ext r_four
  have hb2 : b ^ 2 ≠ 1 := fun h => r_square_ne (congrArg Subtype.val h)
  have hr := symmetricFour_relations (e a) (e b)
    (by simp only [← map_pow, ha3, map_one])
    (fun h => ha1 (e.injective (h.trans (map_one e).symm)))
    (by simp only [← map_pow, hb4, map_one])
    (fun h => hb2 (e.injective (by simpa only [map_pow, map_one] using h)))
  have hcrit : Criterion (a : Perm7) := by
    refine ⟨congrArg Subtype.val ha3, fun h => ha1 (Subtype.ext h), ?_, ?_⟩
    · have h : (a * b ^ 2) ^ 3 = 1 := e.injective (by
        simpa only [map_pow, map_mul, map_one] using hr.1)
      have hh := congrArg H.subtype h
      change ((a : Perm7) * (b : Perm7) ^ 2) ^ 3 = 1 at hh
      rw [show (b : Perm7) = r from rfl] at hh
      exact hh
    · have h : (a * b) ^ 4 = 1 := e.injective (by
        simpa only [map_pow, map_mul, map_one] using hr.2)
      have hh := congrArg H.subtype h
      change ((a : Perm7) * (b : Perm7)) ^ 4 = 1 at hh
      rw [show (b : Perm7) = r from rfl] at hh
      exact hh
  obtain ⟨j, i, hi⟩ := cubic_catalogue a hcrit
  have hHcard : Nat.card H = 24 := by
    rw [Nat.card_congr e.toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hTcard : Nat.card (twoGroup.subgroupOf H) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hT).toEquiv).trans twoGroup_card
  have hCcard : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, haorder]
  have hcomp : (twoGroup.subgroupOf H).IsComplement' (zpowers a) :=
    isComplement'_of_coprime (by rw [hTcard, hCcard, hHcard])
      (by rw [hTcard, hCcard]; decide)
  refine ⟨j, fun Q hTQ hcQ => ?_⟩
  have haQ : (a : Perm7) ∈ Q := by
    rw [hi]
    exact Q.mul_mem (Q.mul_mem (hTQ (tWord_mem_twoGroup i)) hcQ)
      (Q.inv_mem (hTQ (tWord_mem_twoGroup i)))
  have hC : zpowers a ≤ Q.subgroupOf H := zpowers_le.mpr haQ
  intro x hx
  obtain ⟨⟨t, z⟩, htz⟩ := hcomp.2 (⟨x, hx⟩ : H)
  have he : ((t : H) : Perm7) * ((z : H) : Perm7) = x := congrArg Subtype.val htz
  rw [← he]
  exact Q.mul_mem (hTQ t.property) (hC z.property)

/-- The fixed-Sylow pair lies in a proper permutation stabilizer. -/
theorem symmetricFour_pair_not_generate_fixed
    (H₁ H₂ : Subgroup Perm7) (hT₁ : twoGroup ≤ H₁) (hT₂ : twoGroup ≤ H₂)
    (e₁ : H₁ ≃* Perm (Fin 4)) (e₂ : H₂ ≃* Perm (Fin 4)) :
    ¬ alternatingGroup (Fin 7) ≤ H₁ ⊔ H₂ := by
  obtain ⟨i, hi⟩ := symmetricFour_containment H₁ hT₁ e₁
  obtain ⟨j, hj⟩ := symmetricFour_containment H₂ hT₂ e₂
  intro h
  apply alternating_not_le_obstruction i j
  exact h.trans (sup_le
    (hi _ (twoGroup_le_obstruction i j) (cubic_mem_obstruction_left i j))
    (hj _ (twoGroup_le_obstruction i j) (cubic_mem_obstruction_right i j)))

/-- Any two S₄ subgroups containing the same Sylow two-subgroup of A₇
lie in a proper subgroup. No choice of Sylow coordinates is retained. -/
theorem symmetricFour_pair_not_generate
    (S : Sylow 2 A7) (H₁ H₂ : Subgroup A7)
    (hS₁ : (S : Subgroup A7) ≤ H₁) (hS₂ : (S : Subgroup A7) ≤ H₂)
    (e₁ : H₁ ≃* Perm (Fin 4)) (e₂ : H₂ ≃* Perm (Fin 4)) :
    H₁ ⊔ H₂ ≠ ⊤ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A7 S fixedSylow
  let f : A7 →* Perm7 := (alternatingGroup (Fin 7)).subtype.comp
    (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp (MulAut.conj g).injective
  have hS : (S : Subgroup A7).map f = twoGroup := by
    have hh : (S : Subgroup A7).map (MulAut.conj g).toMonoidHom =
        (fixedSylow : Subgroup A7) := congrArg Sylow.toSubgroup hg
    change (S : Subgroup A7).map ((alternatingGroup (Fin 7)).subtype.comp
      (MulAut.conj g).toMonoidHom) = _
    rw [← map_map, hh]
    change (twoGroup.subgroupOf (alternatingGroup (Fin 7))).map
      (alternatingGroup (Fin 7)).subtype = twoGroup
    rw [subgroupOf_map_subtype, inf_eq_left.mpr twoGroup_le_alternating]
  intro hgen
  have hm : H₁.map f ⊔ H₂.map f = alternatingGroup (Fin 7) := by
    rw [← Subgroup.map_sup, hgen]
    change (⊤ : Subgroup A7).map ((alternatingGroup (Fin 7)).subtype.comp
      (MulAut.conj g).toMonoidHom) = _
    rw [← map_map,
      map_top_of_surjective _ (MulAut.conj g).surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply symmetricFour_pair_not_generate_fixed (H₁.map f) (H₂.map f)
    (hS ▸ map_mono hS₁) (hS ▸ map_mono hS₂)
    (((H₁.equivMapOfInjective f hf).symm).trans e₁)
    (((H₂.equivMapOfInjective f hf).symm).trans e₂)
  exact hm.ge

private theorem symmetricFour_central_eq_one (x : Perm (Fin 4))
    (h : ∀ y : Perm (Fin 4), y * x = x * y) : x = 1 := by
  decide +revert +kernel

private theorem central_kernel_injective_on_symmetricFour
    {G : Type*} [Group G] (f : G →* A7) (hk : f.ker ≤ center G)
    (H : Subgroup G) (e : H ≃* Perm (Fin 4)) :
    Function.Injective (f.comp H.subtype) := by
  apply (f.comp H.subtype).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  have hxc : (x : G) ∈ center G := hk hx
  have hxe : e x = 1 := symmetricFour_central_eq_one (e x) (fun y => by
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext ((mem_center_iff.mp hxc) z)))
  exact e.injective (hxe.trans (map_one e).symm)

/-- The same nongeneration holds in every actual central cover of A₇:
its projection is faithful on each centerless S₄ vertex. -/
theorem central_cover_symmetricFour_pair_not_generate
    {G : Type*} [Group G] [Finite G] (f : G →* A7)
    (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (S : Sylow 2 G) (H₁ H₂ : Subgroup G)
    (hS₁ : (S : Subgroup G) ≤ H₁) (hS₂ : (S : Subgroup G) ≤ H₂)
    (e₁ : H₁ ≃* Perm (Fin 4)) (e₂ : H₂ ≃* Perm (Fin 4)) :
    H₁ ⊔ H₂ ≠ ⊤ := by
  have hinj (H : Subgroup G) (e : H ≃* Perm (Fin 4)) :
      Function.Injective (f.subgroupMap H) := by
    intro x y h
    exact central_kernel_injective_on_symmetricFour f hk H e (congrArg Subtype.val h)
  let a₁ : H₁ ≃* H₁.map f := MulEquiv.ofBijective (f.subgroupMap H₁)
    ⟨hinj H₁ e₁, f.subgroupMap_surjective H₁⟩
  let a₂ : H₂ ≃* H₂.map f := MulEquiv.ofBijective (f.subgroupMap H₂)
    ⟨hinj H₂ e₂, f.subgroupMap_surjective H₂⟩
  intro hgen
  apply symmetricFour_pair_not_generate (S.mapSurjective hf) (H₁.map f) (H₂.map f)
    (map_mono hS₁) (map_mono hS₂) (a₁.symm.trans e₁) (a₂.symm.trans e₂)
  rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ hf]

end AlternatingSeven.DihedralLocals
