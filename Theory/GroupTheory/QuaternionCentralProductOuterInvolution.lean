module

public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-!
# Outer involutions on both factors of a quaternion central product

Let two commuting quaternion subgroups generate the ambient finite group and
have intersection of order two. An involutive automorphism preserving both
factors and acting outerly on each has elementary abelian fixed subgroup of
order four. Every cocycle for this action is a coboundary.

A kernel-checked table on the twenty-four possible quaternion generator pairs
computes the central difference fibers of an outer involution. For either
central element `d`, there are two solutions to `x⁻¹ * α x = d`, and each has
square `d`. A central norm `x * α x` forces `x` to be a coboundary. The table is
transported through quaternion isomorphisms and restriction to invariant factors.

The fixed pairs in the direct product are parametrized by the common central
element and the two difference fibers, giving eight pairs. The surjective
multiplication homomorphism preserves subgroup indices and has kernel of order
two, so the fixed subgroup has order four. The square calculation proves it is
elementary abelian. Finally, each component of an ambient cocycle has norm in
the common intersection, and its factor coboundary witnesses multiply to give
the required ambient witness.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.391–392, case (c),
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
The quaternion generator parametrization follows the pattern of
`Theory.GroupTheory.SpecificGroups.QuaternionEightAut`.
-/

namespace Subgroup
private abbrev Q := QuaternionGroup 2
private def pairMap (p : Q × Q) : Q → Q
  | .a i => p.1 ^ i.val
  | .xa i => p.2 * p.1 ^ i.val
private def goodPair (p : Q × Q) : Prop :=
  p.1 ^ 2 = QuaternionGroup.a 2 ∧ p.2 ^ 2 = QuaternionGroup.a 2 ∧
    p.1 * p.2 ≠ p.2 * p.1
private instance : DecidablePred goodPair := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private abbrev Pairs := {p : Q × Q // goodPair p}
private theorem aut_pair (e : MulAut Q) : ∃ p : Pairs, ∀ x, pairMap p.val x = e x := by
  have hs : ∀ x : Q, x^2 ≠ 1 → x^2 = QuaternionGroup.a 2 := by decide
  have hsq (x : Q) (hx : x^2 ≠ 1) : (e x)^2 = QuaternionGroup.a 2 := by
    apply hs
    intro he
    apply hx
    apply e.injective
    simpa only [map_pow, map_one] using he
  refine ⟨⟨(e (.a 1), e (.xa 0)), hsq _ (by decide), hsq _ (by decide), ?_⟩, ?_⟩
  · intro he
    have hn : (QuaternionGroup.a 1 : Q) * .xa 0 ≠ .xa 0 * .a 1 := by decide
    apply hn
    apply e.injective
    simpa only [map_mul] using he
  · intro x
    cases x with
    | a i =>
      change (e (QuaternionGroup.a 1))^i.val = e (QuaternionGroup.a i)
      rw [← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    | xa i =>
      change e (QuaternionGroup.xa 0) * (e (QuaternionGroup.a 1))^i.val = e (QuaternionGroup.xa i)
      rw [← map_pow, ← map_mul, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val,
        QuaternionGroup.xa_mul_a, zero_add]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem outer_table : ∀ p : Pairs,
    (∀ x : Q, pairMap p.val (pairMap p.val x) = x) →
    (¬ ∃ b : Q, ∀ x : Q, pairMap p.val x = b*x*b⁻¹) →
    (∀ d : Q, d^2 = 1 →
      Fintype.card {x : Q // x⁻¹ * pairMap p.val x = d} = 2 ∧
      ∀ x : Q, x⁻¹ * pairMap p.val x = d → x^2 = d) ∧
    (∀ x : Q, (x * pairMap p.val x)^2 = 1 →
      ∃ y : Q, x = y * pairMap p.val y⁻¹) := by decide

/-- The two central difference fibers of an outer quaternion involution each
have size two; their squares equal the difference. Central norms are coboundaries. -/
public theorem quaternion_outer_involution_fibers
    {D : Type*} [Group D] (model : D ≃* QuaternionGroup 2)
    (e : MulAut D) (he : e^2 = 1)
    (hout : ¬ ∃ b : D, ∀ x : D, e x = b*x*b⁻¹) :
    (∀ d : D, d^2 = 1 →
      Nat.card {x : D // x⁻¹ * e x = d} = 2 ∧
      ∀ x : D, x⁻¹ * e x = d → x^2 = d) ∧
    (∀ x : D, (x * e x)^2 = 1 → ∃ y : D, x = y * e y⁻¹) := by
  let a : MulAut Q := MulAut.congr model e
  obtain ⟨p, hp⟩ := aut_pair a
  have hi : ∀ x, pairMap p.val (pairMap p.val x) = x := by
    intro x
    rw [hp, hp]
    have ha : a^2 = 1 := by dsimp [a]; rw [← map_pow, he, map_one]
    simpa [pow_two] using DFunLike.congr_fun ha x
  have ho : ¬ ∃ b : Q, ∀ x : Q, pairMap p.val x = b*x*b⁻¹ := by
    rintro ⟨b, hb⟩
    apply hout
    refine ⟨model.symm b, fun x => model.injective ?_⟩
    have hh := hb (model x)
    rw [hp] at hh
    simpa [a, MulAut.congr_apply] using hh
  obtain ⟨hf, hn⟩ := outer_table p hi ho
  have hmap (x : D) : pairMap p.val (model x) = model (e x) := by
    rw [hp]; simp [a, MulAut.congr_apply]
  constructor
  · intro d hd
    have hd' : (model d)^2 = 1 := by rw [← map_pow, hd, map_one]
    obtain ⟨hc, hs⟩ := hf (model d) hd'
    constructor
    · let E : {x : D // x⁻¹ * e x = d} ≃
          {x : Q // x⁻¹ * pairMap p.val x = model d} :=
        model.toEquiv.subtypeEquiv (by
          intro x
          change x⁻¹ * e x = d ↔ (model x)⁻¹ * pairMap p.val (model x) = model d
          rw [hmap, ← map_inv, ← map_mul]
          exact model.injective.eq_iff.symm)
      rw [Nat.card_congr E, Nat.card_eq_fintype_card, hc]
    · intro x hx
      apply model.injective
      rw [map_pow]
      apply hs
      rw [hmap, ← map_inv, ← map_mul, hx]
  · intro x hx
    have hx' : (model x * pairMap p.val (model x))^2 = 1 := by
      rw [hmap, ← map_mul, ← map_pow, hx, map_one]
    obtain ⟨y, hy⟩ := hn (model x) hx'
    refine ⟨model.symm y, model.injective ?_⟩
    rw [map_mul, MulEquiv.apply_symm_apply, ← hmap, map_inv,
      MulEquiv.apply_symm_apply]
    exact hy
/-- Restrict the quaternion calculation to an invariant factor, with all
identities expressed in the ambient group. -/
public theorem quaternion_outer_involution_factor_data
    {H : Type*} [Group H] [Finite H] (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (α : MulAut H) (hα : α^2 = 1) (hmap : B.map α.toMonoidHom = B)
    (hout : ¬ ∃ b : B, ∀ x : B, α (x:H) = (b:H)*(x:H)*(b:H)⁻¹) :
    (∀ d : (B ⊓ C : Subgroup H),
      Nat.card {b : B // (b:H)⁻¹ * α (b:H) = (d:H)} = 2 ∧
      ∀ b : B, (b:H)⁻¹ * α (b:H) = (d:H) → (b:H)^2 = (d:H)) ∧
    (∀ b : B, (b:H) * α (b:H) ∈ C →
      ∃ y : B, (b:H) = (y:H) * α (y:H)⁻¹) := by
  obtain ⟨model⟩ := hB
  let e : MulAut B := (B.equivMapOfInjective α.toMonoidHom α.injective).trans
    (MulEquiv.subgroupCongr hmap)
  have heval (x : B) : (e x : H) = α (x:H) := rfl
  have he2 : e^2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change α (α (x:H)) = (x:H)
    simpa [pow_two] using DFunLike.congr_fun hα (x:H)
  have heout : ¬ ∃ b : B, ∀ x : B, e x = b*x*b⁻¹ := by
    rintro ⟨b, hb⟩
    exact hout ⟨b, fun x => congrArg Subtype.val (hb x)⟩
  obtain ⟨hf, hn⟩ := quaternion_outer_involution_fibers model e he2 heout
  have hd2 (d : (B ⊓ C : Subgroup H)) : (d:H)^2 = 1 := by
    have hh := pow_card_eq_one' (x := d)
    rw [hinter] at hh
    exact congrArg Subtype.val hh
  constructor
  · intro d
    let dd : B := ⟨d, d.property.1⟩
    obtain ⟨hc, hs⟩ := hf dd (Subtype.ext (hd2 d))
    constructor
    · rw [← hc]
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun b => ⟨fun h => Subtype.ext h,
        fun h => congrArg Subtype.val h⟩)
    · intro b hb
      exact congrArg Subtype.val (hs b (Subtype.ext hb))
  · intro b hb
    have hmem : (b:H) * α (b:H) ∈ B := by
      exact B.mul_mem b.property (heval b ▸ (e b).property)
    have hnorm : (b * e b)^2 = 1 := by
      apply Subtype.ext
      exact hd2 ⟨(b:H) * α (b:H), hmem, hb⟩
    obtain ⟨y, hy⟩ := hn b hnorm
    exact ⟨y, congrArg Subtype.val hy⟩
/-- An involution outer on both quaternion factors has elementary fixed four,
and every involution cocycle is a coboundary. -/
public theorem quaternion_central_product_outer_involution
    {H : Type*} [Group H] [Finite H] (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (α : MulAut H) (hα : α^2 = 1)
    (hBm : B.map α.toMonoidHom = B) (hCm : C.map α.toMonoidHom = C)
    (hBout : ¬ ∃ b : B, ∀ x : B, α (x:H) = (b:H)*(x:H)*(b:H)⁻¹)
    (hCout : ¬ ∃ c : C, ∀ x : C, α (x:H) = (c:H)*(x:H)*(c:H)⁻¹) :
    let F := α.toMonoidHom.eqLocus (MonoidHom.id H)
    IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      ∀ x : H, x * α x = 1 → ∃ p : H, x = p * α p⁻¹ := by
  classical
  let I := B ⊓ C
  let F := α.toMonoidHom.eqLocus (MonoidHom.id H)
  obtain ⟨hBf, hBn⟩ := quaternion_outer_involution_factor_data B C hB hinter α hα hBm hBout
  obtain ⟨hCf', hCn⟩ := quaternion_outer_involution_factor_data C B hC
    (by simpa [inf_comm] using hinter) α hα hCm hCout
  have hCf (d : I) :
      Nat.card {c : C // (c:H)⁻¹ * α (c:H) = (d:H)} = 2 ∧
      ∀ c : C, (c:H)⁻¹ * α (c:H) = (d:H) → (c:H)^2 = (d:H) :=
    hCf' ⟨d, d.property.2, d.property.1⟩
  have hBm' (b : B) : α (b:H) ∈ B := by
    exact hBm.le (mem_map.mpr ⟨b, b.property, rfl⟩)
  have hCm' (c : C) : α (c:H) ∈ C := by
    exact hCm.le (mem_map.mpr ⟨c, c.property, rfl⟩)
  have hnorm : B ≤ normalizer (C : Set H) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hdecomp (x : H) : ∃ b : B, ∃ c : C, (b:H)*(c:H)=x := by
    have hx : x ∈ (↑(B ⊔ C) : Set H) := by rw [hjoin]; trivial
    rw [coe_mul_of_left_le_normalizer_right B C hnorm] at hx
    obtain ⟨b, hb, c, hc, he⟩ := hx
    exact ⟨⟨b,hb⟩, ⟨c,hc⟩, he⟩
  have hI2 (d : I) : (d:H)^2 = 1 := by
    have hh := pow_card_eq_one' (x := d)
    rw [show Nat.card I = 2 from hinter] at hh
    exact congrArg Subtype.val hh
  have hdiff (b : B) (c : C) :
      ((b:H)⁻¹ * α (b:H)) * ((c:H)⁻¹ * α (c:H)) =
      ((b:H)*(c:H))⁻¹ * α ((b:H)*(c:H)) := by
    have hb : (b:H)⁻¹ * α (b:H) ∈ B := B.mul_mem (B.inv_mem b.property) (hBm' b)
    rw [mul_inv_rev, map_mul]
    calc
      _ = (c:H)⁻¹ * (((b:H)⁻¹ * α (b:H)) * α (c:H)) := by
        rw [← mul_assoc, hcomm _ hb _ (C.inv_mem c.property), mul_assoc]
      _ = _ := by group
  have hfixed (b : B) (c : C) : α ((b:H)*(c:H)) = (b:H)*(c:H) ↔
      ∃ d : I, (b:H)⁻¹ * α (b:H) = (d:H) ∧
        (c:H)⁻¹ * α (c:H) = (d:H) := by
    constructor
    · intro hf
      have hp : ((b:H)⁻¹ * α (b:H)) * ((c:H)⁻¹ * α (c:H)) = 1 := by
        rw [hdiff, hf, inv_mul_cancel]
      have he : (b:H)⁻¹ * α (b:H) = ((c:H)⁻¹ * α (c:H))⁻¹ :=
        eq_inv_of_mul_eq_one_left hp
      have hdb : (b:H)⁻¹ * α (b:H) ∈ B := B.mul_mem (B.inv_mem b.property) (hBm' b)
      have hdc : (b:H)⁻¹ * α (b:H) ∈ C := by
        rw [he]; exact C.inv_mem (C.mul_mem (C.inv_mem c.property) (hCm' c))
      let d : I := ⟨(b:H)⁻¹ * α (b:H), hdb, hdc⟩
      refine ⟨d, rfl, ?_⟩
      have hd : (d:H) * (d:H) = 1 := by simpa [pow_two] using hI2 d
      exact mul_left_cancel (hp.trans hd.symm)
    · rintro ⟨d, hb, hc⟩
      have hh : ((b:H)*(c:H))⁻¹ * α ((b:H)*(c:H)) = 1 := by
        rw [← hdiff, hb, hc, ← pow_two, hI2]
      exact (inv_mul_eq_one.mp hh).symm
  let m : B × C →* H := {
    toFun := fun p => (p.1:H)*(p.2:H)
    map_one' := by simp
    map_mul' := by
      rintro ⟨b,c⟩ ⟨b',c'⟩
      change ((b:H)*(b':H))*((c:H)*(c':H)) = ((b:H)*(c:H))*((b':H)*(c':H))
      rw [mul_assoc, ← mul_assoc (b':H), hcomm b' b'.property c c.property,
        mul_assoc, ← mul_assoc] }
  have hm : Function.Surjective m := by
    intro x
    obtain ⟨b,c,hbc⟩ := hdecomp x
    exact ⟨(b,c),hbc⟩
  let D := F.comap m
  let Fib (d : I) := {b : B // (b:H)⁻¹ * α (b:H) = (d:H)} ×
    {c : C // (c:H)⁻¹ * α (c:H) = (d:H)}
  let f : (Σ d : I, Fib d) → D := fun q =>
    ⟨(q.2.1.val, q.2.2.val), (hfixed _ _).mpr ⟨q.1, q.2.1.property, q.2.2.property⟩⟩
  have hfinj : Function.Injective f := by
    rintro ⟨d, b, c⟩ ⟨d', b', c'⟩ hh
    have hb : b.val = b'.val := congrArg (fun x : D => x.val.1) hh
    have hc : c.val = c'.val := congrArg (fun x : D => x.val.2) hh
    have hd : d = d' := by
      apply Subtype.ext
      exact b.property.symm.trans ((congrArg (fun x : B => (x:H)⁻¹ * α (x:H)) hb).trans b'.property)
    subst d'
    have hb' : b = b' := Subtype.ext hb
    have hc' : c = c' := Subtype.ext hc
    subst b'; subst c'; rfl
  have hfsurj : Function.Surjective f := by
    rintro ⟨⟨b,c⟩,hbc⟩
    obtain ⟨d,hb,hc⟩ := (hfixed b c).mp hbc
    exact ⟨⟨d,⟨b,hb⟩,⟨c,hc⟩⟩,rfl⟩
  let : Fintype I := Fintype.ofFinite I
  have hDcard : Nat.card D = 8 := by
    rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfinj,hfsurj⟩), Nat.card_sigma]
    have hfcard (d : I) : Nat.card (Fib d) = 4 := by
      rw [Nat.card_prod, (hBf d).1, (hCf d).1]
    simp only [hfcard, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Nat.card_eq_fintype_card, show Nat.card I = 2 from hinter]
  have h8 (K : Subgroup H) (hK : Nonempty (K ≃* QuaternionGroup 2)) : Nat.card K = 8 := by
    obtain ⟨e⟩ := hK
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hHcard : Nat.card H = 32 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes C B hnorm
    rw [h8 B hB, h8 C hC, inf_comm C B, sup_comm C B, hinter, hjoin, card_top] at hh
    omega
  have hFcard : Nat.card F = 4 := by
    have hh := D.card_mul_index
    rw [hDcard, F.index_comap_of_surjective hm, Nat.card_prod, h8 B hB, h8 C hC] at hh
    have hf := F.card_mul_index
    rw [hHcard] at hf
    have hi : F.index = 8 := by omega
    rw [hi] at hf
    omega
  have hFsq (x : F) : x^2 = 1 := by
    obtain ⟨b,c,hbc⟩ := hdecomp x
    have hx : α ((b:H)*(c:H)) = (b:H)*(c:H) := by
      rw [hbc]; exact x.property
    obtain ⟨d,hb,hc⟩ := (hfixed b c).mp hx
    apply Subtype.ext
    change (x:H)^2 = 1
    rw [← hbc, (show Commute (b:H) (c:H) from hcomm b b.property c c.property).mul_pow,
      (hBf d).2 b hb, (hCf d).2 c hc, ← pow_two, hI2]
  have helem : IsElementaryAbelian 2 F := by
    have hinv (x : F) : x⁻¹ = x := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using hFsq x
    exact {
      toIsMulCommutative := ⟨⟨fun x y => by
        calc
          x*y = (x*y)⁻¹ := (hinv _).symm
          _ = y*x := by rw [mul_inv_rev,hinv,hinv]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hFsq }
  refine ⟨helem, hFcard, ?_⟩
  intro x hx
  obtain ⟨b,c,rfl⟩ := hdecomp x
  have hn : ((b:H) * α (b:H)) * ((c:H) * α (c:H)) = 1 := by
    rw [map_mul] at hx
    calc
      _ = ((b:H)*(c:H))*(α (b:H)*α (c:H)) := by
        rw [mul_assoc, ← mul_assoc (α (b:H)), hcomm _ (hBm' b) c c.property,
          mul_assoc, ← mul_assoc]
      _ = 1 := hx
  have hbC : (b:H)*α (b:H) ∈ C := by
    rw [eq_inv_of_mul_eq_one_left hn]
    exact C.inv_mem (C.mul_mem c.property (hCm' c))
  have hcB : (c:H)*α (c:H) ∈ B := by
    rw [eq_inv_of_mul_eq_one_right hn]
    exact B.inv_mem (B.mul_mem b.property (hBm' b))
  obtain ⟨y,hy⟩ := hBn b hbC
  obtain ⟨z,hz⟩ := hCn c hcB
  refine ⟨(y:H)*(z:H), ?_⟩
  rw [hy,hz,mul_inv_rev,map_mul]
  have hzy : α (z:H)⁻¹ * α (y:H)⁻¹ = α (y:H)⁻¹ * α (z:H)⁻¹ := by
    exact (hcomm _ (by simpa only [map_inv] using B.inv_mem (hBm' y))
      _ (by simpa only [map_inv] using C.inv_mem (hCm' z))).symm
  rw [hzy]
  rw [mul_assoc, ← mul_assoc (α (y:H)⁻¹),
    hcomm _ (by simpa only [map_inv] using B.inv_mem (hBm' y)) z z.property,
    mul_assoc, ← mul_assoc]

end Subgroup
