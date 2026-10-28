module

public import Theory.AlgebraicGroup.BNPair.SimpleLiftCoverage

/-!
Local positive/negative cell geometry for GLS3 1.11.5 and 2.3.5.
The right factor is `U ∩ n⁻¹ V n`. With `V = U^(w₀)`, this is
`U ∩ U^(w₀w)` in the source's right-conjugation convention.
-/

@[expose] public section
namespace Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent

variable {X : Type*} [Group X]

/-- Right-conjugated inversion factor, with the full normalizer element retained. -/
def rightFactor (U V : Subgroup X) (n : X) : Subgroup X :=
  U ⊓ V.comap (MulAut.conj n).toMonoidHom

/-- If `V = U^(n₀)`, the inversion factor is exactly `U ∩ U^(n₀*n)`.
Here right conjugation means `U^x = x⁻¹ U x`. -/
theorem rightFactor_rightConjugate (U : Subgroup X) (n₀ n : X) :
    rightFactor U (U.comap (MulAut.conj n₀).toMonoidHom) n =
      U ⊓ U.comap (MulAut.conj (n₀ * n)).toMonoidHom := by
  ext x
  change (x ∈ U ∧ n₀ * (n * x * n⁻¹) * n₀⁻¹ ∈ U) ↔
    (x ∈ U ∧ (n₀ * n) * x * (n₀ * n)⁻¹ ∈ U)
  rw [show n₀ * (n * x * n⁻¹) * n₀⁻¹ = (n₀ * n) * x * (n₀ * n)⁻¹ by group]

/-- A normal form contains the entire middle element, including its torus parameter. -/
abbrev NormalForm (U N V : Subgroup X) :=
  {a : X × X × X // a.1 ∈ U ∧ a.2.1 ∈ N ∧ a.2.2 ∈ rightFactor U V a.2.1}

def normalProduct {U N V : Subgroup X} (a : NormalForm U N V) : X :=
  a.val.1 * a.val.2.1 * a.val.2.2

/-- Transport normal-form coordinates along the actual group homomorphism. -/
def NormalForm.map {Y : Type*} [Group Y]
    {U N V : Subgroup X} {U' N' V' : Subgroup Y}
    (f : X →* Y) (hU : ∀ x ∈ U, f x ∈ U')
    (hN : ∀ x ∈ N, f x ∈ N') (hV : ∀ x ∈ V, f x ∈ V')
    (a : NormalForm U N V) : NormalForm U' N' V' := by
  refine ⟨(f a.val.1, f a.val.2.1, f a.val.2.2), hU _ a.property.1,
    hN _ a.property.2.1, hU _ a.property.2.2.1, ?_⟩
  change f a.val.2.1 * f a.val.2.2 * (f a.val.2.1)⁻¹ ∈ V'
  have h := hV _ a.property.2.2.2
  change f (a.val.2.1 * a.val.2.2 * a.val.2.1⁻¹) ∈ V' at h
  simpa only [map_mul, map_inv] using h

@[simp] theorem NormalForm.normalProduct_map {Y : Type*} [Group Y]
    {U N V : Subgroup X} {U' N' V' : Subgroup Y}
    (f : X →* Y) (hU : ∀ x ∈ U, f x ∈ U')
    (hN : ∀ x ∈ N, f x ∈ N') (hV : ∀ x ∈ V, f x ∈ V')
    (a : NormalForm U N V) :
    normalProduct (NormalForm.map f hU hN hV a) = f (normalProduct a) := by
  simp only [NormalForm.map, normalProduct, map_mul]

theorem NormalForm.map_injective {Y : Type*} [Group Y]
    {U N V : Subgroup X} {U' N' V' : Subgroup Y}
    (f : X →* Y) (hf : Function.Injective f) (hU : ∀ x ∈ U, f x ∈ U')
    (hN : ∀ x ∈ N, f x ∈ N') (hV : ∀ x ∈ V, f x ∈ V') :
    Function.Injective (NormalForm.map f hU hN hV) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (hf (congrArg (fun c => c.val.1) h))
    (Prod.ext (hf (congrArg (fun c => c.val.2.1) h))
      (hf (congrArg (fun c => c.val.2.2) h)))

/-- Independent geometric inputs for collecting and separating root cells.
There is no global coverage or BN-pair axiom among these fields. -/
structure RootCellGeometry (B U H N V : Subgroup X) where
  positive_le : U ≤ B
  torus_le_borel : H ≤ B
  torus_le_normalizer : H ≤ N
  borel_factors : ∀ b ∈ B, ∃ u ∈ U, ∃ t ∈ H, b = u * t
  torus_normalizes_positive : H ≤ Subgroup.normalizer (U : Set X)
  torus_normalizes_negative : H ≤ Subgroup.normalizer (V : Set X)
  negative_disjoint_borel : Disjoint V B
  positive_disjoint_torus : Disjoint U H
  separate : ∀ n ∈ N, ∀ m ∈ N, ∀ b ∈ B, ∀ c ∈ B,
    m = b * n * c → m * n⁻¹ ∈ H
  split : ∀ n ∈ N, ∀ q ∈ U,
    ∃ a ∈ U, ∃ v ∈ rightFactor U V n, n * q = a * n * v

namespace RootCellGeometry
variable {B U H N V : Subgroup X} (R : RootCellGeometry B U H N V)
include R

/-- Reverse the Borel factors using the torus action on the positive subgroup. -/
theorem torus_positive_factors (b : X) (hb : b ∈ B) :
    ∃ t ∈ H, ∃ u ∈ U, b = t * u := by
  obtain ⟨u, hu, t, ht, he⟩ := R.borel_factors b hb
  refine ⟨t, ht, t⁻¹ * u * t, ?_, ?_⟩
  · simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      (R.torus_normalizes_positive (H.inv_mem ht)) u).mp hu
  · rw [he]
    group

/-- Cell separation at the identity identifies the Borel--normalizer intersection. -/
theorem borel_inf_normalizer : B ⊓ N = H := by
  apply le_antisymm
  · intro n hn
    have h := R.separate 1 N.one_mem n hn.2 n hn.1 1 B.one_mem (by simp)
    simpa only [inv_one, mul_one] using h
  · exact le_inf R.torus_le_borel R.torus_le_normalizer

/-- Separation proves uniqueness of all three coordinates, including the torus. -/
theorem normalProduct_injective :
    Function.Injective (normalProduct (U := U) (N := N) (V := V)) := by
  rintro ⟨⟨u, n, v⟩, hu, hn, hv⟩ ⟨⟨a, m, z⟩, ha, hm, hz⟩ hprod
  change u * n * v = a * m * z at hprod
  change v ∈ U ∧ n * v * n⁻¹ ∈ V at hv
  change z ∈ U ∧ m * z * m⁻¹ ∈ V at hz
  let t := m * n⁻¹
  have ht : t ∈ H := by
    apply R.separate n hn m hm (a⁻¹ * u)
      (B.mul_mem (B.inv_mem (R.positive_le ha)) (R.positive_le hu))
      (v * z⁻¹) (B.mul_mem (R.positive_le hv.1) (B.inv_mem (R.positive_le hz.1)))
    calc
      m = a⁻¹ * (a * m * z) * z⁻¹ := by group
      _ = a⁻¹ * (u * n * v) * z⁻¹ := by rw [hprod]
      _ = a⁻¹ * u * n * (v * z⁻¹) := by group
  have hnz : n * z * n⁻¹ ∈ V := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (R.torus_normalizes_negative (H.inv_mem ht)) (m * z * m⁻¹)).mp hz.2
    convert h using 1
    dsimp [t]
    group
  have hdiffV : n * (v * z⁻¹) * n⁻¹ ∈ V := by
    have h := V.mul_mem hv.2 (V.inv_mem hnz)
    convert h using 1
    group
  have heq : n * (v * z⁻¹) * n⁻¹ = u⁻¹ * a * t := by
    calc
      n * (v * z⁻¹) * n⁻¹ = u⁻¹ * (u * n * v) * z⁻¹ * n⁻¹ := by group
      _ = u⁻¹ * (a * m * z) * z⁻¹ * n⁻¹ := by rw [hprod]
      _ = u⁻¹ * a * t := by dsimp [t]; group
  have hdiffB : n * (v * z⁻¹) * n⁻¹ ∈ B := by
    rw [heq]
    exact B.mul_mem (B.mul_mem (B.inv_mem (R.positive_le hu))
      (R.positive_le ha)) (R.torus_le_borel ht)
  have hone : n * (v * z⁻¹) * n⁻¹ = 1 :=
    disjoint_iff_inf_le.mp R.negative_disjoint_borel ⟨hdiffV, hdiffB⟩
  have hvz : v = z := by
    have he := congrArg (fun x => n⁻¹ * x * n) hone
    have he' : v * z⁻¹ = 1 := by simpa only [mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using he
    exact mul_inv_eq_one.mp he'
  have hua : u⁻¹ * a = t⁻¹ := (mul_eq_one_iff_eq_inv).mp (heq.symm.trans hone)
  have huone : u⁻¹ * a = 1 :=
    disjoint_iff_inf_le.mp R.positive_disjoint_torus
      ⟨U.mul_mem (U.inv_mem hu) ha, hua ▸ H.inv_mem ht⟩
  have hueq : u = a := inv_mul_eq_one.mp huone
  have hneq : n = m := by
    rw [hueq, hvz] at hprod
    exact mul_left_cancel (mul_right_cancel hprod)
  exact Subtype.ext (Prod.ext hueq (Prod.ext hneq hvz))

/-- Unique root coordinates of a fixed element are individually fixed.
Only forward invariance is needed; fixed points need not preserve generation. -/
theorem fixed_coordinates (σ : X →* X)
    (hU : ∀ x ∈ U, σ x ∈ U) (hN : ∀ x ∈ N, σ x ∈ N)
    (hV : ∀ x ∈ V, σ x ∈ V) (a : NormalForm U N V)
    (hfix : σ (normalProduct a) = normalProduct a) :
    σ a.val.1 = a.val.1 ∧ σ a.val.2.1 = a.val.2.1 ∧
      σ a.val.2.2 = a.val.2.2 := by
  have h := R.normalProduct_injective
    ((NormalForm.normalProduct_map σ hU hN hV a).trans hfix)
  exact ⟨congrArg (fun c => c.val.1) h,
    congrArg (fun c => c.val.2.1) h, congrArg (fun c => c.val.2.2) h⟩

/-- Local unipotent collection refines one Borel double coset to a root normal form. -/
theorem normalForm_of_borel_factors {g b n c : X}
    (hb : b ∈ B) (hn : n ∈ N) (hc : c ∈ B) (he : g = b * n * c) :
    ∃ a : NormalForm U N V, normalProduct a = g := by
  obtain ⟨u, hu, t, ht, rfl⟩ := R.borel_factors b hb
  obtain ⟨v, hv, s, hs, rfl⟩ := R.borel_factors c hc
  let m := t * n * s
  have hm : m ∈ N := N.mul_mem (N.mul_mem (R.torus_le_normalizer ht) hn)
    (R.torus_le_normalizer hs)
  have hq : s⁻¹ * v * s ∈ U := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      (R.torus_normalizes_positive (H.inv_mem hs)) v).mp hv
  obtain ⟨a, ha, z, hz, hsplit⟩ := R.split m hm (s⁻¹ * v * s) hq
  refine ⟨⟨(u * a, m, z), U.mul_mem hu ha, hm, hz⟩, ?_⟩
  change (u * a) * m * z = g
  calc
    (u * a) * m * z = u * (a * m * z) := by group
    _ = u * (m * (s⁻¹ * v * s)) := by rw [hsplit]
    _ = (u * t) * n * (v * s) := by dsimp [m]; group
    _ = g := he.symm

/-- Generation and local simple-lift exchange, followed by root collection,
produce unique normal forms. No global coverage is assumed. -/
theorem existsUnique_normalForm_of_simpleLiftExchange
    (S : Set X)
    (hBN : Subgroup.closure ((B : Set X) ∪ (N : Set X)) = ⊤)
    (hN : N ≤ Subgroup.closure ((B : Set X) ∪ S))
    (hSN : S ⊆ (N : Set X))
    (hsquare : ∀ s ∈ S, s * s ∈ B)
    (hexchange : BruhatGeneration.SimpleLiftExchange B N S) (g : X) :
    ∃! a : NormalForm U N V, normalProduct a = g := by
  obtain ⟨b, n, c, hb, hn, hc, he⟩ :=
    BruhatGeneration.exists_factorization_of_simpleLiftExchange B N S
      hBN hN hSN hsquare hexchange g
  obtain ⟨a, ha⟩ := R.normalForm_of_borel_factors hb hn hc he
  exact ⟨a, ha, fun b hb => R.normalProduct_injective (hb.trans ha.symm)⟩

end RootCellGeometry
end Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent
end
