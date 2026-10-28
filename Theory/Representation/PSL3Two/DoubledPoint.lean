module
public import Theory.Representation.PSL3Two.DoubledCubic
public import Theory.Representation.PSL3Two.OrbitStabilizers

/-!
# Point stabilizers in the doubled natural binary three-space

A faithful cubic fixes exactly two vectors on the natural SL₃(2) module.
Its two fixed coordinates in the doubled module are therefore zero or equal.
Every nonzero doubled vector fixed by that cubic has an actual S₄ stabilizer.
The conjugation transport constructs a surjection from the literal component
point centralizer with kernel precisely its intersection with O₂(K).

The consumer is the original doubled-row chief-factor exclusion in
Chapter13/Section04/FixedCoreSource/Nonsolvable/ComponentDoubled. It uses
this S₄ map to construct the A₄ quotient of the reciprocal residual; both
the marking and the two-core projection are retained.

Source: Aschbacher–Smith, 13.4.10(4), printed p.909.
-/

public noncomputable section
open Subgroup
namespace BinaryLinearThree

private theorem nonzero_eq_of_card_two {F : Type*} [AddGroup F] [Finite F]
    (hc : Nat.card F = 2) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
  classical
  let f : Bool → F := fun b => cond b x 0
  have hi : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp_all [f]
  obtain ⟨b,hb⟩ := (hi.bijective_of_nat_card_le (by simp [hc])).2 y
  cases b
  · exact (hy hb.symm).elim
  · exact hb

/-- A nonzero vector in the doubled natural module fixed by a faithful cubic
has the same stabilizer as a nonzero vector in one natural summand. -/
theorem doubled_cubic_fixed_stabilizer
    {A : Type*} [_root_.Group A] [Finite A] (hA : Nat.card A = 3)
    (q : A →* BinaryLinearThree.Group) (hq : Function.Injective q)
    (v : Vector × Vector) (hv : v ≠ 0)
    (hfix : ∀ a : A, (Representation.prod W W) (q a) v = v) :
    Nonempty ((OrbitStabilizers.natural v.1 ⊓ OrbitStabilizers.natural v.2 :
      Subgroup BinaryLinearThree.Group) ≃* Equiv.Perm (Fin 4)) := by
  let ρ : Representation (ZMod 2) A Vector := W.comp q
  have hc := Representation.BinaryFixedPoints.fixedIndex_mul_card ρ
  rw [natural_cubic_fixedIndex hA q hq] at hc
  have hsize : Nat.card Vector = 8 := by
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp
  rw [hsize] at hc
  have hcard : Nat.card ρ.invariants = 2 := by omega
  have h1 : v.1 ∈ ρ.invariants := fun a => congrArg Prod.fst (hfix a)
  have h2 : v.2 ∈ ρ.invariants := fun a => congrArg Prod.snd (hfix a)
  have hz : OrbitStabilizers.natural (0 : Vector) = ⊤ := by
    ext g
    simp only [OrbitStabilizers.mem_natural, map_zero, mem_top]
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := fun hh => hv (Prod.ext hv1 hh)
    rw [hv1,hz,top_inf_eq]
    exact ⟨OrbitStabilizers.naturalEquivSymmetric v.2 hv2⟩
  by_cases hv2 : v.2 = 0
  · rw [hv2,hz,inf_top_eq]
    exact ⟨OrbitStabilizers.naturalEquivSymmetric v.1 hv1⟩
  have he : v.1 = v.2 := congrArg Subtype.val
    (nonzero_eq_of_card_two hcard (x := ⟨v.1,h1⟩) (y := ⟨v.2,h2⟩)
      (fun hh => hv1 (congrArg Subtype.val hh)) (fun hh => hv2 (congrArg Subtype.val hh)))
  rw [he,inf_idem]
  exact ⟨OrbitStabilizers.naturalEquivSymmetric v.2 hv2⟩
/-- The literal centralizer of a nonzero point in a doubled natural module
maps onto S₄ with exactly the component two-core as kernel. -/
theorem doubled_point_centralizer_symmetricFour
    {G : Type*} [_root_.Group G] [Finite G]
    (K U A : Subgroup G) (hKU : K ≤ normalizer (U : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : U ≃* Multiplicative (Vector × Vector))
    (he : letI := conjMulDistribMulActionOfLeNormalizer K U hKU
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod W W) (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)
    (w : U) (hw : w ≠ 1) (hA : Nat.card A = 3)
    (hAK : A ≤ K) (hAw : A ≤ centralizer ({w.val} : Set G)) :
    ∃ f : (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = (K.pCoreIn 2).subgroupOf
        (K ⊓ centralizer ({w.val} : Set G)) := by
  let qK := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let q := qK.comp (inclusion hAK)
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_of_card_eq
    have hp2 : IsPGroup 2 q.ker := by
      have hk : q.ker = (pCore 2 K).comap (inclusion hAK) := by
        ext x
        change eK (QuotientGroup.mk' (pCore 2 K) (inclusion hAK x)) = 1 ↔ _
        rw [eK.map_eq_one_iff]
        exact QuotientGroup.eq_one_iff _
      rw [hk]
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
    have hp3 : IsPGroup 3 q.ker :=
      (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hA)).to_subgroup q.ker
    have hc := (IsPGroup.coprime_card_of_ne 2 3 (by decide) q.ker q.ker hp2 hp3).gcd_eq_one
    simpa only [Nat.gcd_self] using hc
  let v := (e w).toAdd
  let P := OrbitStabilizers.natural v.1 ⊓ OrbitStabilizers.natural v.2
  let := conjMulDistribMulActionOfLeNormalizer K U hKU
  have hmem (k : K) : qK k ∈ P ↔ k.val ∈ centralizer ({w.val} : Set G) := by
    change (qK k ∈ OrbitStabilizers.natural v.1 ∧ qK k ∈ OrbitStabilizers.natural v.2) ↔ _
    rw [OrbitStabilizers.mem_natural,OrbitStabilizers.mem_natural]
    have hp : (Representation.prod W W) (qK k) v = v ↔
        W (qK k) v.1 = v.1 ∧ W (qK k) v.2 = v.2 := Prod.ext_iff
    rw [←hp]
    change (Representation.prod W W) (eK (QuotientGroup.mk' (pCore 2 K) k))
      (e w).toAdd = (e w).toAdd ↔ _
    rw [←he k w,Multiplicative.toAdd.injective.eq_iff,e.injective.eq_iff,Subtype.ext_iff]
    change k.val * w.val * k.val⁻¹ = w.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  have hv : v ≠ 0 := by
    intro hh
    apply hw
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hh
  have hfix (a : A) : (Representation.prod W W) (q a) v = v := by
    have hh := (hmem (inclusion hAK a)).mpr (hAw a.property)
    exact Prod.ext (OrbitStabilizers.mem_natural _ _ |>.mp hh.1)
      (OrbitStabilizers.mem_natural _ _ |>.mp hh.2)
  obtain ⟨eP⟩ := doubled_cubic_fixed_stabilizer hA q hq v hv hfix
  let C := K ⊓ centralizer ({w.val} : Set G)
  let p : C →* P := (qK.comp (inclusion inf_le_left)).codRestrict _
    (fun c => (hmem (inclusion inf_le_left c)).mpr c.property.2)
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨k,hk⟩ := (eK.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K))) x.val
    have hk' : qK k = x.val := hk
    have hkc : k.val ∈ centralizer ({w.val} : Set G) :=
      (hmem k).mp (hk'.symm ▸ x.property)
    exact ⟨⟨k.val,k.property,hkc⟩,Subtype.ext hk⟩
  refine ⟨eP.toMonoidHom.comp p,eP.surjective.comp hp,?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ eP.injective]
  ext c
  change p c = 1 ↔ c.val ∈ K.pCoreIn 2
  rw [Subtype.ext_iff]
  change eK (QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left c)) = 1 ↔ _
  rw [eK.map_eq_one_iff]
  exact (QuotientGroup.eq_one_iff (inclusion inf_le_left c)).trans
    (mem_map_iff_mem K.subtype_injective).symm

end BinaryLinearThree
