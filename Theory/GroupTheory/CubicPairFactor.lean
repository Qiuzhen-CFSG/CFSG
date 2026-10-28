module
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating


/-!
# A symmetric factor of a marked cubic-pair quotient

A two-group acting through S₃ × S₃ contains an element which is odd in
its first coordinate and trivial in its second whenever its first action
is nontrivial and its two sign characters differ. The proof uses only the
order-two Sylow subgroups of S₃.

For a homomorphism from an ambient subgroup P with two-group kernel,
mark the order-nine Cartan by A₃ × A₃ and its chosen cubic by 1 × A₃.
The inverse image of S₃ × 1 is normal in P, supplements the chosen cubic
on the Cartan, and has literal two-core quotient S₃. Thus the quotient
calculation constructs an actual subgroup without assuming a complement
splits over the two-core.

Source application: Aschbacher–Smith, original 9.3.1, printed p.732 of
refs/quasithin.pdf, the construction of Dσ T₂ in the mixed amalgam branch.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.CubicPairFactor
local notation "S" => Equiv.Perm (Fin 3)
local notation "C" => alternatingGroup (Fin 3)

private theorem square_of_two_power (s : S) (hs : ∃ n : ℕ, s ^ (2 ^ n) = 1) :
    s ^ 2 = 1 := by
  obtain ⟨n, hn⟩ := hs
  have hd : orderOf s ∣ 6 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      Nat.factorial] using orderOf_dvd_natCard s
  have hc : Nat.Coprime (orderOf s) 3 :=
    ((by decide : Nat.Coprime 2 3).pow_left n).of_dvd_left (orderOf_dvd_of_pow_eq_one hn)
  exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_mul_right.mp hd)

/-- The two characters of a cubic pair separate the field--swap coset.
The first action must be nontrivial, and some two-element has different signs. -/
theorem exists_first_odd_second_one {X : Type*} [Group X]
    (hX : IsPGroup 2 X) (f : X →* (S × S))
    (hfirst : ∃ x, (f x).1 ≠ 1)
    (hdifferent : ∃ x, Equiv.Perm.sign (f x).1 ≠ Equiv.Perm.sign (f x).2) :
    ∃ x, (f x).1 ∉ C ∧ (f x).2 = 1 := by
  have hs (x : X) : (f x).1 ^ 2 = 1 ∧ (f x).2 ^ 2 = 1 := by
    obtain ⟨n,hn⟩ := hX x
    constructor
    · apply square_of_two_power
      exact ⟨n, by simpa only [map_pow, map_one, Prod.pow_fst, Prod.fst_one] using
        (congrArg (fun y => (f y).1) hn)⟩
    · apply square_of_two_power
      exact ⟨n, by simpa only [map_pow, map_one, Prod.pow_snd, Prod.snd_one] using
        (congrArg (fun y => (f y).2) hn)⟩
  have hodd : ∀ s : S, s^2=1 → s ≠ 1 → s ∉ C := by
    intro s hs hn hc
    have ha : ∀ s : S, s^2=1 → s ≠ 1 → s.IsSwap := by
      change ∀ s : S, s^2=1 → s ≠ 1 → ∃ a b : Fin 3, a ≠ b ∧ s = Equiv.swap a b
      decide +kernel
    have hsign := (ha s hs hn).sign_eq
    rw [Equiv.Perm.mem_alternatingGroup,hsign] at hc
    exact (by decide : (-1 : ℤˣ) ≠ 1) hc
  have hdiff : ∀ a b : S, a^2=1 → b^2=1 →
      Equiv.Perm.sign a ≠ Equiv.Perm.sign b → a = 1 ∨ b = 1 := by
    intro a b ha hb hd
    by_contra hn
    have hna : a ≠ 1 := fun h => hn (Or.inl h)
    have hnb : b ≠ 1 := fun h => hn (Or.inr h)
    have ea := (Int.units_eq_one_or (Equiv.Perm.sign a)).resolve_left
      (fun h => hodd a ha hna (Equiv.Perm.mem_alternatingGroup.mpr h))
    have eb := (Int.units_eq_one_or (Equiv.Perm.sign b)).resolve_left
      (fun h => hodd b hb hnb (Equiv.Perm.mem_alternatingGroup.mpr h))
    exact hd (ea.trans eb.symm)
  have heq : ∀ a b : S, a^2=1 → b^2=1 → (a*b)^2=1 →
      a ≠ 1 → b ≠ 1 → a=b := by decide +kernel
  obtain ⟨x,hx⟩ := hfirst
  obtain ⟨y,hy⟩ := hdifferent
  by_cases hx2 : (f x).2 = 1
  · exact ⟨x,hodd _ (hs x).1 hx,hx2⟩
  by_cases hy2 : (f y).2 = 1
  · refine ⟨y,hodd _ (hs y).1 ?_,hy2⟩
    intro hy1
    exact hy (by rw [hy1,hy2])
  have hy1 : (f y).1 = 1 := (hdiff _ _ (hs y).1 (hs y).2 hy).resolve_right hy2
  have he : (f x).2 = (f y).2 := heq _ _ (hs x).2 (hs y).2
    (by simpa only [map_mul, Prod.snd_mul] using (hs (x*y)).2) hx2 hy2
  refine ⟨x*y,?_,?_⟩
  · simpa only [map_mul, Prod.fst_mul, hy1, mul_one] using hodd _ (hs x).1 hx
  · simpa only [map_mul, Prod.snd_mul, he, ←pow_two] using (hs y).2

/-- Lift the first symmetric factor through the original two-kernel.
The resulting subgroup is normal in the entire original overgroup. -/
theorem exists_normal_factor {G : Type*} [Group G] [Finite G]
    (P A B : Subgroup G) (hAP : A ≤ P)
    (q : P →* (S × S)) (hk : IsPGroup 2 q.ker)
    (hA : (A.subgroupOf P).map q = (C).prod C)
    (hB : (B.subgroupOf P).map q = (⊥ : Subgroup S).prod C)
    (t : P) (ht1 : (q t).1 ∉ C) (ht2 : (q t).2 = 1) :
    ∃ U : Subgroup G, U ≤ P ∧ P ≤ normalizer (U : Set G) ∧
      A ≤ B ⊔ U ∧ Nonempty ((U ⧸ pCore 2 U) ≃* S) := by
  let N := ((MonoidHom.snd S S).comp q).ker
  let U := N.map P.subtype
  have hUP : U ≤ P := map_subtype_le N
  let f : U →* S := ((MonoidHom.fst S S).comp q).comp (inclusion hUP)
  have hmem (x : G) : x ∈ U ↔ ∃ hx : x ∈ P, (q ⟨x,hx⟩).2 = 1 := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · rintro ⟨hx,hq⟩
      exact ⟨⟨x,hx⟩,hq,rfl⟩
  have hsurj : Function.Surjective f := by
    have hc : ∀ s ∈ C, s ∈ f.range := by
      intro s hs
      have hp : (s,1) ∈ (A.subgroupOf P).map q := hA ▸ ⟨hs,one_mem C⟩
      obtain ⟨a,ha,he⟩ := hp
      have haU : (a : G) ∈ U := (hmem a).mpr ⟨a.property,congrArg Prod.snd he⟩
      exact ⟨⟨a,haU⟩,congrArg Prod.fst he⟩
    have htU : (t : G) ∈ U := (hmem t).mpr ⟨t.property,ht2⟩
    have ht : (q t).1 ∈ f.range := ⟨⟨t,htU⟩,rfl⟩
    have ho : Equiv.Perm.sign (q t).1 = -1 :=
      (Int.units_eq_one_or _).resolve_left (fun h => ht1 (Equiv.Perm.mem_alternatingGroup.mpr h))
    intro s
    change s ∈ f.range
    by_cases hs : s ∈ C
    · exact hc s hs
    · have hsign : Equiv.Perm.sign s = -1 :=
        (Int.units_eq_one_or _).resolve_left (fun h => hs (Equiv.Perm.mem_alternatingGroup.mpr h))
      have hm : s * (q t).1⁻¹ ∈ C := by
        rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_inv,hsign,ho]
        decide
      simpa only [inv_mul_cancel_right] using f.range.mul_mem (hc _ hm) ht
  have hfker : IsPGroup 2 f.ker := by
    let j : f.ker →* q.ker :=
      ((inclusion hUP).comp f.ker.subtype).codRestrict q.ker (by
        intro x
        apply Prod.ext
        · exact x.property
        · exact (hmem x.val).mp x.val.property |>.choose_spec)
    apply hk.of_injective j
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : q.ker => (z.val : G)) he
  have hkernel := ker_eq_twoCore_of_surjective_perm_three f hsurj hfker
  refine ⟨U,hUP,?_,?_,⟨(QuotientGroup.quotientMulEquivOfEq hkernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩⟩
  · intro p hp
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      obtain ⟨hxP,hqx⟩ := (hmem x).mp hx
      apply (hmem _).mpr
      refine ⟨P.mul_mem (P.mul_mem hp hxP) (P.inv_mem hp),?_⟩
      change (q (⟨p,hp⟩ * ⟨x,hxP⟩ * ⟨p,hp⟩⁻¹)).2 = 1
      simp only [map_mul,map_inv,Prod.snd_mul,Prod.snd_inv,hqx,mul_one,mul_inv_cancel]
    · intro hx
      obtain ⟨hxP,hqx⟩ := (hmem _).mp hx
      have hxp : x ∈ P := by
        have hh := P.mul_mem (P.mul_mem (P.inv_mem hp) hxP) hp
        simpa only [inv_mul_cancel_left,mul_assoc,inv_mul_cancel,mul_one] using hh
      apply (hmem x).mpr
      refine ⟨hxp,?_⟩
      change (q (⟨p,hp⟩ * ⟨x,hxp⟩ * ⟨p,hp⟩⁻¹)).2 = 1 at hqx
      simpa only [map_mul,map_inv,Prod.snd_mul,Prod.snd_inv,
        mul_inv_eq_one, mul_eq_left] using hqx
  · intro a ha
    let aP : P := ⟨a,hAP ha⟩
    have ham : q aP ∈ (C).prod C := hA ▸ mem_map_of_mem q ha
    have hbm : (1,(q aP).2) ∈ (B.subgroupOf P).map q := hB ▸ ⟨rfl,ham.2⟩
    obtain ⟨b,hb,he⟩ := hbm
    have hu : a * (b : G)⁻¹ ∈ U := by
      apply (hmem _).mpr
      refine ⟨P.mul_mem aP.property (P.inv_mem b.property),?_⟩
      change (q (aP * b⁻¹)).2 = 1
      simp only [map_mul,map_inv,Prod.snd_mul,Prod.snd_inv,he,mul_inv_cancel]
    have hh := (B ⊔ U).mul_mem ((show U ≤ B ⊔ U from le_sup_right) hu)
      ((show B ≤ B ⊔ U from le_sup_left) hb)
    simpa only [Subgroup.coe_subtype, inv_mul_cancel_right] using hh
end Theory.GroupTheory.CubicPairFactor
