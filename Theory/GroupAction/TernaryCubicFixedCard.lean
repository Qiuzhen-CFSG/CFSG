module
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.ElementaryAbelian.Basic

/-!
# Fixed subgroup bounds for cubic automorphisms

A cubic automorphism of an elementary ternary group V satisfies
|V| ≤ |C_V(b)|³. The displacement homomorphism has cube zero; its first
and second kernels give the bound by two applications of the kernel/range
cardinality formula. A nonidentity cubic automorphism of any group of
order nine fixes exactly three elements, by orbit counting.

These source-neutral bounds are used on the literal cubic-core quotients
in the exceptional q=3 analysis for Aschbacher–Smith I.4.5, printed p.417.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace MulAut
variable {D : Type*} [Group D] [Finite D]

/-- A nontrivial cubic automorphism of a group of order nine fixes three elements. -/
theorem cubic_fixed_card_of_card_nine (b : MulAut D) (hb : b^3=1) (hne : b≠1)
    (hc : Nat.card D=9) : Nat.card b.fixedSubgroup=3 := by
  let A := zpowers b
  have hp : IsPGroup 3 A := IsPGroup.of_card_dvd_pow (n:=1) (by
    simpa only [A,Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one hb)
  have heq : FixedPoints.subgroup A D=b.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      apply (MulAut.mem_fixedSubgroup b x).mpr
      exact hx ⟨b,mem_zpowers b⟩
    · intro hx
      have hle : A ≤ MulAction.stabilizer (MulAut D) x :=
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup b x).mp hx)
      exact fun y => hle y.property
  have hm := hp.card_modEq_card_fixedPoints D
  change Nat.card D % 3=Nat.card (FixedPoints.subgroup A D) % 3 at hm
  rw [heq,hc] at hm
  have hd : Nat.card b.fixedSubgroup ∣ 9 := hc ▸ b.fixedSubgroup.card_subgroup_dvd_card
  have htop : b.fixedSubgroup≠⊤ := by
    intro he
    apply hne
    ext x
    exact (MulAut.mem_fixedSubgroup b x).mp (he ▸ mem_top x)
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show Nat.card b.fixedSubgroup∣3^2 from hd)
  interval_cases k
  · have hh : Nat.card b.fixedSubgroup=1 := by simpa only [pow_zero] using he
    omega
  · simpa only [pow_one] using he
  · exact (htop ((card_eq_iff_eq_top _).mp (he.trans hc.symm))).elim


variable {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 3 V]

/-- The cubic displacement filtration bounds the whole ternary group by its fixed subgroup. -/
theorem ternary_cubic_fixed_card_bound (b : MulAut V) (hb : b^3=1) :
    Nat.card V ≤ Nat.card b.fixedSubgroup^3 := by
  let : CommGroup V := IsMulCommutative.instCommGroup
  let f : V →* V := b.toMonoidHom * (MonoidHom.id V)⁻¹
  have hf (x : V) : f x=b x*x⁻¹ := rfl
  have h3 (x : V) : x^3=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 3 V) x
  have hsq (x : V) : x⁻¹*x⁻¹=x := by
    apply inv_injective
    simp only [mul_inv_rev,inv_inv]
    apply mul_eq_one_iff_eq_inv.mp
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using h3 x
  have hb3 (x : V) : b (b (b x))=x := DFunLike.congr_fun hb x
  have hff (x : V) : f (f x)=b (b x)*b x*x := by
    simp only [hf,map_mul,map_inv,mul_inv_rev,inv_inv]
    calc
      _ = b (b x)*((b x)⁻¹*(b x)⁻¹)*x := by ac_rfl
      _ = _ := by rw [hsq]
  have hfff (x : V) : f (f (f x))=1 := by
    rw [hf,hff,map_mul,map_mul,hb3]
    have he : x*b (b x)*b x=b (b x)*b x*x := by ac_rfl
    rw [he,mul_inv_cancel]
  have hk : f.ker=b.fixedSubgroup := by
    ext x
    rw [MonoidHom.mem_ker,MulAut.mem_fixedSubgroup,hf,mul_inv_eq_one]
  let K := (f.comp f).ker
  let g : K →* f.ker := {
    toFun x := ⟨f x,x.property⟩
    map_one' := Subtype.ext f.map_one
    map_mul' x y := Subtype.ext (f.map_mul x y) }
  have hkg : Nat.card g.ker≤Nat.card f.ker := by
    let j : g.ker → f.ker := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
    apply Nat.card_le_card_of_injective j
    intro x y h
    exact Subtype.ext (Subtype.ext (show (x.val.val:V)=y.val.val from congrArg (fun w : f.ker => (w:V)) h))
  have hgr : Nat.card g.range≤Nat.card f.ker := g.range.card_le_card_group
  have hK : Nat.card K≤Nat.card f.ker^2 := by
    have hh := g.ker.card_mul_index
    rw [index_ker] at hh
    rw [←hh,pow_two]
    exact Nat.mul_le_mul hkg hgr
  have hfr : f.range≤K := by
    rintro x ⟨y,rfl⟩
    exact hfff y
  have hh := f.ker.card_mul_index
  rw [index_ker] at hh
  calc
    Nat.card V = Nat.card f.ker*Nat.card f.range := hh.symm
    _ ≤ Nat.card f.ker*Nat.card K := Nat.mul_le_mul_left _ (card_le_of_le hfr)
    _ ≤ Nat.card f.ker*Nat.card f.ker^2 := Nat.mul_le_mul_left _ hK
    _ = Nat.card b.fixedSubgroup^3 := by rw [hk]; ring
end MulAut
