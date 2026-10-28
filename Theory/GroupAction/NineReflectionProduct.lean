module
public import Theory.GroupAction.NineInvolutionLines
public import Theory.GroupAction.KleinFourFactorization
/-!
# Products of two reflections on an elementary ternary plane

A nonidentity involution other than inversion fixes a line of order three.
For two commuting such reflections with nontrivial product, Brauer–Wielandt
makes the product fixed-point-free: its fixed order is the square of the
common fixed order, and order nine would make the product trivial.
In an abelian group, an involution with trivial fixed subgroup inverts every
point. This retains the original automorphisms and needs no coordinates.

Source: Aschbacher, Sporadic Groups,45.3(5) and45.7, pp.243–245.
-/
@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace MulAut
variable {E:Type*} [Group E] [Finite E] [IsMulCommutative E]
theorem reflection_product_inverts_of_card_nine (hE:Nat.card E=9)
    (a b:MulAut E) (ha:Function.Involutive a) (hb:Function.Involutive b)
    (hc:Commute a b) (haf:Nat.card a.fixedSubgroup=3) (hbf:Nat.card b.fixedSubgroup=3)
    (hne:a*b≠1) : ∀x:E,(a*b) x=x⁻¹ := by
  have hodd:Odd (Nat.card E) := by rw [hE]; decide
  have hh:=Theory.GroupAction.brauerWielandt_fixedSubgroup_card hodd a b ha hb hc
  rw [hE,haf,hbf] at hh
  have hd:Nat.card (a.fixedSubgroup⊓b.fixedSubgroup:Subgroup E)∣3 := by
    simpa only [haf] using card_dvd_of_le (show a.fixedSubgroup⊓b.fixedSubgroup≤a.fixedSubgroup from inf_le_left)
  have hf:Nat.card (a*b).fixedSubgroup=1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hd | hd
    · rw [hd] at hh; omega
    · rw [hd] at hh
      have htop:(a*b).fixedSubgroup=⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hE]; omega)
      apply False.elim
      apply hne
      ext x
      exact (MulAut.mem_fixedSubgroup _ _).mp (htop ▸ mem_top x)
  have hab:Function.Involutive (a*b) := by
    intro x
    change a (b (a (b x)))=x
    have he:b (a (b x))=a (b (b x)) := (DFunLike.congr_fun hc.eq (b x)).symm
    rw [he,hb,ha]
  intro x
  have hx:x*(a*b) x∈(a*b).fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup,map_mul,hab]
    exact mul_comm _ _
  have hh:x*(a*b) x=1 := by
    have ht:(a*b).fixedSubgroup=⊥ := Subgroup.card_eq_one.mp hf
    exact mem_bot.mp (ht ▸ hx)
  exact eq_inv_of_mul_eq_one_right hh

end MulAut
namespace MulAut
variable {E:Type*} [Group E] [Finite E]
theorem fixed_card_three_of_nonscalar_involution [IsElementaryAbelian 3 E]
    (hE:Nat.card E=9) (a:MulAut E) (ha:a^2=1) (hne:a≠1)
    (hninv:¬∀x:E,a x=x⁻¹) : Nat.card a.fixedSubgroup=3 := by
  have hnt:¬∀x:E,a x=x := by intro hh; exact hne (MulEquiv.ext hh)
  obtain ⟨hf,_,_⟩:=involution_fixed_commutator_card_three a ha hE hnt hninv
  have he:FixedPoints.subgroup (zpowers a) E=a.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      rw [mem_fixedSubgroup]
      exact hx ⟨a,mem_zpowers a⟩
    · intro hx
      have hl:zpowers a≤MulAction.stabilizer (MulAut E) x := zpowers_le.mpr
        ((mem_fixedSubgroup a x).mp hx)
      exact fun b=>hl b.property
  rwa [he] at hf
end MulAut
