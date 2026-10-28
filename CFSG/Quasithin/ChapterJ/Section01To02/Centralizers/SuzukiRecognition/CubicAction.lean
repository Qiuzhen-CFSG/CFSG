module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.ModelConsequences
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction.Orbits
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# The actual outer cubic action in J.2.9

The original Singer choice gives the B-orbit on S₀ minus the identity.
The faithful natural Ru1 action shows that no nonidentity member of B
centralizes V: such an element would lie in both B and the two-core S.
Since V lies in L_s and the order of Sz(8) is coprime to three, an inner
B-action on L_s would be trivial. This proves outerness on the literal
residual, with no replacement action or assumed automorphism witness.

Source: Aschbacher–Smith, J.2.3(1),(4) and J.2.9(2), printed pp.433–438
(PDF pp.444–449).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- The original B-invariant Singer choice, without changing any subgroup. -/
def singerChoice : SpecialCore.SingerChoice d.toTypeRuSetup c.sylowThree :=
  ⟨c.B7,c.B7_le,c.B7_card,c.B_normalizes⟩

theorem B_normalizes_S0 : c.B ≤ normalizer (c.S0 : Set G) :=
  c.singerChoice.normalizes_fixedCore d.toTypeRuSetup c.sylowThree

theorem B_orbit_S0 (hB : Nat.card c.B = 3) :
    ∀ t ∈ c.S0, t ≠ 1 → ∃ b ∈ c.B, b*c.s*b⁻¹ = t := by
  intro t ht ht1
  exact c.singerChoice.transitive_fixedCore d.toTypeRuSetup c.sylowThree hB
    c.s t c.s_mem ht c.s_ne_one ht1

theorem B_centralizer_V_trivial (hB : Nat.card c.B = 3)
    {b : G} (hb : b ∈ c.B) (hc : b ∈ centralizer (d.V : Set G)) : b = 1 := by
  have hBL : c.B ≤ d.L := SpecialCore.cubicSubgroup_le_L d.toTypeRuSetup c.sylowThree
  let bL : d.L := ⟨b,hBL hb⟩
  have hq : d.ru1.quotientMap bL = 1 := by
    apply BinaryLinearThree.natural_injective
    rw [map_one]
    apply LinearMap.ext
    intro v
    obtain ⟨x,hx⟩ := d.ru1.natural.onto (Multiplicative.ofAdd v)
    have he := d.ru1.natural.equivariant bL x
    have hfix : (⟨b*(x:G)*b⁻¹, (mem_normalizer_iff.mp (d.ru1.natural.normalized bL.property) x).mp x.property⟩ : d.V) = x := by
      apply Subtype.ext
      change b*(x:G)*b⁻¹ = x
      rw [← hc x x.property, mul_inv_cancel_right]
    change (d.ru1.natural.coordinates _).toAdd = BinaryLinearThree.W (d.ru1.quotientMap bL) _ at he
    rw [hfix,hx] at he
    exact he.symm
  have hbS : b ∈ d.toTypeRuSetup.S := by
    have hk : bL ∈ d.ru1.quotientMap.ker := hq
    rw [d.ru1.quotient_kernel] at hk
    exact hk
  have hd : Disjoint c.B d.toTypeRuSetup.S := disjoint_of_coprime_natCard (by
    rw [hB,d.ru1.card_S]
    decide)
  exact disjoint_def.mp hd hb hbS

theorem B_outer_on_Ls
    (model : c.Ls ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)
    (hB : Nat.card c.B = 3)
    (hBN : c.B ≤ normalizer (c.Ls : Set G))
    (hVL : d.V ≤ c.Ls) :
    ∀ b ∈ c.B, b ≠ 1 →
      ¬ ∃ l ∈ c.Ls, ∀ x ∈ c.Ls, b*x*b⁻¹ = l*x*l⁻¹ := by
  intro b hb hb1
  rintro ⟨l,hl,he⟩
  let n : normalizer (c.Ls : Set G) := ⟨b,hBN hb⟩
  let α : MulAut c.Ls := c.Ls.normalizerMonoidHom n
  have hα : α = MulAut.conj (⟨l,hl⟩ : c.Ls) := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact he x x.property
  have hn3 : n^3 = 1 := by
    apply Subtype.ext
    have hb3 : (⟨b,hb⟩ : c.B)^3 = 1 := hB ▸ pow_card_eq_one'
    exact congrArg (fun z : c.B => (z : G)) hb3
  have hα3 : α^3 = 1 := by
    change (c.Ls.normalizerMonoidHom n)^3 = 1
    rw [← map_pow,hn3,map_one]
  have hαL : α ^ Nat.card c.Ls = 1 := by
    rw [hα, ← map_pow, pow_card_eq_one', map_one]
  have hcard : Nat.card c.Ls = 29120 := by
    rw [Nat.card_congr model.toEquiv, BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card 1 (by decide)]
    norm_num
  have ho : orderOf α = 1 := Nat.eq_one_of_dvd_coprimes
    (show Nat.Coprime 3 (Nat.card c.Ls) by rw [hcard]; decide)
    (orderOf_dvd_of_pow_eq_one hα3) (orderOf_dvd_of_pow_eq_one hαL)
  have ha1 := orderOf_eq_one_iff.mp ho
  apply hb1
  apply c.B_centralizer_V_trivial hB hb
  intro v hv
  have hh := congrArg (fun f : MulAut c.Ls => ((f ⟨v,hVL hv⟩ : c.Ls) : G)) ha1
  change b*v*b⁻¹ = v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
