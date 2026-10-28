module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.Seed

public import Theory.ElementaryAbelian.Join

/-!
# The original order-twenty-five subgroups are self-centralizing

Let B₅ ≤ E ≤ P with |E| = 25, where P is the source extraspecial five-core.
An involution of C_G(E) would lie in C_G(B₅), whose quaternion Sylow
subgroup has just one involution. Sylow conjugacy carries it to the
original z while preserving P, forcing a conjugate of E into C_P(z) of
order five. Thus C_G(E) has odd order. Its image in C_G(B₅)/P, of order
eight, is trivial. Finally the center of P has order five, so a subgroup
of order25 in P has centralizer exactly itself.

The literal application is E = B₅ C_P(u), the commuting edge constructed
from the original inverter. It has order25 and is elementary abelian.
No normalizer action or faithful linear representation is assumed.

Source: Aschbacher–Smith, discussion before J.4.8 and proof of J.4.10,
printed pp.443–444, using J.3.6.
-/

public section
noncomputable section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem quaternion_unique : ∀ a b : QuaternionGroup 2,
    a^2=1 → a≠1 → b^2=1 → b≠1 → a=b := by decide +kernel

/-- Every involution of the original five-centralizer is conjugate there to z. -/
theorem involution_conjugate_in_G5 (t : G) (ht : t∈G5 B5) (ht2 : orderOf t=2) :
    ∃ g:G5 B5, (g:G)*t*(g:G)⁻¹=c.z := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  let t' : G5 B5 := ⟨t,ht⟩
  have ht'2 : orderOf t'=2 := by rw [← orderOf_coe]; exact ht2
  have hp : IsPGroup 2 (zpowers t') := IsPGroup.of_card (n:=1)
    (by rw [Nat.card_zpowers,ht'2]; rfl)
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (G5 B5) S q.twoSylow
  have htg : g*t'*g⁻¹∈(q.twoSylow : Subgroup (G5 B5)) := by
    have he := congrArg (fun T : Sylow 2 (G5 B5) => (T : Subgroup (G5 B5))) hg
    change (S : Subgroup (G5 B5)).map (MulAut.conj g).toMonoidHom=_ at he
    rw [← he]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hS (mem_zpowers t'))
  have htgQ : (g:G)*t*(g:G)⁻¹∈CQ B5 := by
    rw [← q.twoSylow_image]
    exact mem_map_of_mem (G5 B5).subtype htg
  have hzQ : c.z∈CQ B5 := (q.inf_U.symm ▸ c.z_mem_Z).1
  obtain ⟨e⟩ := q.quaternion
  have h1 : orderOf (e ⟨(g:G)*t*(g:G)⁻¹,htgQ⟩)=2 := by
    rw [e.orderOf_eq,← orderOf_coe]
    exact ((MulAut.conj (g:G)).orderOf_eq t).trans ht2
  have h2 : orderOf (e ⟨c.z,hzQ⟩)=2 := by
    rw [e.orderOf_eq,← orderOf_coe]
    exact SourceCompletion.z_order c
  exact ⟨g,congrArg Subtype.val (e.injective (quaternion_unique _ _ (orderOf_eq_prime_iff.mp h1).1
    (orderOf_eq_prime_iff.mp h1).2 (orderOf_eq_prime_iff.mp h2).1 (orderOf_eq_prime_iff.mp h2).2))⟩

include c in
/-- An original order-twenty-five subgroup has an odd ambient centralizer. -/
theorem centralizer_order_odd {E : Subgroup G} (hBE : B5Image B5≤E)
    (hEP : E≤fiveOddPart B5) (hE : Nat.card E=25) :
    Odd (Nat.card (centralizer (E : Set G))) := by
  by_contra hn
  have hd : 2∣Nat.card (centralizer (E : Set G)) := (Nat.not_odd_iff_even.mp hn).two_dvd
  obtain ⟨t,ht2⟩ := exists_prime_orderOf_dvd_card' 2 hd
  have hCB : centralizer (E : Set G)≤G5 B5 := centralizer_le hBE
  obtain ⟨g,hg⟩ := involution_conjugate_in_G5 c B5 t (hCB t.property)
    (by rw [orderOf_coe]; exact ht2)
  have hnormal := G5_normalizes_fiveOddPart B5 g.property
  have hfixed : E.conjBy (g:G) ≤ fixedFive B5 c.z := by
    rintro x ⟨a,ha,rfl⟩
    refine ⟨(mem_normalizer_iff.mp hnormal a).mp (hEP ha),?_⟩
    change (g:G)*a*(g:G)⁻¹ ∈ centralizer ({c.z} : Set G)
    rw [mem_centralizer_singleton_iff,← hg]
    simpa only [map_mul,MulAut.conj_apply,MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj (g:G)) (t.property a ha)
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  have hf := c.fiveOddPart_inf_centralizer_z d.card_Z B5 q
  change fixedFive B5 c.z=B5Image B5 at hf
  have hc := card_le_of_le hfixed
  change Nat.card (E.map (MulAut.conj (g:G)).toMonoidHom) ≤ Nat.card (fixedFive B5 c.z) at hc
  rw [card_map_of_injective (MulAut.conj (g:G)).injective,hE,hf,B5Image_card d.card_Z B5] at hc
  omega

include c in
/-- The ambient centralizer lies in the same original five-core. -/
theorem centralizer_le_five_core {E : Subgroup G} (hBE : B5Image B5≤E)
    (hEP : E≤fiveOddPart B5) (hE : Nat.card E=25) :
    centralizer (E : Set G)≤fiveOddPart B5 := by
  let C := centralizer (E : Set G)
  let N := pPrimeCore 2 (G5 B5)
  have hCN : C≤G5 B5 := centralizer_le hBE
  let f : C →* (G5 B5) ⧸ N := (QuotientGroup.mk' N).comp (inclusion hCN)
  have hNc : Nat.card N=125 := by
    have h := SourceCompletion.five_oddPart_card c B5
    rw [card_map_of_injective (G5 B5).subtype_injective] at h
    exact h
  have hG5 : Nat.card (G5 B5)=1000 := by
    obtain ⟨q⟩ := c.fiveQuaternionData_source B5
    rw [G5_card c B5 d.card_Z q,SourceCompletion.five_oddPart_card c B5]
  have hQc : Nat.card ((G5 B5) ⧸ N)=8 := by
    have h := card_eq_card_quotient_mul_card_subgroup N
    rw [hNc,hG5] at h
    omega
  have hodd : Odd (Nat.card f.range) :=
    (centralizer_order_odd c B5 hBE hEP hE).of_dvd_nat (Subgroup.card_range_dvd f)
  have hd : Nat.card f.range∣8 := hQc ▸ f.range.card_subgroup_dvd_card
  have hc : Nat.card f.range=1 := by
    have hco := (Nat.coprime_two_left.mpr hodd).symm.pow_right 3
    have hdiv : Nat.card f.range∣1 := hco.dvd_of_dvd_mul_left
      (show Nat.card f.range∣2^3*1 by simpa using hd)
    exact Nat.dvd_one.mp hdiv
  have hbot : f.range=⊥ := card_eq_one.mp hc
  intro x hx
  have he : f ⟨x,hx⟩=1 := mem_bot.mp (hbot ▸ (show f ⟨x,hx⟩∈f.range from ⟨⟨x,hx⟩,rfl⟩))
  have hm : (⟨x,hCN hx⟩ : G5 B5)∈N := (QuotientGroup.eq_one_iff _).mp he
  exact mem_map_of_mem (G5 B5).subtype hm

include c in
/-- Every order-twenty-five subgroup between the original B₅ and P is self-centralizing. -/
theorem centralizer_eq_of_card_twentyfive {E : Subgroup G} (hBE : B5Image B5≤E)
    (hEP : E≤fiveOddPart B5) (hE : Nat.card E=25) :
    centralizer (E : Set G)=E := by
  let C := centralizer (E : Set G)
  let P := fiveOddPart B5
  let : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p:=5) (by simpa using hE)
  have hEC : E≤C := E.le_centralizer
  have hCP : C≤P := centralizer_le_five_core c B5 hBE hEP hE
  have hCne : C≠P := by
    intro he
    have hEB : E≤B5Image B5 := by
      rw [← Section03.five_oddPart_center c B5 (Section03.order_source c)]
      intro e heE
      refine ⟨⟨e,hEP heE⟩,mem_center_iff.mpr ?_,rfl⟩
      intro p
      have hpC : (p:G)∈C := he.symm ▸ p.property
      exact Subtype.ext (hpC e heE).symm
    have hc := card_le_of_le hEB
    rw [hE,B5Image_card d.card_Z B5] at hc
    omega
  have hdiv : Nat.card C∣125 := by
    have h := card_dvd_of_le hCP
    rwa [SourceCompletion.five_oddPart_card c B5] at h
  have hne : Nat.card C≠125 := by
    intro he
    apply hCne
    exact eq_of_le_of_card_ge hCP (by rw [SourceCompletion.five_oddPart_card c B5,he])
  have hn (n:ℕ) (hd:n∣125) (hne:n≠125) : n≤25 := by
    obtain ⟨k,hk,rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp
      (show n∣5^3 from hd)
    interval_cases k <;> norm_num at *
  exact (eq_of_le_of_card_ge hEC (by rw [hE]; exact hn _ hdiv hne)).symm

/-- The commuting source pair B₅ and C_P(u) has join of order twenty-five. -/
theorem base_fixed_card (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    Nat.card (B5Image B5 ⊔ fixedFive B5 u : Subgroup G)=25 := by
  have h5 := (source_three_fives c B5 u hu huz hi).1
  have hn : fixedFive B5 u ≤ normalizer (B5Image B5 : Set G) :=
    (le_centralizer_iff.mp (central_edge B5 u)).trans (Subgroup.centralizer_le_normalizer _)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn
    (disjoint_base_fixed c B5 u hi),B5Image_card d.card_Z B5,h5]

/-- The actual commuting edge in the J.4 hexagon is self-centralizing. -/
theorem centralizer_base_fixed (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    centralizer ((B5Image B5 ⊔ fixedFive B5 u : Subgroup G) : Set G) =
      B5Image B5 ⊔ fixedFive B5 u :=
  centralizer_eq_of_card_twentyfive c B5 le_sup_left
    (sup_le (B5Image_le_fiveOddPart d.card_Z B5) inf_le_left)
    (base_fixed_card c B5 u hu huz hi)

omit [Finite G] in
private theorem elementary_of_card_five (A : Subgroup G) (hA : Nat.card A=5) :
    IsElementaryAbelian 5 A := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro a
  simpa only [hA] using (pow_card_eq_one' (x:=a))

/-- The original self-centralizing order-twenty-five subgroup is an actual five-plane. -/
theorem base_fixed_elementary (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    IsElementaryAbelian 5 (B5Image B5 ⊔ fixedFive B5 u : Subgroup G) := by
  let := elementary_of_card_five (B5Image B5) (B5Image_card d.card_Z B5)
  let := elementary_of_card_five (fixedFive B5 u) (source_three_fives c B5 u hu huz hi).1
  exact IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp (central_edge B5 u))

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
