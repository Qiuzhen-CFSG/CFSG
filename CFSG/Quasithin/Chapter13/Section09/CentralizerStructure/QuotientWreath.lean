module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Solvability
public import CFSG.Quasithin.Chapter13.Section09.Elementary
/-!
# The actual wreath quotient of the marked centralizer

Normality of Q comes from the preceding reduced-closure argument. The native
self-centralizer calculation in the Sylow central quotient then makes Q
self-centralizing in C_G(z). Its intrinsic square action induces a faithful
map C_G(z)/Q → S₃ wr C₂, retaining the action of every original representative.
The Sylow quotient has order four; strict growth over the original Sylow
therefore leaves exactly quotient orders 12 and 36.

Source: Aschbacher–Smith 13.9.8, printed p.972.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} {m : PairData d}
namespace CoreData
variable (q : CoreData m)

def centralProductInC : QuaternionCentralProductData (q.Q.subgroupOf m.C) :=
  q.factors.map (subgroupOfEquivOfLe q.le_C).symm

theorem centralizer_le_of_tilde_self_centralizing (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde))
    (hself : m.tilde d.T ⊓ centralizer (m.tilde q.Q : Set m.Tilde) ≤ m.tilde q.Q) :
    centralizer (q.Q.subgroupOf m.C : Set m.C) ≤ q.Q.subgroupOf m.C := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  have hTC := (q.centralizer_isPGroup hE).le_sylow_of_normal (d.T.subtype m.z_central)
  let π := QuotientGroup.mk' (m.Z.subgroupOf m.C)
  have he : (m.tilde q.Q).comap π = q.Q.subgroupOf m.C := by
    apply comap_map_eq_self
    rw [QuotientGroup.ker_mk']
    exact comap_mono q.Z_le
  intro x hx
  rw [← he]
  apply hself
  constructor
  · exact mem_map_of_mem π (hTC hx)
  · intro y hy
    obtain ⟨a,ha,rfl⟩ := hy
    exact (π.map_mul a x).symm.trans ((congrArg π (hx a ha)).trans (π.map_mul x a))

theorem exists_quotient_wreath_embedding (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde))
    (hself : m.tilde d.T ⊓ centralizer (m.tilde q.Q : Set m.Tilde) ≤ m.tilde q.Q) :
    letI : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
    ∃ f : (m.C ⧸ q.Q.subgroupOf m.C) →* BinaryFourPlus.Wreath,
      Function.Injective f ∧ ∀ x : m.C,
        f (QuotientGroup.mk' (q.Q.subgroupOf m.C) x) =
          q.centralProductInC.quotientWreathAction (MulAut.conjNormal x) := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  let N := q.Q.subgroupOf m.C
  have hc : centralizer (N : Set m.C) ≤ N :=
    q.centralizer_le_of_tilde_self_centralizing h hE hfix hself
  have hi : Function.Injective (MulAut.outerAction N) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    change (QuotientGroup.map N (MulAut.innerSubgroup N) MulAut.conjNormal _).ker = ⊥
    rw [QuotientGroup.ker_map,MulAut.conjNormal_comap_innerSubgroup,
      sup_eq_left.mpr hc,QuotientGroup.map_mk'_self]
  refine ⟨q.centralProductInC.outerWreathEmbedding.comp (MulAut.outerAction N),
    q.centralProductInC.outerWreathEmbedding_injective.comp hi,?_⟩
  intro x
  exact q.centralProductInC.outerWreathEmbedding_mk (MulAut.conjNormal x)


theorem exists_quotient_sylow_four (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde)) :
    letI : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
    ∃ S : Sylow 2 (m.C ⧸ q.Q.subgroupOf m.C), Nat.card S = 4 := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  let N := q.Q.subgroupOf m.C
  let π := QuotientGroup.mk' N
  let P := d.T.subtype m.z_central
  let S := P.mapSurjective (QuotientGroup.mk'_surjective N)
  refine ⟨S,?_⟩
  have hNP : N ≤ P := comap_mono q.le_T
  have hNcard : Nat.card N = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe q.le_C).toEquiv).trans q.card
  have hPcard : Nat.card P = 128 :=
    (Nat.card_congr (subgroupOfEquivOfLe m.z_central).toEquiv).trans d.card_sylow
  have hh := (N.subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hNP).toEquiv,hNcard,hPcard] at hh
  change 32 * N.relIndex P = 128 at hh
  have hk : π.ker = N := QuotientGroup.ker_mk' N
  rw [← hk,relIndex_ker] at hh
  change Nat.card (P.toSubgroup.map π) = 4
  omega

theorem quotient_card_twelve_or_thirty_six (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde))
    (hself : m.tilde d.T ⊓ centralizer (m.tilde q.Q : Set m.Tilde) ≤ m.tilde q.Q)
    (hgrowth : (d.T : Subgroup G) < m.C) :
    letI : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
    Nat.card (m.C ⧸ q.Q.subgroupOf m.C) = 12 ∨
      Nat.card (m.C ⧸ q.Q.subgroupOf m.C) = 36 := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  let N := q.Q.subgroupOf m.C
  obtain ⟨f,hf,_⟩ := q.exists_quotient_wreath_embedding h hE hfix hself
  have hcW : Nat.card BinaryFourPlus.Wreath = 72 := by
    rw [RegularWreathProduct.card]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial,BinaryFourPlus.C2]
  have hdiv : Nat.card (m.C ⧸ N) ∣ 72 :=
    hcW ▸ card_dvd_of_injective f hf
  obtain ⟨S,hS⟩ := q.exists_quotient_sylow_four h hE hfix
  have hfour : 4 ∣ Nat.card (m.C ⧸ N) := hS ▸ S.toSubgroup.card_subgroup_dvd_card
  have hnot8 : ¬ 8 ∣ Nat.card (m.C ⧸ N) := by
    intro hh
    have hh8 := S.pow_dvd_card_of_pow_dvd_card (n := 3) hh
    rw [hS] at hh8
    norm_num at hh8
  have hnot4 : Nat.card (m.C ⧸ N) ≠ 4 := by
    intro hc
    have hNcard : Nat.card N = 32 :=
      (Nat.card_congr (subgroupOfEquivOfLe q.le_C).toEquiv).trans q.card
    have hC := card_eq_card_quotient_mul_card_subgroup N
    rw [hc,hNcard] at hC
    have he : (d.T : Subgroup G) = m.C :=
      eq_of_le_of_card_ge m.z_central (by rw [hC,d.card_sylow])
    exact hgrowth.ne he
  have hm := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
  have hd : (72 : ℕ).divisors = {1,2,3,4,6,8,9,12,18,24,36,72} := by decide
  rw [hd] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with h1 | h2 | h3 | h4 | h6 | h8 | h9 | h12 | h18 | h24 | h36 | h72
  all_goals first | exact Or.inl h12 | exact Or.inr h36 |
    omega

end CoreData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
