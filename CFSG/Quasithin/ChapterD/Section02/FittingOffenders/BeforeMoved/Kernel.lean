module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalTransport

/-!
# Normal closures acting on two or three cubic factors

Conjugation permutes the literal factors. On a two-element family its square
fixes each factor; when the actor fixes three factors, its normal closure
fixes them too. An automorphism of a group of order three has square one.
Thus fourth powers in the actor's normal closure centralize the whole core.

The consumer is the pre-moved reduction in Aschbacher–Smith 15.1.2, p.1084.
No faithfulness or ratio premise is needed for this group-theoretic step.
-/

public section
namespace CFSG.Quasithin.ChapterD.BeforeMoved
open Subgroup Representation.BinaryOffender FittingConfigurations
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem normalized_three_square (Z : Subgroup G) (hZ : Nat.card Z = 3)
    {g : G} (hg : g ∈ normalizer (Z : Set G)) : g ^ 2 ∈ centralizer (Z : Set G) := by
  let : IsCyclic Z := isCyclic_of_prime_card hZ
  have hc : Nat.card (MulAut Z) = 2 := by
    rw [IsCyclic.card_mulAut,hZ,Nat.totient_prime Nat.prime_three]
  let a := Z.normalizerMonoidHom ⟨g,hg⟩
  have he : a ^ 2 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := a))
  intro z hz
  have hh := congrArg (fun k : MulAut Z => (k ⟨z,hz⟩ : G)) he
  change g * (g * z * g⁻¹) * g⁻¹ = z at hh
  have hmul := congrArg (fun x : G => x * g ^ 2) hh
  simpa only [pow_two,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hmul.symm

omit [Finite G] in
private theorem two_factors_square_normalizes (F : Fin 2 → Subgroup G)
    (hperm : ∀ g : G, ∀ i, ∃ j, (F i).conjBy g = F j) (g : G) (i : Fin 2) :
    g ^ 2 ∈ normalizer (F i : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  have h0 := hperm g 0
  have h1 := hperm g 1
  obtain ⟨j,hj⟩ := h0
  obtain ⟨k,hk⟩ := h1
  have hinj : Function.Injective (fun H : Subgroup G => H.conjBy g) := by
    intro H K he
    have hh := congrArg (fun L : Subgroup G => L.conjBy g⁻¹) he
    simpa only [conjBy_inv] using hh
  have hcase (i : Fin 2) : i = 0 ∨ i = 1 := by omega
  rcases hcase j with rfl | rfl <;> rcases hcase k with rfl | rfl <;>
    rcases hcase i with rfl | rfl
  all_goals change (F _).conjBy (g ^ 2) = F _
  all_goals rw [pow_two,conjBy_mul]
  · rw [hj,hj]
  · rw [hk,hj]; exact hinj (hj.trans hk.symm)
  · rw [hj,hj]
  · rw [hk,hk]
  · rw [hj,hk]
  · rw [hk,hj]
  · rw [hj,hk]; exact (hinj (hj.trans hk.symm)).symm
  · rw [hk,hk]

omit [Finite G] in
private theorem family_normalizers_normal {ι : Type*} (F : ι → Subgroup G)
    (hperm : ∀ g : G, ∀ i, ∃ j, (F i).conjBy g = F j) :
    (⨅ i, normalizer (F i : Set G)).Normal := by
  constructor
  intro n hn g
  simp only [Subgroup.mem_iInf] at hn ⊢
  intro i
  obtain ⟨j,hj⟩ := hperm g⁻¹ i
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (F i).conjBy (g*n*g⁻¹) = F i
  have hnj : (F j).conjBy n = F j := mem_normalizer_iff_map_conj_eq.mp (hn j)
  rw [conjBy_mul,conjBy_mul,hj,hnj,← hj,conjBy_inv']

omit [Finite G] in
private theorem factors_le {P : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) (i : Fin s) : d.ambient i ≤ P :=
  map_subtype_le (d.factor i)

omit [Finite G] in
private theorem factors_generate {P : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) : (⨆ i, d.ambient i) = P := by
  classical
  apply le_antisymm (iSup_le (factors_le ρ d))
  intro p hp
  obtain ⟨x,hx⟩ := d.multiply_bijective.2 (⟨p,hp⟩ : P)
  have hm : (List.ofFn fun i => ((x i : P) : G)).prod ∈ ⨆ i, d.ambient i := by
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hy
    exact (le_iSup (fun i => d.ambient i) i) (mem_map_of_mem P.subtype (x i).property)
  have he : (List.ofFn fun i => ((x i : P) : G)).prod = p := by
    have hh := congrArg (fun z : P => (z : G)) hx
    change P.subtype (List.ofFn fun i => (x i : P)).prod = p at hh
    rw [map_list_prod,List.map_ofFn] at hh
    exact hh
  exact he ▸ hm

/-- Two or three canonical planes control each old actor's normal closure
modulo the centralizer of the original core. No minimum-ratio premise on
this representation is used. -/
theorem normalClosure_fourth_centralizes {P A : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) (hs : s = 2 ∨ s = 3)
    (hperm : ∀ g : G, ∀ i, ∃ j, (d.ambient i).conjBy g = d.ambient j)
    (hthree : s = 3 → ∀ i, A ≤ normalizer (d.ambient i : Set G))
    {n : G} (hn : n ∈ normalClosure (A : Set G)) : n ^ 4 ∈ centralizer (P : Set G) := by
  have hnormal (i : Fin s) : n ^ 2 ∈ normalizer (d.ambient i : Set G) := by
    rcases hs with rfl | hs
    · exact two_factors_square_normalizes d.ambient hperm n i
    · let N := ⨅ i, normalizer (d.ambient i : Set G)
      let : N.Normal := family_normalizers_normal d.ambient hperm
      have hAN : A ≤ N := le_iInf (hthree hs)
      have hN : normalClosure (A : Set G) ≤ N := normalClosure_le_normal hAN
      exact (normalizer (d.ambient i : Set G)).pow_mem
        ((iInf_le (fun i => normalizer (d.ambient i : Set G)) i) (hN hn)) 2
  have hc (i : Fin s) : n ^ 4 ∈ centralizer (d.ambient i : Set G) := by
    have hcard : Nat.card (d.ambient i) = 3 :=
      (card_map_of_injective P.subtype_injective).trans (d.card_factor i)
    simpa only [← pow_mul] using normalized_three_square (d.ambient i) hcard (hnormal i)
  have hle : P ≤ centralizer ({n ^ 4} : Set G) := by
    rw [← factors_generate ρ d]
    apply iSup_le
    intro i x hx
    exact mem_centralizer_singleton_iff.mpr (hc i x hx)
  intro p hp
  exact mem_centralizer_singleton_iff.mp (hle hp)

end CFSG.Quasithin.ChapterD.BeforeMoved
