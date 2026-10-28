module
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.FullAxis
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupTheory.ElementaryConjugatePrimePair
public import Theory.GroupTheory.OddElementLift

/-!
# Hyperplane TI pairs from an odd action in a quotient

Suppose a quotient kernel normalizes an elementary TI subgroup V. A nontrivial
odd quotient element inverted by one member of V and fixed or inverted by every
member gives a conjugate V^g with |V : N_V(V^g)| = 2. The fixing subgroup lifts
into N_V(V^g), because the kernel normalizes both conjugates. If the normalizer
were full, the TI-pair theorem would make the pair elementary, contradicting
the odd element in its quotient image.

Coprime action constructs the required cyclic line inside a normalized odd-prime
subgroup of the quotient. Its odd-order lift gives a literal conjugate pair
upstairs. No invariant odd subgroup upstairs or odd-dihedral recognition is
assumed. The index is finally translated to a binary hyperplane.
Source: Aschbacher–Smith, construction before 12.2.20, printed p.802,
and the elementary part of I.6.2, printed pp.424–425.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G K : Type*} [Group G] [Finite G] [Group K]

theorem pair_normalizer_index_two_of_quotient_inverted_line
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hTI : IsTISubgroup V)
    (q : G →* K) (hk : q.ker ≤ normalizer (V : Set G))
    (g v : G) (hv : v ∈ V) (ho : Odd (orderOf (q g))) (hg : q g ≠ 1)
    (hinv : q v * q g * (q v)⁻¹ = (q g)⁻¹)
    (hsign : ∀ w ∈ V, q w * q g * (q w)⁻¹ = q g ∨
      q w * q g * (q w)⁻¹ = (q g)⁻¹) :
    (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V = 2 := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hqA : A.map q = (V.map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp
  have hgen : (V ⊔ A).map q = zpowers (q g) ⊔ V.map q := by
    rw [Subgroup.map_sup, hqA]
    exact conjugate_join_eq_cyclic_sup (V.map q) (q g) (q v)
      (mem_map_of_mem q hv) ho hinv
  have hnc : ¬ V ≤ centralizer (A : Set G) := by
    intro hc
    let : IsElementaryAbelian 2 (V ⊔ A : Subgroup G) :=
      IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hc)
    let : IsElementaryAbelian 2 ((V ⊔ A).map q) := IsElementaryAbelian.map _
    have hm : q g ∈ (V ⊔ A).map q := hgen.symm ▸ mem_sup_left (mem_zpowers _)
    have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2) (q g) hm
    exact hg (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes ho.coprime_two_right
      dvd_rfl (orderOf_dvd_of_pow_eq_one hp)))
  have hneq : A ≠ V := by
    intro he
    apply hnc
    rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hd := ((hTI.eq_or_disjoint_conjugate g).resolve_left hneq).symm
  have hproper : ¬ V ≤ normalizer (A : Set G) := by
    intro hn
    exact hnc (ti_pair_commute_of_full_normalizer V A hd hTI (hTI.map_equiv _)
      (card_map_of_injective (MulAut.conj g).injective).symm (inf_eq_left.mpr hn))
  have hkA : q.ker ≤ normalizer (A : Set G) := by
    have he : q.ker.map (MulAut.conj g).toMonoidHom = q.ker :=
      mem_normalizer_iff_map_conj_eq.mp (q.ker.normalizer_eq_top ▸ mem_top g)
    rw [← he]
    exact (map_mono hk).trans (V.le_normalizer_map (MulAut.conj g).toMonoidHom)
  have hfix (w : G) (hw : w ∈ V) (hc : q w * q g * (q w)⁻¹ = q g) :
      w ∈ normalizer (A : Set G) := by
    have hc' : q g * q w * (q g)⁻¹ = q w := by
      apply mul_inv_eq_iff_eq_mul.mpr
      exact (mul_inv_eq_iff_eq_mul.mp hc).symm
    have ha : g * w * g⁻¹ ∈ A := mem_map_of_mem (MulAut.conj g).toMonoidHom hw
    have he : w / (g * w * g⁻¹) ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_div, map_mul, map_mul, map_inv, hc']
      exact div_self' _
    have hm := (normalizer (A : Set G)).mul_mem (hkA he) (A.le_normalizer ha)
    simpa only [div_mul_cancel] using hm
  have hi : (normalizer (A : Set G)).relIndex V ∣ 2 := by
    apply relIindex_dvd_two_iff'.mpr
    refine ⟨v, hv, fun w hw => ?_⟩
    rcases hsign w hw with hf | hi
    · exact Or.inr (hfix w hw hf)
    · left
      apply hfix (v * w) (V.mul_mem hv hw)
      simp only [map_mul, mul_inv_rev]
      calc
        (q v * q w) * q g * ((q w)⁻¹ * (q v)⁻¹) =
            q v * (q w * q g * (q w)⁻¹) * (q v)⁻¹ := by group
        _ = q v * (q g)⁻¹ * (q v)⁻¹ := by rw [hi]
        _ = q g := by simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hinv
  exact ((Nat.dvd_prime Nat.prime_two).mp hi).resolve_left
    (fun he => hproper (relIndex_eq_one.mp he))

/-- An odd cyclic line in the quotient gives a literal hyperplane pair upstairs.
The original elementary subgroup need only normalize that quotient odd subgroup. -/
theorem exists_odd_pair_index_two_of_quotient_action
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hTI : IsTISubgroup V)
    (q : G →* K) (hq : Function.Surjective q)
    (hk : q.ker ≤ normalizer (V : Set G))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (R : Subgroup K)
    (hR : IsPGroup p R) (hn : V.map q ≤ normalizer (R : Set K))
    (hm : ⁅R, V.map q⁆ ≠ ⊥) :
    ∃ g : G, Odd (orderOf g) ∧
      (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V = 2 := by
  let : Finite K := Finite.of_surjective q hq
  let : IsElementaryAbelian 2 (V.map q) := IsElementaryAbelian.map _
  obtain ⟨b, u, a, _, hu, ha, ho, hinv, hsign⟩ :=
    Theory.GroupAction.exists_inverted_prime_power_line hp R (V.map q) hR hn hm
  have hb : Odd (orderOf b) := ho.symm ▸ ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have hb1 : b ≠ 1 := by
    intro he
    have hpow : 1 < p ^ a := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
    rw [← ho, he, orderOf_one] at hpow
    omega
  obtain ⟨x, hx⟩ := hq b
  obtain ⟨g, _, hg, hgq⟩ := q.exists_odd_power_with_image x (hx ▸ hb)
  have hgb : q g = b := hgq.trans hx
  obtain ⟨v, hv, hvu⟩ := hu
  refine ⟨g, hg, pair_normalizer_index_two_of_quotient_inverted_line V hTI q hk
    g v hv (hgb ▸ hb) (hgb ▸ hb1) ?_ ?_⟩
  · simpa only [hgb, hvu] using hinv
  · intro w hw
    simpa only [hgb] using hsign (q w) (mem_map_of_mem q hw)

omit [Finite G] in
/-- The subgroup index convention is exactly binary codimension one. -/
theorem pairAxisSpace_isCoatom_of_index_two
    (V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hi : (normalizer (A : Set G)).relIndex V = 2) :
    IsCoatom (pairAxisSpace V A) := by
  let D := (normalizer (A : Set G)).subgroupOf V
  have hiD : D.index = 2 := hi
  have hD : IsCoatom D := by
    refine ⟨fun ht => by simp [ht] at hiD, fun B hDB => ?_⟩
    have hm := Subgroup.relIndex_mul_index hDB.le
    rw [hiD] at hm
    have hp : (D.relIndex B * B.index).Prime := hm ▸ Nat.prime_two
    rcases Nat.prime_mul_iff.mp hp with ⟨_, hB⟩ | ⟨_, hr⟩
    · exact Subgroup.index_eq_one.mp hB
    · exact (hDB.not_ge (Subgroup.relIndex_eq_one.mp hr)).elim
  exact ((Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)).isCoatom_iff _).mpr hD

end CFSG.Quasithin.ChapterI.Section06To08
