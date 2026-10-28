module
public import Theory.AlgebraicGroup.BNPair.StandardParabolicCore
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow

/-!
# The Sylow subgroup and two-core of a finite split BN-pair

For a split Tits system in characteristic two, the specified normal
unipotent subgroup U is Sylow in the whole group and has normalizer B.
It is the embedded two-core of B, meets N trivially, and the ambient
normal two-core is trivial. Saturation puts the normal core of B inside
B ∩ N; a faithful Borel therefore also forces a trivial ambient center.

To compute the normalizer, classify its overgroup of B by its simple
Bruhat cells. A simple representative normalizing U also normalizes
B ∩ N, hence B, contradicting the nontriviality axiom. The index of U
in B is odd, and the fixed-coset congruence modulo two makes its ambient
index odd as well. Normal two-subgroups lie in U and, by saturation, in
the odd group B ∩ N, so are trivial.

These are elementary reduction steps for the finite quotient used in
DGS, Groups and Graphs, Part II, Theorem D, printed p.224. The precise
splitness convention and the Sylow/core arguments are in the supplied
GLS3 Carter excerpt, Chapter2Ca2.tex, split BN-pair definition and
Propositions 2.5.1–2.5.2. They do not establish Fong–Seitz minimality or
recognition and assume no Weyl-group order or Lie-model identification.
-/

@[expose] public section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X]

/-- The characteristic-two splitness hypotheses for this particular B,N.
The torus is literally B ∩ N. The saturation intersection uses all elements
of N; replacing them by inverses gives the usual conjugate convention. -/
structure SplitData (T : TitsSystem (X := X)) where
  U : Subgroup X
  U_le : U ≤ T.B
  normalizes : T.B ≤ normalizer (U : Set X)
  isTwo : IsPGroup 2 U
  odd : Nat.Coprime 2 (Nat.card (T.B ⊓ T.N : Subgroup X))
  abelian : IsMulCommutative (T.B ⊓ T.N : Subgroup X)
  factorization : U ⊔ (T.B ⊓ T.N) = T.B
  saturation : (⨅ n : T.N, T.B.comap (MulAut.conj (n : X)).toMonoidHom) = T.B ⊓ T.N

namespace SplitData
variable {T : TitsSystem (X := X)} (d : SplitData T)

/-- The specified unipotent subgroup has the full Borel as its normalizer. -/
theorem normalizer_eq : normalizer (d.U : Set X) = T.B := by
  apply le_antisymm ?_ d.normalizes
  rw [T.subgroup_eq_standardParabolic_simpleIndices _ d.normalizes]
  apply T.standardParabolic_le T.B le_rfl
  intro s hs
  rcases (T.mem_simpleIndices_iff _ _).mp hs with ⟨hs, hsCell⟩
  exfalso
  obtain ⟨n, b, hn, hb, hcell⟩ := T.exists_rankOne_witness hs
  have hnU : (n : X) ∈ normalizer (d.U : Set X) :=
    hsCell (T.representative_mem_bruhatCell s n hn)
  have hnH : (n : X) ∈ normalizer ((T.B ⊓ T.N : Subgroup X) : Set X) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).mp
      T.intersection_normal n.property
  have hnB : (n : X) ∈ normalizer (T.B : Set X) := by
    rw [← d.factorization]
    exact normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hnU, hnH⟩
  have hconj : (n : X) * b * (n : X)⁻¹ ∈ T.B :=
    (mem_normalizer_iff.mp hnB b).mp hb
  have hsq : ((n : X) ^ 2) ∈ T.B :=
    (T.representative_sq_mem_intersection hs n hn).1
  have hw : (n : X) * b * (n : X) ∈ T.B := by
    have := T.B.mul_mem hconj hsq
    simpa only [pow_two, mul_assoc, inv_mul_cancel_left] using this
  have hw' : (n : X) * b * (n : X) ∈ T.bruhatCell 1 := by
    rw [T.bruhatCell_one]
    exact hw
  exact (T.involutions s hs).1 (T.doubleCoset_index_unique hcell hw')

/-- The actual normal two-subgroup has odd index inside the Borel. -/
theorem borel_index_not_two [Finite X] : ¬ 2 ∣ (d.U.subgroupOf T.B).index := by
  let U := d.U.subgroupOf T.B
  let H := (T.B ⊓ T.N).subgroupOf T.B
  let : U.Normal := normal_subgroupOf_of_le_normalizer d.normalizes
  have hjoin : U ⊔ H = ⊤ := by
    rw [← subgroupOf_sup d.U_le inf_le_left, d.factorization, subgroupOf_self]
  have hi : U.index = U.relIndex H := by
    rw [← relIndex_top_right, ← hjoin, relIndex_sup_left]
  have hcard : Nat.card H = Nat.card (T.B ⊓ T.N : Subgroup X) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  intro hdiv
  apply Nat.prime_two.coprime_iff_not_dvd.mp d.odd
  rw [← hcard]
  exact hdiv.trans (hi ▸ U.relIndex_dvd_card H)

/-- The fixed-coset congruence promotes the odd Borel index to the whole group. -/
theorem index_not_two [Finite X] : ¬ 2 ∣ d.U.index := by
  obtain ⟨n, hn⟩ := d.isTwo.exists_card_eq
  have he := Sylow.card_quotient_normalizer_modEq_card_quotient hn
  change (d.U.subgroupOf (normalizer (d.U : Set X))).index ≡ d.U.index [MOD 2] at he
  rw [d.normalizer_eq] at he
  exact fun h => d.borel_index_not_two ((he.dvd_iff dvd_rfl).mpr h)

/-- The specified U, with its ambient Sylow property proved. -/
def sylow [Finite X] : Sylow 2 X := d.isTwo.toSylow d.index_not_two

/-- No replacement or conjugation of the specified U is made. -/
@[simp] theorem coe_sylow [Finite X] : (d.sylow : Subgroup X) = d.U := rfl

/-- The Borel two-core is exactly U, compared in the Borel carrier. -/
theorem borel_twoCore [Finite X] : pCore 2 T.B = d.U.subgroupOf T.B := by
  let : (d.U.subgroupOf T.B).Normal := normal_subgroupOf_of_le_normalizer d.normalizes
  apply le_antisymm
  · exact pCore_isPGroup.le_sylow_of_normal
      (d.isTwo.comap_subtype.toSylow d.borel_index_not_two)
  · exact le_sSup ⟨inferInstance, d.isTwo.comap_subtype⟩

/-- The unipotent subgroup has trivial intersection with the chosen N. -/
theorem unipotent_inf_N [Finite X] : d.U ⊓ T.N = ⊥ := by
  obtain ⟨n, hn⟩ := d.isTwo.exists_card_eq
  have hd : Disjoint d.U (T.B ⊓ T.N) := disjoint_of_coprime_natCard
    (by rw [hn]; exact d.odd.pow_left n)
  apply le_bot_iff.mp
  exact (le_inf inf_le_left (le_inf (inf_le_left.trans d.U_le) inf_le_right)).trans hd.le_bot

include d in
/-- Saturation traps the entire normal Borel core in its actual torus. -/
theorem borel_normalCore_le_intersection : T.B.normalCore ≤ T.B ⊓ T.N := by
  rw [← d.saturation]
  intro x hx
  simp only [mem_iInf, mem_comap]
  intro n
  exact T.B.normalCore_le ((inferInstance : T.B.normalCore.Normal).conj_mem x hx n)

include d in
/-- Borel faithfulness eliminates the ambient center. -/
theorem center_eq_bot_of_borel_core (hcore : T.B.normalCore = ⊥) : center X = ⊥ := by
  have hz : center X ≤ T.B := by
    rw [← d.normalizer_eq]
    exact center_le_normalizer _
  exact le_bot_iff.mp (hcore ▸ normal_le_normalCore.mpr hz)

include d in
/-- Every ambient normal two-subgroup is trivial. -/
theorem normal_two_subgroup_eq_bot [Finite X] (V : Subgroup X) [V.Normal]
    (hv : IsPGroup 2 V) : V = ⊥ := by
  have hVU : V ≤ d.U := hv.le_sylow_of_normal d.sylow
  have hVH : V ≤ T.B ⊓ T.N := by
    rw [← d.saturation]
    intro x hx
    simp only [mem_iInf, mem_comap]
    intro n
    exact d.U_le (hVU ((inferInstance : V.Normal).conj_mem x hx n))
  obtain ⟨n, hn⟩ := hv.exists_card_eq
  have hd : Nat.card V ∣ Nat.card (T.B ⊓ T.N : Subgroup X) := card_dvd_of_le hVH
  have hc : Nat.Coprime (2 ^ n) (Nat.card (T.B ⊓ T.N : Subgroup X)) := d.odd.pow_left n
  exact card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hc (hn ▸ dvd_rfl) hd)

include d in
/-- The finite split carrier has trivial two-core. -/
theorem twoCore_eq_bot [Finite X] : pCore 2 X = ⊥ :=
  d.normal_two_subgroup_eq_bot _ pCore_isPGroup

end SplitData
end Theory.AlgebraicGroup.TitsSystem.SourceBinary
