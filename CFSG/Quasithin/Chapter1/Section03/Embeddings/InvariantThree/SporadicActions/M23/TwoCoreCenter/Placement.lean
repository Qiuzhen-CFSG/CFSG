module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M23.IntrinsicLine
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.Mathieu.M22.Properties.NoOrder1152
public import Theory.Mathieu.M23.QuasithinGeometry.Actions

/-!
# Placing an M23 Sylow pair in an actual four-set stabilizer

The product of the Sylow two-subgroup and its elementary-nine complement has
order 1152. After conjugating the Sylow subgroup to the certified permutation
subgroup, its 1+2+4+16 point orbits constrain the product's orbits. A fixed point
would embed it in M22, which has no subgroup of order 1152. Orbit divisibility
therefore forces an invariant four-set. Four-transitivity gives its stabilizer
order 1152, so the containment is equality.

The resulting equivalence is induced by actual M23 conjugations in the fixed
Witt-design carrier. No abstract local-model identification or splitting
hypothesis is used. The two-core and its center remain to be computed in this
four-set stabilizer.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher's *Sporadic Groups*;
GLS3, Table 5.3d. The needed natural action is the certified S(4,7,23) action.
-/

open Subgroup MulAction
open scoped Pointwise Classical
open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions

private theorem sylow_card (S : Sylow 2 M23) : Nat.card S = 128 := by
  rw [Sylow.card_eq_multiplicity, m23_order,
    show Nat.factorization 10200960 2 = 7 by decide +kernel]
  norm_num

/-- The actual product of an M23 Sylow pair has order 1152. -/
public theorem m23_pair_product_card {S : Sylow 2 M23} {R : Subgroup M23}
    (h : PairInput S R) : Nat.card (R ⊔ (S : Subgroup M23) : Subgroup M23) = 1152 := by
  rw [EvenRankTwo.product_card h, (m23_pair_elementary_nine h).2, sylow_card]

private theorem no_fixed_point (H : Subgroup M23) (hH : Nat.card H = 1152)
    (x : Fin 23) : ¬ H ≤ stabilizer M23 x := by
  intro hle
  let : IsPretransitive M23 (Fin 23) := m23_isPretransitive
  obtain ⟨g, hg⟩ := exists_smul_eq M23 (9 : Fin 23) x
  let e : stabilizer M23 x ≃* M22 :=
    (stabilizerEquivStabilizer hg.symm).symm.trans m23EquivM22PointStabilizer.symm
  apply m22_subgroup_card_ne_1152 ((H.subgroupOf (stabilizer M23 x)).map e.toMonoidHom)
  rw [card_map_of_injective e.injective]
  exact (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hH

private def orbitClass (x : Fin 23) : Fin 4 :=
  if x = 0 then 0 else if x = 6 ∨ x = 12 then 1
  else if x = 5 ∨ x = 11 ∨ x = 17 ∨ x = 18 then 2 else 3

private def seed : Fin 4 → Fin 23 := ![0, 6, 5, 1]

private theorem class_seed : ∀ i, orbitClass (seed i) = i := by decide +kernel

set_option maxRecDepth 100000 in
private theorem seed_reaches : ∀ x : Fin 23, ∃ i : Fin 128,
    FusionCertificate.perm i (seed (orbitClass x)) = x := by decide +kernel

private def selected (b : Fin 4 → Bool) : Finset (Fin 23) :=
  Finset.univ.filter fun x => b (orbitClass x)

private theorem selected_zero (b : Fin 4 → Bool)
    (h0 : 0 ∈ selected b) (hd : (selected b).card ∣ 1152) :
    selected b = {0} ∨ selected b = {0, 6, 12} := by
  revert b
  decide +kernel

private theorem selected_five (b : Fin 4 → Bool)
    (h5 : 5 ∈ selected b) (h0 : 0 ∉ selected b) (h6 : 6 ∉ selected b)
    (hd : (selected b).card ∣ 1152) : selected b = {5, 11, 17, 18} := by
  revert b
  decide +kernel

private theorem seed_mem_iff (H : Subgroup M23) (hS : FusionCertificate.subgroup ≤ H)
    (x y : Fin 23) : seed (orbitClass x) ∈ orbit H y ↔ x ∈ orbit H y := by
  obtain ⟨i, hi⟩ := seed_reaches x
  let g : H := ⟨⟨FusionCertificate.perm i, FusionCertificate.rawSubgroup_le
    (FusionCertificate.perm_mem i)⟩, hS (FusionCertificate.perm_mem i)⟩
  have hg : g • seed (orbitClass x) = x := hi
  constructor
  · intro hx
    simpa only [hg] using mem_orbit_of_mem_orbit g hx
  · intro hx
    have hback : g⁻¹ • x = seed (orbitClass x) := inv_smul_eq_iff.mpr hg.symm
    simpa only [hback] using mem_orbit_of_mem_orbit g⁻¹ hx

private theorem orbit_selected (H : Subgroup M23) (hS : FusionCertificate.subgroup ≤ H)
    (y : Fin 23) : ∃ b : Fin 4 → Bool, (orbit H y).toFinset = selected b := by
  classical
  refine ⟨fun i => decide (seed i ∈ orbit H y), ?_⟩
  ext x
  simp only [selected, Finset.mem_filter, Finset.mem_univ, decide_eq_true_eq, true_and,
    Set.mem_toFinset]
  exact (seed_mem_iff H hS x y).symm

private theorem orbit_card_dvd (H : Subgroup M23) (hH : Nat.card H = 1152)
    (x : Fin 23) : (orbit H x).toFinset.card ∣ 1152 := by
  rw [← Set.ncard_eq_toFinset_card', ← index_stabilizer, ← hH]
  exact (stabilizer H x).index_dvd_card

private theorem standard_four_invariant (H : Subgroup M23) (hH : Nat.card H = 1152)
    (hS : FusionCertificate.subgroup ≤ H) :
    H ≤ stabilizer M23 ({5, 11, 17, 18} : Finset (Fin 23)) := by
  classical
  obtain ⟨b, hb⟩ := orbit_selected H hS 0
  have h0 : (0 : Fin 23) ∈ selected b := hb ▸ (Set.mem_toFinset.mpr (mem_orbit_self 0))
  have hd : (selected b).card ∣ 1152 := hb ▸ orbit_card_dvd H hH 0
  have hz : (orbit H (0 : Fin 23)).toFinset = {0, 6, 12} := by
    rcases selected_zero b h0 hd with he | he
    · exfalso
      apply no_fixed_point H hH 0
      intro g hg
      have hm : (g • (0 : Fin 23)) ∈ (orbit H (0 : Fin 23)).toFinset :=
        Set.mem_toFinset.mpr (mem_orbit 0 (⟨g, hg⟩ : H))
      rw [hb, he, Finset.mem_singleton] at hm
      exact hm
    · exact hb.trans he
  obtain ⟨c, hc⟩ := orbit_selected H hS 5
  have h5 : (5 : Fin 23) ∈ selected c := hc ▸ (Set.mem_toFinset.mpr (mem_orbit_self 5))
  have hnot (x : Fin 23) (hx : x = 0 ∨ x = 6) : x ∉ selected c := by
    intro hxc
    have hxf : x ∈ orbit H (5 : Fin 23) := Set.mem_toFinset.mp (hc.symm ▸ hxc)
    have hxz : x ∈ orbit H (0 : Fin 23) := by
      apply Set.mem_toFinset.mp
      rw [hz]
      rcases hx with rfl | rfl <;> simp
    have heq : orbit H (5 : Fin 23) = orbit H (0 : Fin 23) :=
      (orbit_eq_iff.mpr hxf).symm.trans (orbit_eq_iff.mpr hxz)
    have hf : (5 : Fin 23) ∈ (orbit H (0 : Fin 23)).toFinset :=
      Set.mem_toFinset.mpr (heq ▸ mem_orbit_self 5)
    rw [hz] at hf
    exact (by decide : (5 : Fin 23) ∉ ({0, 6, 12} : Finset (Fin 23))) hf
  have hf : (orbit H (5 : Fin 23)).toFinset = {5, 11, 17, 18} :=
    hc.trans (selected_five c h5 (hnot 0 (Or.inl rfl)) (hnot 6 (Or.inr rfl))
      (hc ▸ orbit_card_dvd H hH 5))
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro x hx
  rw [← hf] at hx ⊢
  exact Set.mem_toFinset.mpr (mem_orbit_of_mem_orbit (⟨g, hg⟩ : H) (Set.mem_toFinset.mp hx))

private theorem four_sets_conjugate (A B : Finset (Fin 23))
    (hA : A.card = 4) (hB : B.card = 4) : ∃ g : M23, g • A = B := by
  classical
  let a : Fin 4 ≃ A := (Fintype.equivFinOfCardEq (by simpa using hA)).symm
  let b : Fin 4 ≃ B := (Fintype.equivFinOfCardEq (by simpa using hB)).symm
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp m23_isFourPretransitive)
    (a.toEmbedding.trans (Function.Embedding.subtype _))
    (b.toEmbedding.trans (Function.Embedding.subtype _))
  have happ (i : Fin 4) : g • (a i).val = (b i).val :=
    congrArg (fun f : Fin 4 ↪ Fin 23 => f i) hg
  refine ⟨g, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hx
    obtain ⟨i, hi⟩ := a.surjective ⟨y, hy⟩
    have hi' : (a i).val = y := congrArg Subtype.val hi
    rw [← hi', happ]
    exact (b i).property
  · rw [Finset.card_smul_finset, hA, hB]

private theorem four_stabilizer_card (A : Finset (Fin 23)) (hA : A.card = 4) :
    Nat.card (stabilizer M23 A) = 1152 := by
  have ho : orbit M23 A =
      ((Finset.univ : Finset (Fin 23)).powersetCard 4 : Set (Finset (Fin 23))) := by
    ext B
    rw [mem_orbit_iff, Finset.mem_coe, Finset.mem_powersetCard]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨Finset.subset_univ _, (Finset.card_smul_finset _ _).trans hA⟩
    · rintro ⟨_, hB⟩
      exact four_sets_conjugate A B hA hB
  have hi : (stabilizer M23 A).index = 8855 := by
    rw [index_stabilizer, ho, Set.ncard_coe_finset, Finset.card_powersetCard]
    decide
  have hc := (stabilizer M23 A).card_mul_index
  rw [hi, m23_order] at hc
  omega

/-- A Sylow pair in the concrete Witt-design carrier is an actual four-set stabilizer. -/
public theorem m23_pair_eq_fourSet_stabilizer {S : Sylow 2 M23} {R : Subgroup M23}
    (h : PairInput S R) :
    ∃ A : Finset (Fin 23), A.card = 4 ∧
      R ⊔ (S : Subgroup M23) = stabilizer M23 A := by
  let X : Subgroup M23 := R ⊔ (S : Subgroup M23)
  obtain ⟨g, hg⟩ := exists_smul_eq M23 S FusionCertificate.sylow
  let e : MulAut M23 := MulAut.conj g
  let Y := X.map e.toMonoidHom
  have hY : Nat.card Y = 1152 :=
    (card_map_of_injective e.injective).trans (m23_pair_product_card h)
  have hSY : FusionCertificate.subgroup ≤ Y := by
    have heq : (S : Subgroup M23).map e.toMonoidHom = FusionCertificate.subgroup :=
      congrArg Sylow.toSubgroup hg
    rw [← heq]
    exact Subgroup.map_mono le_sup_right
  let A : Finset (Fin 23) := {5, 11, 17, 18}
  have hA : A.card = 4 := by decide
  have heq : Y = stabilizer M23 A := eq_of_le_of_card_ge
    (standard_four_invariant Y hY hSY) (by rw [hY, four_stabilizer_card A hA])
  refine ⟨g⁻¹ • A, (Finset.card_smul_finset _ _).trans hA, ?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.map_map]
  change Y = (stabilizer M23 A).map
    (e.toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom)
  have hi : e.toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id M23 := by
    apply MonoidHom.ext
    intro x
    change g * (g⁻¹ * x * (g⁻¹)⁻¹) * g⁻¹ = x
    simp [mul_assoc]
  rw [hi, Subgroup.map_id]
  exact heq

/-- In particular the product is isomorphic to the fixed four-set stabilizer,
through conjugations in the original M23, not a separate abstract model. -/
public theorem m23_pair_fourStabilizer_equiv {S : Sylow 2 M23} {R : Subgroup M23}
    (h : PairInput S R) : Nonempty ((R ⊔ (S : Subgroup M23) : Subgroup M23) ≃* fourStabilizer) := by
  obtain ⟨A, hA, heq⟩ := m23_pair_eq_fourSet_stabilizer h
  obtain ⟨g, hg⟩ := four_sets_conjugate A lambda hA lambda_card
  exact ⟨(MulEquiv.subgroupCongr heq).trans (stabilizerEquivStabilizer hg.symm)⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
