module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.PrimeModel
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.RemainingBranch
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.ElementaryAbelian.PrimePlane
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CharacteristicVertex
/-!
# The actual opposite vertex in the odd-prime product branch

The opposite two-core centralizing the component is normal in G=KG₂ and
therefore trivial. An elementary opposite core fixes its Sylow intersection
with K pointwise. Prime-field PSL₂ rigidity realizes each such automorphism
by that intersection, so faithfulness places the entire core in K.
The two-rank calculation gives core order four and overlap order eight;
the exceptional-amalgam bound forces the opposite vertex to be S₄.

Source: Aschbacher--Smith F.6.17(2), printed p.309. The final source adapter
uses the actual cubic left residual supplied by F.6.13 and constructs the
characteristic-two failure and elementary core hypotheses internally.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

omit [Finite G] in
theorem SingleResidualComponent.core_disjoint_centralizer (d : SingleResidualComponent G₁ G₂) (hcore : pCore 2 G = ⊥) :
    Disjoint ((pCore 2 G₂).map G₂.subtype) (centralizer (d.component : Set G)) := by
  let K := d.component
  let Q := (pCore 2 G₂).map G₂.subtype
  let C := centralizer (K : Set G)
  let N := Q ⊓ C
  let : K.Normal := d.normal
  have hnG₂ : G₂ ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg n hn
    exact ⟨(mem_normalizer_iff.mp ((pCore 2 G₂).le_normalizer_map G₂.subtype
      (show g ∈ (normalizer (pCore 2 G₂)).map G₂.subtype by
        exact ⟨⟨g,hg⟩, by rw [normalizer_eq_top]; trivial, rfl⟩)) n).mp hn.1,
      (inferInstance : C.Normal).conj_mem n hn.2 g⟩
  have hnK : K ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk n hn
    have hc : k*n*k⁻¹=n := by rw [hn.2 k hk]; group
    simpa only [hc] using hn
  have hn : N.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← d.generates]
    exact sup_le hnK hnG₂))
  have hle : N ≤ pCore 2 G := le_sSup ⟨hn,(pCore_isPGroup.map G₂.subtype).to_le inf_le_left⟩
  exact disjoint_iff.mpr (le_bot_iff.mp (hle.trans hcore.le))


open scoped MatrixGroups
theorem SingleResidualComponent.core_le_component_of_prime_model (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hQ : IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hl : 3 < p)
    (j : d.component ≃* PSL(2,ZMod p)) :
    (pCore 2 G₂).map G₂.subtype ≤ d.component := by
  let K := d.component
  let Q := (pCore 2 G₂).map G₂.subtype
  let : K.Normal := d.normal
  let : IsElementaryAbelian 2 Q := hQ
  have hd := SingleResidualComponent.core_disjoint_centralizer d hcore
  obtain ⟨S,hS⟩ := sylow_in_normal_eq_right_core_intersection h K d.right_escapes
  have hSQ : (S : Subgroup K).map K.subtype ≤ Q := hS.le.trans inf_le_left
  intro q hq
  let a : MulAut K := MulAut.conjNormal q
  have hfix : ∀ x ∈ S, a x = x := by
    intro x hx
    apply Subtype.ext
    have hxQ : (x : G) ∈ Q := hSQ ⟨x,hx,rfl⟩
    have hc : q * (x : G) = (x : G) * q :=
      congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨q,hq⟩ : Q) ⟨x,hxQ⟩)
    change q * (x : G) * q⁻¹ = (x : G)
    rw [hc]
    group
  obtain ⟨x,hx,ha⟩ := Theory.PSL2.SylowFixedQuotients.fixed_inner_transport j
    (S : Subgroup K)
    (fun b hb => Theory.PSL2.primeField_sylow_fixed_inner hp hl
      (S.mapSurjective (f := j.toMonoidHom) j.surjective) b hb) a hfix
  have hxQ : (x : G) ∈ Q := hSQ ⟨x,hx,rfl⟩
  have hz : q * (x : G)⁻¹ ∈ centralizer (K : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer K]
    change (MulAut.conjNormal : G →* MulAut K) (q * (x : G)⁻¹) = 1
    rw [map_mul,map_inv,MulAut.conjNormal_val]
    change a * (MulAut.conj x)⁻¹ = 1
    rw [ha,mul_inv_cancel]
  have he : q * (x : G)⁻¹ = 1 := hd.le_bot ⟨Q.mul_mem hq (Q.inv_mem hxQ),hz⟩
  exact (mul_inv_eq_one.mp he).symm ▸ x.property


theorem SingleResidualComponent.core_four_overlap_eight_of_prime_model (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hQ : IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hl : 3 < p)
    (j : d.component ≃* PSL(2,ZMod p)) :
    Nat.card ((pCore 2 G₂).map G₂.subtype) = 4 ∧ Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8 := by
  let K := d.component
  let Q := (pCore 2 G₂).map G₂.subtype
  let : K.Normal := d.normal
  let : IsElementaryAbelian 2 Q := hQ
  have hQK := SingleResidualComponent.core_le_component_of_prime_model d h hcore hQ hp hl j
  obtain ⟨S,hS⟩ := sylow_in_normal_eq_right_core_intersection h K d.right_escapes
  rw [inf_eq_left.mpr hQK] at hS
  let eS : S ≃* Q := ((S : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hS)
  have hr : primeRank 2 Q = 2 := by
    rw [← primeRank_equiv 2 eS, ← S.primeRank_eq, primeRank_equiv 2 j]
    exact Theory.PSL2.primeField_two_rank hl
  have hQcard : Nat.card Q = 4 :=
    IsElementaryAbelian.card_eq_prime_sq_of_primeRank_two hr
  refine ⟨hQcard,?_⟩
  have hQT : Q ≤ G₁ ⊓ G₂ := by
    simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection
  have hh := (Q.subgroupOf (G₁ ⊓ G₂)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hQT).toEquiv,hQcard] at hh
  have hi : (Q.subgroupOf (G₁ ⊓ G₂)).index = 2 := by
    change Q.relIndex (G₁ ⊓ G₂) = 2
    have ht := h.symm.left_core_index
    rw [inf_comm G₂ G₁] at ht
    exact ht
  rw [hi] at hh
  exact hh.symm


theorem SingleResidualComponent.right_vertex_and_overlap_of_prime_model (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hbad : generalizedFitting G₁ ≠ pCore 2 G₁)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hl : 3 < p)
    (j : d.component ≃* PSL(2,ZMod p)) :
    (pCore 2 G₂).map G₂.subtype ≤ d.component ∧
      Nat.card ((pCore 2 G₂).map G₂.subtype) = 4 ∧
      Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8 ∧
      generalizedFitting G₂ = pCore 2 G₂ ∧
      Nonempty (G₂ ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) := by
  obtain ⟨hQ,_,_⟩ := right_core_small_elementary_of_not_characteristic_two h hcore hbad
  have hle := SingleResidualComponent.core_le_component_of_prime_model d h hcore hQ hp hl j
  obtain ⟨hfour,he⟩ := SingleResidualComponent.core_four_overlap_eight_of_prime_model d h hcore hQ hp hl j
  have hgood : generalizedFitting G₂ = pCore 2 G₂ := by
    by_contra hbad₂
    have hh := h.intersection_card_of_neither_characteristic_two hcore hbad hbad₂
    omega
  have he' : Nat.card (G₂ ⊓ G₁ : Subgroup G) = 8 := by rw [inf_comm]; exact he
  obtain ⟨t⟩ := h.symm.intersection_equiv_dihedral_four_of_characteristic_two hgood he'
  exact ⟨hle,hfour,he,hgood,
    h.symm.local_equiv_symmetric_four_of_intersection_card_eight hgood he',
    ⟨(MulEquiv.subgroupCongr (inf_comm G₁ G₂)).trans t⟩⟩


/-- The actual cubic residual excludes characteristic two at the first vertex. -/
theorem left_not_characteristic_two_of_cubic
    (h : IsGoldschmidtTriple G₁ G₂)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    generalizedFitting G₁ ≠ pCore 2 G₁ := by
  have hcard : Nat.card (pResidual 2 G₁) = 3 := by
    rwa [card_map_of_injective G₁.subtype_injective] at hc
  have hp : pResidual 2 G₁ ≤ pPrimeCore 2 G₁ :=
    le_sSup ⟨inferInstance, by rw [hcard]; decide⟩
  intro hg
  have he := (SymmetricThreeTwoCore.characteristic_two_iff h.quotient_left.some).mp hg
  have hb : pResidual 2 G₁ = ⊥ := le_bot_iff.mp (hp.trans he.le)
  simp [hb] at hcard

/-- All opposite-vertex and Sylow conclusions on the original quotient;
only the earlier F.6.13 cubic residual and actual prime-field model remain. -/
theorem SingleResidualComponent.source_prime_local_models
    {H : Type*} [Group H] [Finite H] (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    (pCore 2 G₂).map G₂.subtype ≤ d.component ∧
      Nat.card ((pCore 2 G₂).map G₂.subtype) = 4 ∧
      Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8 ∧
      generalizedFitting G₂ = pCore 2 G₂ ∧
      Nonempty (G₂ ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) := by
  obtain ⟨_,_,⟨j⟩⟩ := prime_psl_component_center_and_outer e d.isComponent hp hm
  exact d.right_vertex_and_overlap_of_prime_model h
    (le_bot_iff.mp (twoCore_le_primeToThreeCore.trans_eq
      (Noncyclic.primeToThreeCore_eq_bot_of_quotient e)))
    (left_not_characteristic_two_of_cubic h hc) hp
    (prime_psl_component_prime_gt_three d.isComponent hp hm) j
end CFSG.Quasithin.ChapterF.SourceAssembly
