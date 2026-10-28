module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.FixedInvolutions

/-!
# Unitary geometry through actual model isomorphisms

The concrete SU₃ and PSU₃ calculations apply in the original group of a
Section 16 consumer once it has an actual model isomorphism. We transport
the Sylow normalizer, its right-conjugate intersection, the literal
commutator, the fixed torus and the common centralizer through that same
isomorphism. The resulting root equivalence has the consumer's original
`rootGenerated` subgroup as its domain, including in the SU₃ case.

The two field cardinalities are unchanged. No recognition of arbitrary
central covers, standard-pair assumption, or extra automorphism premise
is used. The fixed-involution results are re-exported from `FixedInvolutions`.

Source: GLS4, Chapter 4, Lemmas 3.2(b–e,h) and 3.4(f), used in Chapter 2,
16.2(b3) and 16.4–16.5.
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup PFchapter1section1 PFAppendixIII _root_.BenderSuzuki.MatrixGroups

section Transport
variable {G H : Type*} [Group G] [Group H]

private theorem twoPoint_map_equiv (e : G ≃* H) (B : Subgroup G) (t : G) :
    (twoPoint B t).map e.toMonoidHom = twoPoint (B.map e.toMonoidHom) (e t) := by
  rw [twoPoint, twoPoint, Subgroup.map_inf _ _ _ e.injective]
  congr 1
  simp only [rightConjugate, Subgroup.conjBy, Subgroup.map_map]
  congr 1
  ext x
  simp

private theorem root_map_equiv (e : G ≃* H) (P : Subgroup G) (t : G) :
    (rootGenerated P t).map e.toMonoidHom = rootGenerated (P.map e.toMonoidHom) (e t) := by
  rw [rootGenerated, rootGenerated, Subgroup.map_sup,
    map_omegaOneAmbient_injective e.toMonoidHom e.injective, MonoidHom.map_zpowers]
  rfl

private theorem centralizer_map_equiv (e : G ≃* H) (s : Set G) :
    (centralizer s).map e.toMonoidHom = centralizer (e '' s) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) ⟨y, hy, rfl⟩

private theorem involution_map_equiv (e : G ≃* H) {t : G} (ht : IsInvolution t) :
    IsInvolution (e t) :=
  ⟨fun h => ht.1 (e.injective (h.trans (map_one e).symm)),
    by rw [← map_pow, ht.2, map_one]⟩

variable [Finite G]

private theorem outside_map_equiv (e : G ≃* H) (P : Sylow 2 G) (t : G)
    (ht : t ∉ normalizer (P : Set G)) :
    e t ∉ normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set H) := by
  intro h
  change e t ∈ normalizer ((P : Subgroup G).map e.toMonoidHom : Set H) at h
  rw [← map_equiv_normalizer_eq] at h
  obtain ⟨x, hx, he⟩ := h
  exact ht (e.injective he ▸ hx)

private theorem tori_of_equiv (e : G ≃* H) (P : Sylow 2 G) (t : G)
    {d r c : ℕ}
    (hmodel : let D := twoPoint (normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set H)) (e t)
      IsCyclic D ∧ Nat.card D = d ∧
      IsCyclic (⁅D, zpowers (e t)⁆ : Subgroup H) ∧
      Nat.card (⁅D, zpowers (e t)⁆ : Subgroup H) = r ∧
      (∀ x ∈ ⁅D, zpowers (e t)⁆, rightConjugateElem x (e t) = x⁻¹) ∧
      IsCyclic (D ⊓ centralizer ({e t} : Set H) : Subgroup H) ∧
      Nat.card (D ⊓ centralizer ({e t} : Set H) : Subgroup H) = c) :
    let D := twoPoint (normalizer (P : Set G)) t
    IsCyclic D ∧ Nat.card D = d ∧
      IsCyclic (⁅D, zpowers t⁆ : Subgroup G) ∧
      Nat.card (⁅D, zpowers t⁆ : Subgroup G) = r ∧
      (∀ x ∈ ⁅D, zpowers t⁆, rightConjugateElem x t = x⁻¹) ∧
      IsCyclic (D ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      Nat.card (D ⊓ centralizer ({t} : Set G) : Subgroup G) = c := by
  let D := twoPoint (normalizer (P : Set G)) t
  let D' := twoPoint (normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set H)) (e t)
  have hD : D.map e.toMonoidHom = D' := by
    dsimp only [D, D']
    rw [twoPoint_map_equiv]
    exact congrArg (fun B => twoPoint B (e t)) (map_equiv_normalizer_eq (P : Subgroup G) e)
  have hT : (⁅D, zpowers t⁆ : Subgroup G).map e.toMonoidHom = ⁅D', zpowers (e t)⁆ := by
    rw [Subgroup.map_commutator, hD, MonoidHom.map_zpowers]
    rfl
  have hC : (D ⊓ centralizer ({t} : Set G)).map e.toMonoidHom =
      D' ⊓ centralizer ({e t} : Set H) := by
    rw [Subgroup.map_inf _ _ _ e.injective, hD, centralizer_map_equiv, Set.image_singleton]
  let eD := (D.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hD)
  let eT := ((⁅D, zpowers t⁆ : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hT)
  let eC := ((D ⊓ centralizer ({t} : Set G)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hC)
  obtain ⟨hcD, hd, hcT, hr, hi, hcC, hc⟩ := hmodel
  refine ⟨eD.isCyclic.mpr hcD, (Nat.card_congr eD.toEquiv).trans hd,
    eT.isCyclic.mpr hcT, (Nat.card_congr eT.toEquiv).trans hr, ?_,
    eC.isCyclic.mpr hcC, (Nat.card_congr eC.toEquiv).trans hc⟩
  intro x hx
  have hh := hi (e x) (hT ▸ mem_map_of_mem e.toMonoidHom hx)
  apply e.injective
  simpa only [rightConjugateElem, map_mul, map_inv] using hh

private noncomputable def root_equiv_of_equiv (e : G ≃* H) (P : Sylow 2 G) (t : G) :
    rootGenerated (P : Subgroup G) t ≃*
      rootGenerated (P.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup H) (e t) :=
  ((rootGenerated (P : Subgroup G) t).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (root_map_equiv e (P : Subgroup G) t))

private theorem marked_pair_of_equiv (e : G ≃* H) (P : Sylow 2 G) (z t : G)
    (hgen : zpowers (e z) ⊔ zpowers (e t) ⊔
      ⁅twoPoint (normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set H)) (e t), zpowers (e t)⁆ =
        rootGenerated (P.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup H) (e t))
    (hodd : Odd (Nat.card (centralizer ({e z,e t} : Set H)))) :
    (zpowers z ⊔ zpowers t ⊔ ⁅twoPoint (normalizer (P : Set G)) t, zpowers t⁆ =
      rootGenerated (P : Subgroup G) t) ∧
      Odd (Nat.card (centralizer ({z,t} : Set G))) := by
  have hN : (normalizer (P : Set G)).map e.toMonoidHom =
      normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set H) :=
    map_equiv_normalizer_eq (P : Subgroup G) e
  have hP : (P.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup H) =
      (P : Subgroup G).map e.toMonoidHom := rfl
  rw [hP] at hgen
  constructor
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_sup, Subgroup.map_commutator, MonoidHom.map_zpowers,
      twoPoint_map_equiv, hN,
      root_map_equiv, MulEquiv.coe_toMonoidHom] using hgen
  · have hc : (centralizer ({z,t} : Set G)).map e.toMonoidHom =
        centralizer ({e z,e t} : Set H) := by
      rw [centralizer_map_equiv, Set.image_insert_eq, Set.image_singleton]
    let ec := ((centralizer ({z,t} : Set G)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hc)
    rwa [Nat.card_congr ec.toEquiv]

end Transport

variable {G : Type*} [Group G] [Finite G]
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hn hJ hcard hfixed in
/-- The three literal unitary tori and their orders through a genuine PSU₃ isomorphism. -/
public theorem unitary_projective_tori_of_equiv
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 G)
    (t : G) (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    let D := twoPoint (normalizer (P : Set G)) t
    IsCyclic D ∧ Nat.card D = ((2 ^ n) ^ 2 - 1) / Nat.gcd 3 (2 ^ n + 1) ∧
      IsCyclic (⁅D, zpowers t⁆ : Subgroup G) ∧
      Nat.card (⁅D, zpowers t⁆ : Subgroup G) = 2 ^ n - 1 ∧
      (∀ x ∈ ⁅D, zpowers t⁆, rightConjugateElem x t = x⁻¹) ∧
      IsCyclic (D ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      Nat.card (D ⊓ centralizer ({t} : Set G) : Subgroup G) =
        (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hi := involution_map_equiv e ht
  have ho := outside_map_equiv e P t htB
  obtain ⟨hD, hd⟩ := unitary_projective_twoPoint_torus J hn hcard hfixed hJ Q (e t) hi ho
  obtain ⟨hT, hr, hinv⟩ := unitary_projective_commutator_torus J hn hcard hfixed hJ Q (e t) hi ho
  obtain ⟨hC, hc⟩ := unitary_projective_fixed_torus J hn hcard hfixed hJ Q (e t) hi ho
  exact tori_of_equiv e P t ⟨hD, hd, hT, hr, hinv, hC, hc⟩

include hn hJ hcard hfixed in
/-- The same tori for SU₃ itself, retaining the full scalar center in D and C_D(t). -/
public theorem unitary_special_tori_of_equiv
    (e : G ≃* J.specialSubgroup) (P : Sylow 2 G)
    (t : G) (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    let D := twoPoint (normalizer (P : Set G)) t
    IsCyclic D ∧ Nat.card D = (2 ^ n) ^ 2 - 1 ∧
      IsCyclic (⁅D, zpowers t⁆ : Subgroup G) ∧
      Nat.card (⁅D, zpowers t⁆ : Subgroup G) = 2 ^ n - 1 ∧
      (∀ x ∈ ⁅D, zpowers t⁆, rightConjugateElem x t = x⁻¹) ∧
      IsCyclic (D ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      Nat.card (D ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ n + 1 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hi := involution_map_equiv e ht
  have ho := outside_map_equiv e P t htB
  obtain ⟨hD, hd⟩ := unitary_special_twoPoint_torus J hn hcard hfixed hJ Q (e t) hi ho
  obtain ⟨hT, hr, hinv⟩ := unitary_special_commutator_torus J hn hcard hfixed hJ Q (e t) hi ho
  obtain ⟨hC, hc⟩ := unitary_special_fixed_torus J hn hcard hfixed hJ Q (e t) hi ho
  exact tori_of_equiv e P t ⟨hD, hd, hT, hr, hinv, hC, hc⟩

/-- A concrete PSL₂ equivalence on the original root-generated subgroup of a PSU₃ model. -/
public noncomputable def unitary_projective_rootGenerated_equiv_of_equiv
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 G)
    (t : G) (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    rootGenerated (P : Subgroup G) t ≃* PSL2BinaryMatrixGroup n :=
  (root_equiv_of_equiv e P t).trans
    (unitary_projective_rootGenerated_equiv J hn hcard hfixed hJ
      (P.mapSurjective (f := e.toMonoidHom) e.surjective) (e t) (involution_map_equiv e ht)
      (outside_map_equiv e P t htB))

/-- The original SU₃ root-generated subgroup is PSL₂; no central quotient of it is taken. -/
public noncomputable def unitary_special_rootGenerated_equiv_of_equiv
    (e : G ≃* J.specialSubgroup) (P : Sylow 2 G)
    (t : G) (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    rootGenerated (P : Subgroup G) t ≃* PSL2BinaryMatrixGroup n :=
  (root_equiv_of_equiv e P t).trans
    (unitary_special_rootGenerated_equiv J hn hcard hfixed hJ
      (P.mapSurjective (f := e.toMonoidHom) e.surjective) (e t) (involution_map_equiv e ht)
      (outside_map_equiv e P t htB))

include hn hJ hcard hfixed in
/-- The marked generation and odd common-centralizer clauses in an isomorphic PSU₃ model. -/
public theorem unitary_projective_marked_pair_of_equiv
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 G)
    (z t : G) (hzP : z ∈ P) (hz : IsInvolution z)
    (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    (zpowers z ⊔ zpowers t ⊔ ⁅twoPoint (normalizer (P : Set G)) t, zpowers t⁆ =
      rootGenerated (P : Subgroup G) t) ∧
      Odd (Nat.card (centralizer ({z,t} : Set G))) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hi := involution_map_equiv e ht
  have ho := outside_map_equiv e P t htB
  have hzi := involution_map_equiv e hz
  have hzQ : e z ∈ Q := mem_map_of_mem e.toMonoidHom hzP
  exact marked_pair_of_equiv e P z t
    (unitary_projective_marked_generation J hn hcard hfixed hJ Q (e t) hi ho
      (e z) hzQ hzi.1 hzi.2)
    (unitary_projective_pair_centralizer_odd J hn hcard hfixed hJ Q (e z) (e t) hzQ hzi.1 hi ho)

include hn hJ hcard hfixed in
/-- The marked generation and odd common-centralizer clauses in an isomorphic SU₃ model. -/
public theorem unitary_special_marked_pair_of_equiv
    (e : G ≃* J.specialSubgroup) (P : Sylow 2 G)
    (z t : G) (hzP : z ∈ P) (hz : IsInvolution z)
    (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    (zpowers z ⊔ zpowers t ⊔ ⁅twoPoint (normalizer (P : Set G)) t, zpowers t⁆ =
      rootGenerated (P : Subgroup G) t) ∧
      Odd (Nat.card (centralizer ({z,t} : Set G))) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hi := involution_map_equiv e ht
  have ho := outside_map_equiv e P t htB
  have hzi := involution_map_equiv e hz
  have hzQ : e z ∈ Q := mem_map_of_mem e.toMonoidHom hzP
  exact marked_pair_of_equiv e P z t
    (unitary_special_marked_generation J hn hcard hfixed hJ Q (e t) hi ho
      (e z) hzQ hzi.1 hzi.2)
    (unitary_special_pair_centralizer_odd J hn hcard hfixed hJ Q (e z) (e t) hzQ hzi hi ho)

end BenderSuzuki.ZD.RankOneModelGeometry
