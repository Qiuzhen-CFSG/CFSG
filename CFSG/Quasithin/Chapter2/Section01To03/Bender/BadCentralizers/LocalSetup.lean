module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.OnanExclusion
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentGeometry
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization
public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.Representation.BinaryHyperplane
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.AbelianCoprimeFullFixedGeneration
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Mathlib.LinearAlgebra.Isomorphisms

/-!+# The source bad-centralizer setup in the Bender argument

The selected irreducible binary subgroup U has an orbit of z meeting every
hyperplane. Coprime fixed-point generation puts the odd core of every
nonidentity U-element centralizer in M, where characteristic two kills it.
Sylow conjugacy is made only inside M, moving u and its component together
while retaining U and the original distinguished z.

These lemmas concern Proposition 2.2.2, printed pp.519--520. All model
classification and L-balance inputs remain separate earlier-source results.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

namespace BadCentralizers

private theorem mem_zpowers_two {z x : G} (hz : orderOf z = 2)
    (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

omit [Finite G] in
private theorem centralizer_zpowers (u : G) :
    centralizer (zpowers u : Set G) = centralizer ({u} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

omit [Finite G] in
private theorem centralizer_map (e : G ≃* G) (u : G) :
    (centralizer ({u} : Set G)).map e.toMonoidHom =
      centralizer ({e u} : Set G) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
        congrArg e (mem_centralizer_singleton_iff.mp hy))
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

omit [Finite G] in
private theorem centralizer_le_of_conjugate {z u : G} (m : M)
    (hC : centralizer ({z} : Set G) ≤ M) (he : (MulAut.conj (m : G)) z = u) :
    centralizer ({u} : Set G) ≤ M := by
  rw [← he, ← centralizer_map]
  exact (map_mono hC).trans_eq (mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer m.property))

end BadCentralizers

/-- The bad-centralizer branch forces U to be larger than its distinguished line. -/
theorem LocalControlWitness.ne_zpowers_of_bad_centralizer
    (w : LocalControlWitness T M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M) :
    w.U ≠ zpowers w.z := by
  intro he
  obtain ⟨u, hu, hu1, hC⟩ := hbad
  rcases BadCentralizers.mem_zpowers_two w.z_order (he ▸ hu) with h | h
  · exact hu1 h
  · exact hC (h.symm ▸ w.centralizer_le)

omit [Finite G] in
/-- U centralizes each of its elements, with the literal ambient centralizer. -/
theorem LocalControlWitness.le_element_centralizer
    (w : LocalControlWitness T M) {u : G} (hu : u ∈ w.U) :
    w.U ≤ centralizer ({u} : Set G) := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm (⟨x, hx⟩ : w.U) ⟨u, hu⟩))

/-- The actual image orbit of z has at least two points in the bad branch. -/
theorem LocalControlWitness.z_image_orbit_card
    (w : LocalControlWitness T M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M) :
    let _ : IsElementaryAbelian 2 w.U := w.elementary
    1 < Nat.card (Set.range (fun a : sourceActionImage w =>
      sourceImageRepresentation w a (Additive.ofMul ⟨w.z, w.z_mem⟩))) := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let zV : Additive w.U := Additive.ofMul ⟨w.z, w.z_mem⟩
  let O := Set.range (fun a : sourceActionImage w => sourceImageRepresentation w a zV)
  change 1 < Nat.card O
  by_contra hn
  let : Subsingleton O := Finite.card_le_one_iff_subsingleton.mp (by omega)
  have hfix (a : sourceActionImage w) : sourceImageRepresentation w a zV = zV := by
    have he := Subsingleton.elim
      (⟨sourceImageRepresentation w a zV, a, rfl⟩ : O)
      (⟨sourceImageRepresentation w 1 zV, 1, rfl⟩ : O)
    simpa only [map_one, Module.End.one_apply] using congrArg Subtype.val he
  have hnM : M ≤ normalizer (zpowers w.z : Set G) := by
    intro m hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    congr 1
    exact congrArg (fun v : Additive w.U => (v.toMul : G))
      (hfix ((conjugationAction M w.U w.normalizes).rangeRestrict ⟨m, hm⟩))
  rcases w.minimal (zpowers w.z) (zpowers_le.mpr w.z_mem) hnM with hb | ht
  · exact w.z_ne_one (mem_bot.mp (hb ▸ mem_zpowers w.z))
  · exact w.ne_zpowers_of_bad_centralizer hbad ht.symm

/-- Every hyperplane contains an actual M-conjugate of the original z.
The subgroup is intrinsic to U and has index two. -/
theorem LocalControlWitness.exists_z_conjugate_mem_hyperplane
    (w : LocalControlWitness T M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M)
    (B : Subgroup w.U) (hB : B.index = 2) :
    ∃ m : M, (m : G) * w.z * (m : G)⁻¹ ∈ B.map w.U.subtype := by
  classical
  let : IsElementaryAbelian 2 w.U := w.elementary
  let : Representation.IsIrreducible (sourceImageRepresentation w) :=
    sourceImageRepresentation_irreducible w
  let zV : Additive w.U := Additive.ofMul ⟨w.z, w.z_mem⟩
  let O := Set.range (fun a : sourceActionImage w => sourceImageRepresentation w a zV)
  let q : Additive w.U →ₗ[ZMod 2] Additive (w.U ⧸ B) :=
    (QuotientGroup.mk' B).toAdditive.toZModLinearMap 2
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective B y.toMul
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  have hc : Nat.card (Additive (w.U ⧸ B)) = 2 := by
    change Nat.card (w.U ⧸ B) = 2
    rwa [← index_eq_card]
  have hd : Module.finrank (ZMod 2) (Additive (w.U ⧸ B)) = 1 := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (w.U ⧸ B))
    rw [hc, Nat.card_zmod] at he
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) (by simpa using he.symm)
  have hker : Module.finrank (ZMod 2) (Additive w.U ⧸ q.ker) = 1 := by
    rw [(q.quotKerEquivOfSurjective hq).finrank_eq, hd]
  obtain ⟨v, ⟨a, rfl⟩, hv⟩ := Representation.BinaryHyperplane.invariant_set_meets_hyperplane
    (sourceImageRepresentation w) O
    (by
      rintro a _ ⟨b, rfl⟩
      refine ⟨a * b, ?_⟩
      simp only [map_mul, Module.End.mul_apply])
    (w.z_image_orbit_card hbad) q.ker hker
  obtain ⟨m, hm⟩ := a.property
  have hvB : (a : MulAut w.U) ⟨w.z, w.z_mem⟩ ∈ B := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg Additive.toMul hv
  refine ⟨m, ?_⟩
  have hx := mem_map_of_mem w.U.subtype hvB
  rw [← hm] at hx
  exact hx

/-- A.1.43 gives the centralizer containment in the exact indexing family
of coprime fixed-point generation, including its trivial quotient. -/
theorem LocalControlWitness.centralizer_le_of_cyclic_quotient
    (w : LocalControlWitness T M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M)
    (B : Subgroup w.U) :
    let _ : IsElementaryAbelian 2 w.U := w.elementary
    IsCyclic (w.U ⧸ B) → centralizer (B.map w.U.subtype : Set G) ≤ M := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  change IsCyclic (w.U ⧸ B) → centralizer (B.map w.U.subtype : Set G) ≤ M
  intro hB
  have hd : B.index ∣ 2 := by
    rw [index_eq_card, ← hB.exponent_eq_card]
    exact (Group.exponent_quotient_dvd B).trans (IsElementaryAbelian.exponent_dvd_p 2 w.U)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · have ht : B = ⊤ := index_eq_one.mp h
    rw [ht, ← MonoidHom.range_eq_map, w.U.range_subtype]
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr w.z_mem)).trans w.centralizer_le
  · obtain ⟨m, hm⟩ := w.exists_z_conjugate_mem_hyperplane hbad B h
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hm)).trans
      (BadCentralizers.centralizer_le_of_conjugate m w.centralizer_le rfl)

/-- Generation by the actual U-fixed subgroups puts every normalized odd
subgroup in M. No solvability premise is needed. -/
theorem LocalControlWitness.normalized_odd_subgroup_le
    (w : LocalControlWitness T M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M)
    (R : Subgroup G) (hR : Nat.Coprime 2 (Nat.card R))
    (hUR : w.U ≤ normalizer (R : Set G)) : R ≤ M := by
  classical
  let : IsElementaryAbelian 2 w.U := w.elementary
  let : Fact (IsPGroup 2 w.U) := ⟨IsElementaryAbelian.isPGroup 2 w.U⟩
  let : MulDistribMulAction w.U R := conjMulDistribMulActionOfLeNormalizer w.U R hUR
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    (G := R) (A := w.U) 2 hR
  have ht : (⊤ : Subgroup R) ≤ M.subgroupOf R := by
    rw [← hgen]
    refine iSup₂_le fun B hB x hx => ?_
    apply w.centralizer_le_of_cyclic_quotient hbad B hB
    rintro b ⟨a, ha, rfl⟩
    have he := congrArg (fun r : R => (r : G)) (hx (⟨a, ha⟩ : B))
    change (a : G) * (x : G) * (a : G)⁻¹ = (x : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  intro x hx
  exact ht (mem_top (⟨x, hx⟩ : R))

/-- The intersection M ∩ C_G(u) has characteristic two directly by 1.1.3(2). -/
theorem LocalControlWitness.centralizer_inter_mem_He
    (w : LocalControlWitness T M) (hM : HasCharacteristicTwo M)
    {u : G} (hu : u ∈ w.U) : M ⊓ centralizer ({u} : Set G) ∈ Chapter1.He G := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  have hUM : w.U ≤ M := w.le_twoCore.trans (pCoreIn_le _ _)
  have hp : IsPGroup 2 (zpowers u) :=
    (IsElementaryAbelian.isPGroup 2 w.U).of_injective
      (inclusion (zpowers_le.mpr hu)) (inclusion_injective _)
  change (M ⊓ centralizer ({u} : Set G)) ⊓
    centralizer ((M ⊓ centralizer ({u} : Set G)).pCoreIn 2 : Set G) ≤
      (M ⊓ centralizer ({u} : Set G)).pCoreIn 2
  simpa only [BadCentralizers.centralizer_zpowers] using
    pCoreIn_selfCentralizing_centralizer (p := 2) (Chapter1.mem_He_iff.mpr hM)
      hp (zpowers_le.mpr (hUM hu))

/-- The source O(C_G(u))=1 assertion is uniform in the original u.
It precedes, and does not assume, Sylow placement or component classification. -/
theorem LocalControlWitness.oddCore_element_centralizer_eq_bot
    (w : LocalControlWitness T M) (hM : HasCharacteristicTwo M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M)
    {u : G} (hu : u ∈ w.U) : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥ := by
  let H := centralizer ({u} : Set G)
  let R := (pPrimeCore 2 H).map H.subtype
  have hRH : R ≤ H := map_subtype_le _
  have hHN : H ≤ normalizer (R : Set G) := by
    intro x hx
    exact (pPrimeCore 2 H).le_normalizer_map H.subtype
      (mem_map_of_mem H.subtype
        (show (⟨x, hx⟩ : H) ∈ normalizer (pPrimeCore 2 H : Set H) from
          le_normalizer_of_normal (mem_top _)))
  have hcop : Nat.Coprime 2 (Nat.card R) := by
    dsimp only [R]
    rw [card_map_of_injective H.subtype_injective]
    exact pPrimeCore_coprime_card
  have hRM : R ≤ M := w.normalized_odd_subgroup_le hbad R hcop
    ((w.le_element_centralizer hu).trans hHN)
  let D := M ⊓ H
  have hRD : R ≤ D := le_inf hRM hRH
  let : (R.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRD).mpr (inf_le_right.trans hHN)
  have hDb : pPrimeCore 2 D = ⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    (Chapter1.mem_He_iff.mp (w.centralizer_inter_mem_He hM hu))
  have hcopD : Nat.Coprime 2 (Nat.card (R.subgroupOf D)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hRD).toEquiv]
  have hRb := (pPrimeCore_eq_bot_iff.mp hDb) (R.subgroupOf D) inferInstance hcopD
  have hR : R = ⊥ := by
    have he := congrArg (Subgroup.map D.subtype) hRb
    simpa only [map_subgroupOf_eq_of_le hRD, Subgroup.map_bot] using he
  exact (map_eq_bot_iff_of_injective _ H.subtype_injective).mp hR

omit [Finite G] in
/-- Any Sylow of the element centralizer containing U lies in M by (*). -/
theorem LocalControlWitness.exists_centralizer_sylow_containing
    (w : LocalControlWitness T M) {u : G} (hu : u ∈ w.U) :
    ∃ S : Sylow 2 (centralizer ({u} : Set G)),
      w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
        (centralizer ({u} : Set G)).subtype ∧
      (S : Subgroup (centralizer ({u} : Set G))).map
        (centralizer ({u} : Set G)).subtype ≤ M := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let H := centralizer ({u} : Set G)
  have hUH : w.U ≤ H := w.le_element_centralizer hu
  let : IsElementaryAbelian 2 (w.U.subgroupOf H) := IsElementaryAbelian.subgroupOf hUH
  obtain ⟨S, hS⟩ := (IsElementaryAbelian.isPGroup 2 (w.U.subgroupOf H)).exists_le_sylow
  have hUS : w.U ≤ (S : Subgroup H).map H.subtype := by
    simpa only [map_subgroupOf_eq_of_le hUH] using map_mono (f := H.subtype) hS
  exact ⟨S, hUS, (w.source_star _ (S.isPGroup'.map H.subtype) (hUS w.z_mem)).1⟩

omit [Finite G] in
/-- Fusion into M supplies strong closure in every two-overgroup of U in M,
without asserting that this overgroup lies in the fixed T. -/
theorem LocalControlWitness.strongly_closed_in_overgroup
    (w : LocalControlWitness T M) (S : Subgroup G) (hUS : w.U ≤ S) (hSM : S ≤ M) :
    IsStronglyClosedSet (w.U : Set G) S ⊤ := by
  refine ⟨hUS, ?_⟩
  intro x hx g _ hg
  have hconj : IsConj x (g⁻¹ * x * g) :=
    isConj_iff.mpr ⟨g⁻¹, by simp only [inv_inv]⟩
  have hf : ∃ m ∈ M, m⁻¹ * x * m = g⁻¹ * x * g := by
    change g⁻¹ * x * g ∈ {y : G | ∃ m ∈ M, m⁻¹ * x * m = y}
    rw [← w.conjugates_in_M x hx]
    exact ⟨hconj, hSM hg⟩
  obtain ⟨m, hm, he⟩ := hf
  rw [← he]
  change m⁻¹ * x * m ∈ w.U
  simpa only [inv_inv] using
    (mem_normalizer_iff.mp (w.normalizes (M.inv_mem hm)) x).mp hx

/-- Uniform component normalization for the original centralizers.
This uses no M-conjugation of v and no model alternative. -/
theorem LocalControlWitness.normalizes_all_element_centralizer_components
    (w : LocalControlWitness T M) (hM : HasCharacteristicTwo M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M)
    {v : G} (hv : v ∈ w.U) (L : Subgroup G)
    (hL : IsComponentIn L (centralizer ({v} : Set G))) :
    w.U ≤ normalizer (L : Set G) := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let H := centralizer ({v} : Set G)
  obtain ⟨S, hUS, hSM⟩ := w.exists_centralizer_sylow_containing hv
  let V := w.U.subgroupOf H
  let : IsMulCommutative V := w.U.comap_injective_isMulCommutative H.subtype_injective
  have hUH : w.U ≤ H := w.le_element_centralizer hv
  have hc := w.strongly_closed_in_overgroup _ hUS hSM
  have hV : IsStronglyClosedSet (V : Set H) (S : Subgroup H) ⊤ := by
    constructor
    · intro x hx
      obtain ⟨y, hy, he⟩ := hUS hx
      exact (Subtype.ext he : y = x) ▸ hy
    · intro x hx g _ hg
      exact hc.2 x hx g (mem_top _) (mem_map_of_mem H.subtype hg)
  have hn := hL.2.normalized_by_abelian_stronglyClosed_of_pPrimeCore_eq_bot
    S V (L.subgroupOf H) hV (w.oddCore_element_centralizer_eq_bot hM hbad hv)
  intro a ha
  have hNa := (L.subgroupOf H).le_normalizer_map H.subtype
    (mem_map_of_mem H.subtype (hn (show (⟨a, hUH ha⟩ : H) ∈ V from ha)))
  change a ∈ normalizer ((L.subgroupOf H).map H.subtype : Set G) at hNa
  rw [map_subgroupOf_eq_of_le hL.1] at hNa
  exact hNa

namespace BadCentralizers

private theorem conjugate_p_subgroup_le (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (P : Subgroup G) (hp : IsPGroup 2 P) (hPM : P ≤ M) :
    ∃ m : M, P.map (MulAut.conj (m : G)).toMonoidHom ≤ (T : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := (hp.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Q (T.subtype hTM)
  refine ⟨m, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxQ : (⟨x, hPM hx⟩ : M) ∈ Q := hQ hx
  have hh : m * (⟨x, hPM hx⟩ : M) * m⁻¹ ∈ (m • Q : Sylow 2 M) :=
    mem_map_of_mem (MulAut.conj m).toMonoidHom hxQ
  rw [hm] at hh
  exact hh

private noncomputable def centralizerEquiv (e : G ≃* G) (u : G) :
    centralizer ({u} : Set G) ≃* centralizer ({e u} : Set G) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (centralizer_map e u))

omit [Finite G] in
private theorem map_inverse_conjugate (K : Subgroup G) (m : G) :
    (K.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom = K := by
  rw [map_map]
  have he : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
      MonoidHom.id G := by
    ext x
    change m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x
    group
  rw [he, map_id]

end BadCentralizers

/-- The source conjugates u and S by one element of M. U and the original
z are unchanged; the equality records the actual transported Sylow image. -/
theorem LocalControlWitness.conjugate_centralizer_sylow
    (w : LocalControlWitness T M) (hTM : (T : Subgroup G) ≤ M)
    {u : G} (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype) :
    ∃ m : M, ∃ S' : Sylow 2 (centralizer ({(MulAut.conj (m : G)) u} : Set G)),
      w.U ≤ (S' : Subgroup _).map (centralizer ({(MulAut.conj (m : G)) u} : Set G)).subtype ∧
      (S' : Subgroup _).map (centralizer ({(MulAut.conj (m : G)) u} : Set G)).subtype ≤
        (T : Subgroup G) ∧
      (S' : Subgroup _).map (centralizer ({(MulAut.conj (m : G)) u} : Set G)).subtype =
        ((S : Subgroup _).map (centralizer ({u} : Set G)).subtype).map
          (MulAut.conj (m : G)).toMonoidHom := by
  let H := centralizer ({u} : Set G)
  let P := (S : Subgroup H).map H.subtype
  have hp : IsPGroup 2 P := S.isPGroup'.map H.subtype
  have hPM : P ≤ M := (w.source_star P hp (hUS w.z_mem)).1
  obtain ⟨m, hm⟩ := BadCentralizers.conjugate_p_subgroup_le T hTM P hp hPM
  let e := MulAut.conj (m : G)
  let H' := centralizer ({e u} : Set G)
  let c : H ≃* H' := BadCentralizers.centralizerEquiv e u
  let S' := S.mapSurjective (f := c.toMonoidHom) c.surjective
  have he : (S' : Subgroup H').map H'.subtype = P.map e.toMonoidHom := by
    change ((S : Subgroup H).map c.toMonoidHom).map H'.subtype = _
    rw [map_map, map_map]
    congr 1
  refine ⟨m, S', ?_, he.symm ▸ hm, he⟩
  rw [he]
  have hu := map_mono (f := e.toMonoidHom) hUS
  have hfix : w.U.map e.toMonoidHom = w.U :=
    mem_normalizer_iff_map_conj_eq.mp (w.normalizes m.property)
  rw [hfix] at hu
  exact hu

omit [Finite G] in
/-- An aligned bad centralizer cannot have characteristic two, by (*). -/
theorem LocalControlWitness.not_characteristicTwo_of_aligned_bad_centralizer
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup _).map (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup _).map (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hbad : ¬ centralizer ({u} : Set G) ≤ M) :
    ¬ HasCharacteristicTwo (centralizer ({u} : Set G)) := by
  let H := centralizer ({u} : Set G)
  intro hc
  have hzH : w.z ∈ H := (map_subtype_le _ : (S : Subgroup H).map H.subtype ≤ H)
    (hUS w.z_mem)
  have hzC : (⟨w.z, hzH⟩ : H) ∈ centralizer (pCore 2 H : Set H) := by
    intro x hx
    exact Subtype.ext (w.z_central x
      (hST (pCoreIn_le_sylow H S (mem_map_of_mem H.subtype hx)))).eq.symm
  have hzCore : w.z ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype (hc hzC)
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    intro x hx
    exact (pCore 2 H).le_normalizer_map H.subtype
      (mem_map_of_mem H.subtype
        (show (⟨x, hx⟩ : H) ∈ normalizer (pCore 2 H : Set H) from
          le_normalizer_of_normal (mem_top _)))
  exact hbad (hHN.trans (w.source_star (H.pCoreIn 2)
    ((pCore_isPGroup (p := 2) (G := H)).map H.subtype) hzCore).2)

/-- Every actual component of a U-element centralizer lies outside M. -/
theorem LocalControlWitness.component_not_le_of_element_centralizer
    (w : LocalControlWitness T M) (hM : HasCharacteristicTwo M)
    {u : G} (hu : u ∈ w.U) (L : Subgroup G)
    (hL : IsComponentIn L (centralizer ({u} : Set G))) : ¬ L ≤ M := by
  intro hLM
  let D := M ⊓ centralizer ({u} : Set G)
  have hc : HasCharacteristicTwo D :=
    Chapter1.mem_He_iff.mp (w.centralizer_inter_mem_He hM hu)
  exact not_isComponent_of_twoCore hc (L.subgroupOf D)
    (hL.restrict (le_inf hLM hL.1) inf_le_right).2

/-- A finite group with O(H)=1 and non-characteristic-two F* has a component. -/
private theorem exists_component_of_oddCore_eq_bot_not_characteristicTwo
    {H : Type*} [Group H] [Finite H] (hcore : pPrimeCore 2 H = ⊥)
    (hc : ¬ HasCharacteristicTwo H) : ∃ L : Subgroup H, IsComponent H L := by
  by_contra hn
  push Not at hn
  have he : componentLayer H = ⊥ := by
    apply sSup_eq_bot.mpr
    intro L hL
    exact (hn L hL).elim
  have hf : generalizedFitting H = pCore 2 H := by
    rw [generalizedFitting, he, sup_bot_eq, Fitting_eq_pcore H 2 hcore]
  apply hc
  change centralizer (pCore 2 H : Set H) ≤ pCore 2 H
  simpa only [hf] using centralizer_generalizedFitting_le H

omit [Finite G] in
/-- Actual components and their maximal-choice set are invariant under M. -/
theorem LocalControlWitness.bad_component_conjugate
    (w : LocalControlWitness T M) {L : Subgroup G}
    (hL : L ∈ badCentralizerComponents w) (m : M) :
    componentConjugate L m ∈ badCentralizerComponents w := by
  obtain ⟨hLM, u, hu, hu1, hc⟩ := hL
  let e := MulAut.conj (m : G)
  have hM : M.map e.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer m.property)
  have hU : w.U.map e.toMonoidHom = w.U :=
    mem_normalizer_iff_map_conj_eq.mp (w.normalizes m.property)
  refine ⟨?_, e u, ?_, ?_, ?_⟩
  · intro he
    have hh := map_mono (f := (MulAut.conj ((m : G)⁻¹)).toMonoidHom) he
    have hMi : M.map (MulAut.conj ((m : G)⁻¹)).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (M.inv_mem m.property))
    rw [BadCentralizers.map_inverse_conjugate, hMi] at hh
    exact hLM hh
  · exact hU ▸ mem_map_of_mem e.toMonoidHom hu
  · intro h
    exact hu1 (e.injective (h.trans (map_one e).symm))
  · simpa only [BadCentralizers.centralizer_map] using hc.map e

omit [Finite G] in
/-- A single M-conjugation preserves inclusion-maximality among all actual
bad-centralizer components, not just the components with an aligned Sylow. -/
theorem LocalControlWitness.maximal_bad_component_conjugate
    (w : LocalControlWitness T M) {L : Subgroup G}
    (hmax : Maximal (fun K => K ∈ badCentralizerComponents w) L) (m : M) :
    Maximal (fun K => K ∈ badCentralizerComponents w) (componentConjugate L m) := by
  refine ⟨w.bad_component_conjugate hmax.1 m, ?_⟩
  intro K hK hLK
  have hKm := w.bad_component_conjugate hK m⁻¹
  have hLKm : L ≤ componentConjugate K m⁻¹ := by
    have hh := map_mono (f := (MulAut.conj ((m : G)⁻¹)).toMonoidHom) hLK
    simpa only [BadCentralizers.map_inverse_conjugate, componentConjugate,
      Subgroup.coe_inv, MulEquiv.coe_toMonoidHom] using hh
  have he := hmax.2 hKm hLKm
  have hh := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) he
  have hinv : (componentConjugate K m⁻¹).map (MulAut.conj (m : G)).toMonoidHom = K := by
    simpa only [inv_inv, componentConjugate, Subgroup.coe_inv] using
      BadCentralizers.map_inverse_conjugate K ((m : G)⁻¹)
  exact hinv ▸ hh

/-- A bad centralizer supplies an actual component outside M, with no
classification or assumed component-existence input. -/
theorem LocalControlWitness.bad_components_nonempty
    (w : LocalControlWitness T M) (hM : HasCharacteristicTwo M)
    (hTM : (T : Subgroup G) ≤ M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M) :
    (badCentralizerComponents w).Nonempty := by
  have hbad0 := hbad
  obtain ⟨u, hu, hu1, hbadU⟩ := hbad
  obtain ⟨S, hUS, _⟩ := w.exists_centralizer_sylow_containing hu
  obtain ⟨m, S', hUS', hST', _⟩ := w.conjugate_centralizer_sylow hTM S hUS
  let e := MulAut.conj (m : G)
  let v := e u
  have hv : v ∈ w.U := by
    have he := mem_normalizer_iff_map_conj_eq.mp (w.normalizes m.property)
    exact he ▸ mem_map_of_mem e.toMonoidHom hu
  have hv1 : v ≠ 1 := by
    intro he
    exact hu1 (e.injective (he.trans (map_one e).symm))
  have hbadV : ¬ centralizer ({v} : Set G) ≤ M := by
    intro hc
    apply hbadU
    exact BadCentralizers.centralizer_le_of_conjugate m⁻¹ hc
      (by simp [v, e, MulAut.conj_apply, mul_assoc])
  let H := centralizer ({v} : Set G)
  obtain ⟨K, hK⟩ := exists_component_of_oddCore_eq_bot_not_characteristicTwo
    (w.oddCore_element_centralizer_eq_bot hM hbad0 hv)
    (w.not_characteristicTwo_of_aligned_bad_centralizer v S' hUS' hST' hbadV)
  let L := K.map H.subtype
  have hLH : L ≤ H := map_subtype_le _
  have he : L.subgroupOf H = K := by
    apply map_injective H.subtype_injective
    exact map_subgroupOf_eq_of_le hLH
  have hL : IsComponentIn L H := ⟨hLH, he.symm ▸ hK⟩
  exact ⟨L, w.component_not_le_of_element_centralizer hM hv L hL, v, hv, hv1, hL⟩

/-- Maximal source component with its genuine aligned centralizer and Sylow.
The maximal component is chosen first among all bad centralizers; only then
are it, u and the Sylow moved by the same element of M. -/
theorem LocalControlWitness.exists_maximal_bad_centralizer_data
    (w : LocalControlWitness T M) (hM : HasCharacteristicTwo M)
    (hTM : (T : Subgroup G) ≤ M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M) :
    ∃ u ∈ w.U, u ≠ 1 ∧
      ∃ S : Sylow 2 (centralizer ({u} : Set G)),
        w.U ≤ (S : Subgroup _).map (centralizer ({u} : Set G)).subtype ∧
        (S : Subgroup _).map (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G) ∧
        pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥ ∧
        ∃ L : Subgroup G, IsComponentIn L (centralizer ({u} : Set G)) ∧
          Maximal (fun K => K ∈ badCentralizerComponents w) L := by
  obtain ⟨L, hmax⟩ := exists_maximal_badCentralizerComponent w
    (w.bad_components_nonempty hM hTM hbad)
  obtain ⟨u, hu, hu1, hL⟩ := hmax.1.2
  obtain ⟨S, hUS, _⟩ := w.exists_centralizer_sylow_containing hu
  obtain ⟨m, S', hUS', hST', _⟩ := w.conjugate_centralizer_sylow hTM S hUS
  let e := MulAut.conj (m : G)
  have hv : e u ∈ w.U :=
    (mem_normalizer_iff_map_conj_eq.mp (w.normalizes m.property)) ▸
      mem_map_of_mem e.toMonoidHom hu
  have hv1 : e u ≠ 1 := fun he => hu1 (e.injective (he.trans (map_one e).symm))
  refine ⟨e u, hv, hv1, S', hUS', hST',
    w.oddCore_element_centralizer_eq_bot hM hbad hv,
    componentConjugate L m, ?_, w.maximal_bad_component_conjugate hmax m⟩
  simpa only [BadCentralizers.centralizer_map] using hL.map e

/-- Source 1.1.6 applies to the literal aligned involution centralizer, using
the original distinguished z and the existing even-characteristic hypothesis. -/
theorem LocalControlWitness.lemma115_of_aligned_element_centralizer
    (w : LocalControlWitness T M) {K : GroupClass} (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M) {u : G} (hu : u ∈ w.U) (hu1 : u ≠ 1)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hST : (S : Subgroup _).map (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G)) :
    Chapter1.Lemma115Hypotheses (centralizer ({u} : Set G)) S M w.z := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let H := centralizer ({u} : Set G)
  let B := zpowers u
  have hBne : B ≠ ⊥ := fun he => hu1 (mem_bot.mp (he ▸ mem_zpowers u))
  have hp : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 w.U).of_injective
    (inclusion (zpowers_le.mpr hu)) (inclusion_injective _)
  have hBH : B ≤ H := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCH : centralizer (B : Set G) ≤ H := by
    rw [BadCentralizers.centralizer_zpowers]
  have hHN : H ≤ normalizer (B : Set G) := by
    dsimp only [H, B]
    rw [← BadCentralizers.centralizer_zpowers u]
    exact Subgroup.centralizer_le_normalizer _
  exact Chapter1.lemma_1_1_6 hBne hp hBH hCH hHN S T hST w.z_order
    (w.le_sylow w.z_mem) (fun t ht => (w.z_central t ht).eq.symm)
    hM w.centralizer_le
    (fun N hN hTN => Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T N hN hTN))

end CFSG.Quasithin.Chapter2.BenderFusion
