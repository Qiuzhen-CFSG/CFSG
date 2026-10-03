module

public import Stellmacher.Recognition.Parrott.OuterOmegaTransport
public import Stellmacher.Recognition.Parrott.OuterQuotientConjugacy

/-!
# The derived-core suborbits in outer elementary thirty-two

The derived core E has order thirty-two and fixes eight elements at each
outer involution. It normalizes X by the omega transporter lemma, so its
orbits on outer points of X have order four. A Sylow conjugate in a second
E-coset gives two disjoint such orbits in the Sylow-normalizer orbit.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.674–676, especially the quotient-conjugacy argument on p.676.
-/

open Subgroup MulAction
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The derived-core normalizer suborbit of an outer point has four elements. -/
public theorem outer_elementary_derived_suborbit_card
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let N := normalizer (X : Set G)
    ∀ x : X, (x : G) ∉ (pCore 2 H).map H.subtype →
      Nat.card (orbit (E.subgroupOf N) x) = 4 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let N := normalizer (X : Set G)
  let B := E.subgroupOf N
  change ∀ x : X, (x : G) ∉ J.map H.subtype → Nat.card (orbit B x) = 4
  intro x hxJ
  have hEN := d.derived_le_outer_elementary_normalizer h X hXT hX x x.property hxJ
  let xH : H := ⟨x, d.sylow_le_centralizer (hXT x.property)⟩
  have hx2 : orderOf xH = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property)
      (fun hh => hxJ (hh ▸ one_mem _))
  have hxHJ : xH ∉ J := fun hh => hxJ (mem_map_of_mem H.subtype hh)
  have hgeom := parrott_outer_fixed_join_geometry z h xH hx2 hxHJ
  have hEcard : Nat.card E = 32 := hgeom.1
  let Z := E ⊓ centralizer ({(x : G)} : Set G)
  have hZcard : Nat.card Z = 8 := hgeom.2.1
  have hBcard : Nat.card B = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans hEcard
  let S := stabilizer B x
  let f : B →* G := N.subtype.comp B.subtype
  have hf : Function.Injective f := N.subtype_injective.comp B.subtype_injective
  have hSmap : S.map f = Z := by
    apply le_antisymm
    · rintro g ⟨b, hb, rfl⟩
      refine ⟨b.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have hh := congrArg (fun v : X => (v : G)) (mem_stabilizer_iff.mp hb)
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro g hg
      let b : B := ⟨⟨g, hEN hg.1⟩, hg.1⟩
      refine ⟨b, mem_stabilizer_iff.mpr ?_, rfl⟩
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg.2))
  have hScard : Nat.card S = 8 := by
    have hh := card_map_of_injective (K := S) (f := f) hf
    rw [hSmap] at hh
    exact hh.symm.trans hZcard
  have hc := S.index_mul_card
  rw [show S.index = Nat.card (orbit B x) from index_stabilizer B x, hScard, hBcard] at hc
  omega

/-- A Sylow conjugate in a second derived-core coset gives the lower bound
of eight for the actual Sylow-normalizer action. -/
public theorem eight_le_outer_suborbit_of_second_coset
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let T : Subgroup G := d.sylow
    let N := normalizer (X : Set G)
    let A := T.subgroupOf N
    ∀ x : X, (x : G) ∉ (pCore 2 H).map H.subtype →
      (∃ t ∈ T, t * (x : G) * t⁻¹ ∈ X ∧
        (x : G)⁻¹ * (t * (x : G) * t⁻¹) ∉ E) →
      8 ≤ Nat.card (orbit A x) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let K := J.map H.subtype
  let DH := (commutator J).map J.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let T : Subgroup G := d.sylow
  let N := normalizer (X : Set G)
  let A := T.subgroupOf N
  let B := E.subgroupOf N
  change ∀ x : X, (x : G) ∉ K → _ → 8 ≤ Nat.card (orbit A x)
  intro x hxJ ⟨t, ht, htx, hne⟩
  have hET : E ≤ T := by
    change E ≤ (d.sylow : Subgroup G)
    dsimp only [E]
    rw [d.sylow_map, ← map_map]
    exact map_mono ((map_subtype_le (commutator J)).trans
      (pCore_isPGroup.le_sylow_of_normal d.localSylow))
  have htN := d.outer_elementary_transporter_mem_normalizer h X hXT hX x x.property hxJ t ht htx
  let tA : A := ⟨⟨t, htN⟩, ht⟩
  let x' : X := ⟨t * (x : G) * t⁻¹, htx⟩
  have hxx' : x' ∈ orbit A x := ⟨tA, rfl⟩
  have hx'J : (x' : G) ∉ K := by
    have htK : t ∈ normalizer (K : Set G) := by
      apply le_normalizer_map H.subtype
      exact mem_map_of_mem H.subtype
        (show (⟨t, d.sylow_le_centralizer ht⟩ : H) ∈ normalizer (J : Set H) by
          rw [normalizer_eq_top]; trivial)
    exact fun hh => hxJ ((mem_normalizer_iff.mp htK x).mpr hh)
  have hxE : (x : G) ∈ normalizer (E : Set G) := by
    dsimp only [E]
    rw [← map_map]
    apply le_normalizer_map H.subtype
    exact mem_map_of_mem H.subtype
      (show (⟨x, d.sylow_le_centralizer (hXT x.property)⟩ : H) ∈
          normalizer (DH : Set H) by rw [normalizer_eq_top]; trivial)
  have hx'B : x' ∉ orbit B x := by
    rintro ⟨b, hb⟩
    have heq := congrArg (fun v : X => (v : G)) hb
    change ((b : N) : G) * (x : G) * ((b : N) : G)⁻¹ = (x' : G) at heq
    apply hne
    change (x : G)⁻¹ * (x' : G) ∈ E
    rw [← heq]
    have hh := E.mul_mem ((mem_normalizer_iff''.mp hxE ((b : N) : G)).mp b.property)
      (E.inv_mem b.property)
    change ((x : G)⁻¹ * ((b : N) : G) * (x : G)) * ((b : N) : G)⁻¹ ∈ E at hh
    simpa only [mul_assoc] using hh
  have hdisj : Disjoint (orbit B x) (orbit B x') := by
    apply Set.disjoint_left.mpr
    intro v hv hv'
    have h₁ : orbit B v = orbit B x := orbit_eq_iff.mpr hv
    have h₂ : orbit B v = orbit B x' := orbit_eq_iff.mpr hv'
    exact hx'B (orbit_eq_iff.mp (h₂.symm.trans h₁))
  have hsub (v : X) : orbit B v ⊆ orbit A v := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨(b : N), hET b.property⟩, rfl⟩
  have hbig : orbit B x ∪ orbit B x' ⊆ orbit A x := by
    apply Set.union_subset (hsub x)
    rw [← orbit_eq_iff.mpr hxx']
    exact hsub x'
  have hfour := d.outer_elementary_derived_suborbit_card h X hXT hX x hxJ
  have hfour' := d.outer_elementary_derived_suborbit_card h X hXT hX x' hx'J
  have hcount := Set.ncard_le_ncard hbig
  rw [Set.ncard_union_eq hdisj, show (orbit B x).ncard = 4 from hfour,
    show (orbit B x').ncard = 4 from hfour'] at hcount
  exact hcount

/-- Every outer point has a Sylow conjugate in a second derived-core coset
inside the same elementary subgroup. -/
public theorem outer_elementary_second_coset
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32)
    (x : G) (hx : x ∈ X)
    (hxJ : x ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    ∃ t ∈ (d.sylow : Subgroup G), t * x * t⁻¹ ∈ X ∧
      x⁻¹ * (t * x * t⁻¹) ∉ E := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let K := J.map H.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  obtain ⟨a, haX, haK, haE⟩ :=
    d.outer_elementary_exists_core_not_derived h X hXT hX x hx hxJ
  let xH : H := ⟨x, d.sylow_le_centralizer (hXT hx)⟩
  let aH : H := ⟨a, d.sylow_le_centralizer (hXT haX)⟩
  have haJ : aH ∈ J := by
    obtain ⟨b, hb, heq⟩ := haK
    exact (show b = aH from H.subtype_injective heq) ▸ hb
  have hxHJ : xH ∉ J := fun hh => hxJ (mem_map_of_mem H.subtype hh)
  have hx2 : orderOf xH = 2 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf x = 2
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx)
      (fun hh => hxJ (hh ▸ one_mem _))
  have hax : Commute aH xH := Subtype.ext (congrArg X.subtype
    (mul_comm (⟨a, haX⟩ : X) ⟨x, hx⟩))
  obtain ⟨t, ht⟩ := parrott_outer_quotient_conjugacy z h xH hx2 hxHJ aH haJ hax
  let b : G := H.subtype (t : H)
  let v : G := b * x * b⁻¹
  have hcos : (x * a)⁻¹ * v ∈ E := by
    have hh := mem_map_of_mem H.subtype ht
    simpa only [E, J, H, xH, aH, v, b, map_map, map_mul, map_inv, subtype_apply] using hh
  have hbT : b ∈ (d.sylow : Subgroup G) := by
    rw [d.sylow_map]
    exact mem_map_of_mem H.subtype
      (pCore_isPGroup.le_sylow_of_normal d.localSylow t.property)
  have hxaK : x * a ∉ K := by
    intro hh
    exact hxJ ((mul_mem_cancel_right haK).mp hh)
  have hv2 : v ^ 2 = 1 := by
    change ((MulAut.conj b) x) ^ 2 = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian x hx, map_one]
  have hvX : v ∈ X := d.outer_elementary_involution_coset_mem h X hXT hX
    (x * a) (X.mul_mem hx haX) hxaK v hv2 hcos
  refine ⟨b, hbT, hvX, ?_⟩
  intro hvE
  apply haE
  have heq : a = (x⁻¹ * v) * ((x * a)⁻¹ * v)⁻¹ := by group
  rw [heq]
  exact E.mul_mem hvE (E.inv_mem hcos)

/-- Every outer point of an elementary thirty-two has at least eight points
in its Sylow-normalizer orbit. No fusion assumption on the point is needed. -/
public theorem eight_le_outer_elementary_suborbit
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32) :
    let H := centralizer ({z} : Set G)
    let N := normalizer (X : Set G)
    let U := ((pCore 2 H).map H.subtype).subgroupOf X
    let A := (d.sylow : Subgroup G).subgroupOf N
    ∀ x : X, x ∉ U → 8 ≤ Nat.card (orbit A x) := by
  dsimp only
  intro x hx
  exact d.eight_le_outer_suborbit_of_second_coset h X hXT hX x hx
    (d.outer_elementary_second_coset h X hXT hX x x.property hx)

/-- The actual elementary outer omega of order thirty-two has outer
Sylow-normalizer suborbits of size at least eight. -/
public theorem eight_le_outer_omega_suborbit
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G)) :
    let H := centralizer ({z} : Set G)
    let T : Subgroup G := d.sylow
    let yT : T := ⟨y, hyT⟩
    let Q := centralizer ({yT} : Set T)
    let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
    let N := normalizer (X : Set G)
    let U := ((pCore 2 H).map H.subtype).subgroupOf X
    let A := T.subgroupOf N
    IsElementaryAbelian 2 X → Nat.card X = 32 →
      ∀ x : X, x ∉ U → 8 ≤ Nat.card (orbit A x) := by
  let T : Subgroup G := d.sylow
  let yT : T := ⟨y, hyT⟩
  let Q := centralizer ({yT} : Set T)
  let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
  dsimp only
  intro hElem hX x hx
  let : IsElementaryAbelian 2 X := hElem
  have hXT : X ≤ T := by
    rintro _ ⟨w, _, rfl⟩
    exact (w : T).property
  exact d.eight_le_outer_elementary_suborbit h X hXT hX x hx

/-- The actual outer omega has eight- or sixteen-element Sylow-normalizer
suborbits outside the core when its order is thirty-two. -/
public theorem outer_omega_suborbit_eq_eight_or_sixteen
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G))
    (hyJ : y ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hy : orderOf y = 2) :
    let H := centralizer ({z} : Set G)
    let T : Subgroup G := d.sylow
    let yT : T := ⟨y, hyT⟩
    let Q := centralizer ({yT} : Set T)
    let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
    let N := normalizer (X : Set G)
    let U := ((pCore 2 H).map H.subtype).subgroupOf X
    let A := T.subgroupOf N
    IsElementaryAbelian 2 X → Nat.card X = 32 →
      ∀ x : X, x ∉ U →
        Nat.card (orbit A x) = 8 ∨ Nat.card (orbit A x) = 16 := by
  let T : Subgroup G := d.sylow
  let yT : T := ⟨y, hyT⟩
  let Q := centralizer ({yT} : Set T)
  let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
  dsimp only
  intro hElem hX x hx
  have hU := d.outer_omega_core_card_of_card_thirtyTwo h y hyT hyJ hy hX
  exact d.outer_suborbit_eq_eight_or_sixteen_of_eight_le X hX hU x hx
    (d.eight_le_outer_omega_suborbit h y hyT hElem hX x hx)

end Stellmacher.Recognition.ParrottSecondElementaryData
