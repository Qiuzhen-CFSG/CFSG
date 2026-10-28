module
public import Stellmacher.Recognition.Parrott.OuterInvolutionFixedSpace
public import Theory.GroupTheory.SpecificGroups.FiveFourInvolutionCentralizer
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Join

/-!
# Omega of an outer involution centralizer in Parrott's local group

Put H=C_G(z), J=O₂(H), and let E be the actual derived image in G.
Assume every involution of the mapped core lies in E. For an involution
y in H outside J, its centralizer P in H is a two-group. The actual
ambient image X of Ω₁(P) equals <y> joined with E∩C_G(y), and is elementary
abelian of order16. No N₂ or simplicity hypothesis is needed.

The two-group conclusion and the elementary fixed join of order sixteen
inside omega are also exposed independently, without the core-involution
premise, for the fusion argument in Lemma 5.

The projection of P to the supplied faithful C5 semidirect C4 model lies
in the cyclic order4 centralizer of the image of y; its kernel lies in J.
This proves P is a two-group. Every involution of P maps either to the
identity or to the unique involution in that cyclic centralizer. Hence
either the involution or its product with y is a core involution, and so
lies in E∩C_G(y). This identifies the omega subgroup. The fixed-space
result gives |E∩C_G(y)|=8, and y is an external commuting involution,
giving an elementary direct product of order16.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 3, p.675. The displayed involution premise is precisely that
lemma's contradiction assumption. The core, centralizer, omega subgroup,
quotient model, and ambient maps are the original constructions.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition

/-- The centralizer in H of an outer involution is a two-group, independently
of which involutions occur in the core. -/
public theorem parrott_outer_centralizer_isPGroup
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z)
    (y : centralizer ({z} : Set G)) (hy : orderOf y = 2)
    (hyJ : y ∉ pCore 2 (centralizer ({z} : Set G))) :
    IsPGroup 2 (centralizer ({y} : Set (centralizer ({z} : Set G)))) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let P := centralizer ({y} : Set H)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let f := e.toMonoidHom.comp (QuotientGroup.mk' J)
  have hker : f.ker = J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hfy : orderOf (f y) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hy2, map_one]
    · intro heq
      have hyker : y ∈ f.ker := heq
      rw [hker] at hyker
      exact hyJ hyker
  let C := centralizer ({f y} : Set _)
  have hCp : IsPGroup 2 C := IsPGroup.of_card (n := 2)
    (faithful_five_four_involution_centralizer φ hφ (f y) hfy).2
  have hpre : IsPGroup 2 (C.comap f) :=
    hCp.comap_of_ker_isPGroup f (by rw [hker]; exact pCore_isPGroup)
  have hle : P ≤ C.comap f := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp ha)
  exact hpre.of_injective (inclusion hle) (inclusion_injective hle)

/-- The centralizer of an outer involution lies in each supplied Sylow
two-subgroup containing it. This identifies the local centralizers in H and T. -/
public theorem parrott_outer_centralizer_le_sylow
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z)
    (y : centralizer ({z} : Set G)) (hy : orderOf y = 2)
    (hyJ : y ∉ pCore 2 (centralizer ({z} : Set G)))
    (T : Sylow 2 (centralizer ({z} : Set G))) (hyT : y ∈ (T : Subgroup _)) :
    centralizer ({y} : Set (centralizer ({z} : Set G))) ≤ (T : Subgroup _) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let M := Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let f := e.toMonoidHom.comp (QuotientGroup.mk' J)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective J)
  change y ∉ J at hyJ
  have hker : f.ker = J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hfy : orderOf (f y) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, show y ^ 2 = 1 from hy ▸ pow_orderOf_eq_one y, map_one]
    · intro heq
      exact hyJ (hker ▸ (show y ∈ f.ker from heq))
  let C := centralizer ({f y} : Set M)
  have hCp : IsPGroup 2 C := IsPGroup.of_card (n := 2)
    (faithful_five_four_involution_centralizer φ hφ (f y) hfy).2
  have hpre : IsPGroup 2 (C.comap f) :=
    hCp.comap_of_ker_isPGroup f (by rw [hker]; exact pCore_isPGroup)
  let S : Sylow 2 M := T.mapSurjective hf
  have hM : Nat.card M = 20 := by rw [SemidirectProduct.card]; norm_num
  have hS : Nat.card S = 4 := by
    rw [S.card_eq_multiplicity, hM]
    decide +kernel
  let : IsMulCommutative S :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hS)
  have hmem (a : H) (ha : a ∈ (T : Subgroup H)) : f a ∈ (S : Subgroup M) :=
    mem_map_of_mem f ha
  have hTpre : (T : Subgroup H) ≤ C.comap f := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm
      (⟨f a, hmem a ha⟩ : S) (⟨f y, hmem y hyT⟩ : S))
  have heq : C.comap f = (T : Subgroup H) := T.is_maximal' hpre hTpre
  rw [← heq]
  intro a ha
  apply mem_centralizer_singleton_iff.mpr
  simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp ha)

/-- Every outer involution supplies an elementary fixed join of order sixteen
inside the actual omega subgroup; no restriction on core involutions is needed. -/
public theorem parrott_outer_fixed_join_data
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ y : H, orderOf y = 2 → y ∉ J →
      let P := centralizer ({y} : Set H)
      let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
      let Z := E ⊓ centralizer ({(y : G)} : Set G)
      let X₀ := zpowers (y : G) ⊔ Z
      IsElementaryAbelian 2 X₀ ∧ Nat.card X₀ = 16 ∧ X₀ ≤ X := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change ∀ y : H, orderOf y = 2 → y ∉ J → _
  intro y hy hyJ
  let P := centralizer ({y} : Set H)
  let embed : P →* G := H.subtype.comp P.subtype
  let X := (omega₁ P (p := 2)).map embed
  let Z := E ⊓ centralizer ({(y : G)} : Set G)
  let Y := zpowers (y : G)
  let X₀ := Y ⊔ Z
  change IsElementaryAbelian 2 X₀ ∧ Nat.card X₀ = 16 ∧ X₀ ≤ X
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hyG2 : (y : G) ^ 2 = 1 := congrArg Subtype.val hy2
  have hEy : (y : G) ∉ E := by
    rintro ⟨d, hd, he⟩
    have hh : (d : H) = y := H.subtype_injective he
    exact hyJ (hh ▸ d.property)
  obtain ⟨_, _, _, _, _, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEH : E ≤ H := by
    rintro x ⟨d, _, rfl⟩
    exact (d : H).property
  let : IsElementaryAbelian 2 Z := {
    toIsMulCommutative := isMulCommutative_iff.mpr (by
      intro a b
      exact Subtype.ext (congrArg (fun x : E => (x : G)) (mul_comm
        (⟨(a : G), a.property.1⟩ : E) (⟨(b : G), b.property.1⟩ : E))))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property.1)) }
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.zpowers_of_pow_eq_one hyG2
  have hyCZ : (y : G) ∈ centralizer (Z : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mp ha.2
  have hZY : Z ≤ centralizer (Y : Set G) :=
    le_centralizer_iff.mpr (zpowers_le.mpr hyCZ)
  let : IsElementaryAbelian 2 X₀ := IsElementaryAbelian.sup_of_le_centralizer hZY
  have hZcard : Nat.card Z = 8 := by
    have hc := parrott_outer_involution_fixed_card z h y hy hyJ
    have hh := card_map_of_injective
      (K := (centralizer ({(y : G)} : Set G)).subgroupOf E) (f := E.subtype) E.subtype_injective
    rw [subgroupOf_map_subtype] at hh
    have hh' : Nat.card Z = Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) := by
      simpa only [Z, inf_comm] using hh
    exact hh'.trans hc
  have hX₀card : Nat.card X₀ = 16 := by
    have hh := card_sup_zpowers_of_normalizing_involution Z (y : G) hyG2
      (fun hyZ => hEy hyZ.1) (centralizer_le_normalizer _ hyCZ)
    simpa only [X₀, Y, sup_comm, hZcard] using hh
  let yP : P := ⟨y, mem_centralizer_singleton_iff.mpr rfl⟩
  have hmap_mem (a : P) (ha : a ^ 2 = 1) : embed a ∈ X := by
    apply mem_map_of_mem
    exact subset_closure (by simpa only [Set.mem_ofPred_eq, pow_one] using ha)
  have hleX : X₀ ≤ X := by
    apply sup_le
    · apply zpowers_le.mpr
      exact hmap_mem yP (Subtype.ext hy2)
    · intro a ha
      let aH : H := ⟨a, hEH ha.1⟩
      let aP : P := ⟨aH, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp ha.2))⟩
      exact hmap_mem aP (Subtype.ext (Subtype.ext
        (elemPow_eq_one_of_isElementaryAbelian a ha.1)))
  exact ⟨inferInstance, hX₀card, hleX⟩

/-- Under the core-involution negation, the outer centralizer has elementary omega of order16. -/
public theorem parrott_outer_centralizer_omega
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ y : H, orderOf y = 2 → y ∉ J →
      let P := centralizer ({y} : Set H)
      let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
      let Z := E ⊓ centralizer ({(y : G)} : Set G)
      IsPGroup 2 P ∧ X = zpowers (y : G) ⊔ Z ∧ IsElementaryAbelian 2 X ∧ Nat.card X = 16 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) → _
  intro hcore y hy hyJ
  let P := centralizer ({y} : Set H)
  let embed : P →* G := H.subtype.comp P.subtype
  let X := (omega₁ P (p := 2)).map embed
  let Z := E ⊓ centralizer ({(y : G)} : Set G)
  let Y := zpowers (y : G)
  let X₀ := Y ⊔ Z
  change IsPGroup 2 P ∧ X = X₀ ∧ IsElementaryAbelian 2 X ∧ Nat.card X = 16
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hyG2 : (y : G) ^ 2 = 1 := congrArg Subtype.val hy2
  obtain ⟨hX₀elem, hX₀card, hleX⟩ := parrott_outer_fixed_join_data z h y hy hyJ
  let : IsElementaryAbelian 2 X₀ := hX₀elem
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let M := Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)
  let : Finite M := Finite.of_equiv (Multiplicative (ZMod 5) × Multiplicative (ZMod 4))
    SemidirectProduct.equivProd.symm
  let modelHom := e.toMonoidHom.comp (QuotientGroup.mk' J)
  let ybar := modelHom y
  have hybar : orderOf ybar = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hy2, map_one]
    · intro heq
      change e (QuotientGroup.mk' J y) = 1 at heq
      have hq : QuotientGroup.mk' J y = 1 := e.injective (by simpa only [map_one] using heq)
      exact hyJ ((QuotientGroup.eq_one_iff (N := J) y).mp hq)
  let C := centralizer ({ybar} : Set _)
  obtain ⟨hCcyc, _⟩ := faithful_five_four_involution_centralizer φ hφ ybar hybar
  let : IsCyclic C := hCcyc
  let π : P →* C := (modelHom.comp P.subtype).codRestrict C (by
    intro a
    apply mem_centralizer_singleton_iff.mpr
    change modelHom (a : H) * modelHom y = modelHom y * modelHom (a : H)
    simpa only [map_mul] using congrArg modelHom (mem_centralizer_singleton_iff.mp a.property))
  have hkerJ (a : P) (ha : π a = 1) : (a : H) ∈ J := by
    apply (QuotientGroup.eq_one_iff (N := J) (a : H)).mp
    change QuotientGroup.mk' J (a : H) = 1
    apply e.injective
    change e (QuotientGroup.mk' J (a : H)) = e 1
    have hh := congrArg Subtype.val ha
    change e (QuotientGroup.mk' J (a : H)) = 1 at hh
    simpa only [map_one] using hh
  have hPp : IsPGroup 2 P := parrott_outer_centralizer_isPGroup z h y hy hyJ
  let yP : P := ⟨y, mem_centralizer_singleton_iff.mpr rfl⟩
  have hyπ : orderOf (π yP) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hybar
  have hcorePow (a : P) (ha : a ^ 2 = 1) (haJ : (a : H) ∈ J) : embed a ∈ E := by
    by_cases heq : embed a = 1
    · exact heq ▸ E.one_mem
    · exact hcore (embed a) (mem_map_of_mem H.subtype haJ)
        (orderOf_eq_prime (congrArg embed ha) heq)
  have hXle : X ≤ X₀ := by
    apply (map_le_iff_le_comap).mpr
    change closure {a : P | a ^ (2 ^ 1) = 1} ≤ X₀.comap embed
    refine (closure_le _).mpr ?_
    intro a ha
    have ha2 : a ^ 2 = 1 := by simpa only [Set.mem_ofPred_eq, pow_one] using ha
    change embed a ∈ X₀
    by_cases haπ : π a = 1
    · exact (le_sup_right : Z ≤ X₀) ⟨hcorePow a ha2 (hkerJ a haπ),
        mem_centralizer_singleton_iff.mpr (congrArg H.subtype (mem_centralizer_singleton_iff.mp a.property))⟩
    · have hae : π a = π yP := IsCyclic.eq_of_orderOf_eq_two
        (orderOf_eq_prime (by rw [← map_pow, ha2, map_one]) haπ) hyπ
      have hap : (a * yP) ^ 2 = 1 := by
        apply Subtype.ext
        have hc : Commute (a : H) y := mem_centralizer_singleton_iff.mp a.property
        change ((a : H) * y) ^ 2 = 1
        rw [hc.mul_pow, hy2, mul_one]
        exact congrArg Subtype.val ha2
      have haj : ((a * yP : P) : H) ∈ J := hkerJ _ (by
        rw [map_mul, hae]
        have hh : (π yP) ^ 2 = 1 := by
          rw [← hyπ]
          exact pow_orderOf_eq_one (π yP)
        simpa only [pow_two] using hh)
      have haz : embed (a * yP) ∈ Z :=
        ⟨hcorePow _ hap haj, mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp (a * yP).property))⟩
      have hprod := X₀.mul_mem ((le_sup_right : Z ≤ X₀) haz)
        ((le_sup_left : Y ≤ X₀) (mem_zpowers (y : G)))
      change (embed a * (y : G)) * (y : G) ∈ X₀ at hprod
      simpa only [mul_assoc, ← pow_two, hyG2, mul_one] using hprod
  have hX : X = X₀ := le_antisymm hXle hleX
  exact ⟨hPp, hX, by rw [hX]; infer_instance, by rw [hX]; exact hX₀card⟩

end Stellmacher.Recognition
