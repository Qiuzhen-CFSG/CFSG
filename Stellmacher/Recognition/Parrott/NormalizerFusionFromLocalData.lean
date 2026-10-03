module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeCyclic
public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOrder
public import Stellmacher.Recognition.Parrott.DerivedConjugacyCensus
public import Theory.GroupTheory.SylowElementConjugacy
public import Stellmacher.Recognition.Parrott.SecondNormalizerTransport
public import Stellmacher.Recognition.Parrott.NormalizerElementaryFusion
public import Stellmacher.Recognition.Parrott.NormalizerOuterFusion

/-!
# Local assembly for Parrott's normalizer fusion

Let H=C_G(z), J=O₂(H), E=J′ in G, and N=N_G(F) for the supplied
second elementary subgroup. The fixed involution supplied by the caller
is the unique nonidentity element of C_F(Q), so it agrees with the
compatible center generators. The proved derived order and the explicit
containment C_X(Q)≤X′ then supply the order-four generator with square v.

The two H-classes in E outside ⟨z⟩ can be represented by the compatible
t and v: fusion of t with z and nonfusion of v with z separate them.
This gives conjugators in H∨N for every involution in E. Transport of
fixed joins moves any core involution outside E into the supplied F,
still outside E. Thus fusion in F outside Z(X), together with transport
of outer Sylow involutions into E, completes Sylow fusion in H∨N.
Sylow conjugacy then supplies ambient completeness.

The final assembly discharges the elementary and outer fusion calculations
using the corresponding local modules. Normalizer growth and the containment
C_X(Q)≤X′ remain supplied inputs, not conclusions of this module.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), pp.677–678; fixed-join transport uses pp.674–675.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem involution_eq_of_mem_zpowers {v w : G}
    (hv : orderOf v = 2) (hw : orderOf w = 2) (hm : w ∈ zpowers v) : w = v := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hv] at hm
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hm
  have hnlt := Finset.mem_range.mp hn
  interval_cases n
  · have hw1 : w = 1 := by simpa using heq.symm
    simp [hw1] at hw
  · simpa using heq.symm

/-- Compatible central and cyclic generators for the prescribed fixed involution. -/
public theorem normalizer_fusion_generators
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let U := omega₁ K (p := 2)
    let A := (Q : Subgroup N).map N.subtype
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∃ t b : G, t ∈ E ⊓ d.F ∧ v ∈ E ⊓ d.F ∧
      orderOf t = 2 ∧ t ∉ zpowers z ∧ v ∉ ZK ∧
      ZK = zpowers z ⊔ zpowers t ∧ ZU = (zpowers z ⊔ zpowers t) ⊔ zpowers v ∧
      (∃ q : Q, ((q : N) : G) * z * ((q : N) : G)⁻¹ = t) ∧
      v ∈ centralizer (A : Set G) ∧ ZU ⊓ centralizer (A : Set G) = zpowers v ∧
      ¬ IsConj z v ∧ b ∈ X ∧ orderOf b = 4 ∧ b ^ 2 = v ∧
      X ⊓ centralizer (A : Set G) = zpowers b := by
  intro H J E N K X D U A ZK ZU hCD v hv hfix
  obtain ⟨t, w, ht, hw, ht2, hw2, htz, hwZ, hZK, hZU, hq, hwC, hwfix, _, hnc⟩ :=
    d.exists_normalizer_three_fixed_generators h hN hproper Q
  have hwv : w = v := involution_eq_of_mem_zpowers hv hw2 (hfix ▸ ⟨hw.2, hwC⟩)
  subst w
  obtain ⟨b, hb, hb4, hb2, hbC⟩ :=
    d.exists_normalizer_three_cyclic_generator_of_derived_calculations h hN hproper Q
      (d.normalizer_core_derived_order h hN hproper) hCD v hv hfix
  exact ⟨t, b, ht, hw, ht2, htz, hwZ, hZK, hZU, hq, hwC, hwfix,
    hnc, hb, hb4, hb2, hbC⟩

omit [Finite G] in
private theorem local_conj_trans (H : Subgroup G) {x y w : G}
    (hxy : ∃ a : H, (a : G) * x * (a : G)⁻¹ = y)
    (hyw : ∃ a : H, (a : G) * y * (a : G)⁻¹ = w) :
    ∃ a : H, (a : G) * x * (a : G)⁻¹ = w := by
  obtain ⟨a, rfl⟩ := hxy
  obtain ⟨b, hb⟩ := hyw
  exact ⟨b * a, by simpa only [coe_mul, mul_inv_rev, mul_assoc] using hb⟩

omit [Finite G] in
private theorem local_conj_symm (H : Subgroup G) {x y : G}
    (hxy : ∃ a : H, (a : G) * x * (a : G)⁻¹ = y) :
    ∃ a : H, (a : G) * y * (a : G)⁻¹ = x := by
  obtain ⟨a, rfl⟩ := hxy
  exact ⟨a⁻¹, by simp [mul_assoc]⟩

/-- Any nonconjugate pair of noncentral elements in the derived core represents
its two local classes; the conjugators remain in the original centralizer. -/
public theorem derived_fusion_of_distinct_representatives
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t v : G, t ∈ E → t ∉ zpowers z → v ∈ E → v ∉ zpowers z →
      ¬ IsConj t v → ∀ u : G, u ∈ E → u ∉ zpowers z →
      (∃ a : H, (a : G) * t * (a : G)⁻¹ = u) ∨
      (∃ a : H, (a : G) * v * (a : G)⁻¹ = u) := by
  intro H J E t v ht htz hv hvz htv u hu huz
  obtain ⟨x, y, _, _, _, _, _, _, hc⟩ := parrott_derived_conjugacy_census z h
  have hne (w : G)
      (hwt : ∃ a : H, (a : G) * w * (a : G)⁻¹ = t)
      (hwv : ∃ a : H, (a : G) * w * (a : G)⁻¹ = v) : False := by
    obtain ⟨a, ha⟩ := local_conj_trans H (local_conj_symm H hwt) hwv
    exact htv (isConj_iff.mpr ⟨(a : G), ha⟩)
  rcases hc t ht htz with hxt | hyt <;> rcases hc v hv hvz with hxv | hyv
  · exact (hne x hxt hxv).elim
  · rcases hc u hu huz with hxu | hyu
    · exact Or.inl (local_conj_trans H (local_conj_symm H hxt) hxu)
    · exact Or.inr (local_conj_trans H (local_conj_symm H hyv) hyu)
  · rcases hc u hu huz with hxu | hyu
    · exact Or.inr (local_conj_trans H (local_conj_symm H hxv) hxu)
    · exact Or.inl (local_conj_trans H (local_conj_symm H hyt) hyu)
  · exact (hne y hyt hyv).elim


/-- Every involution in the original derived core is reached from z or the
prescribed fixed involution by a conjugator in the join of the two normalizers. -/
public theorem derived_involution_fusion_in_join
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let L := H ⊔ normalizer (d.F : Set G)
    ¬ IsConj z v ∧ ∀ u : G, u ∈ E → orderOf u = 2 →
      ∃ l : L, (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u := by
  intro H J E L
  obtain ⟨t, w, ht, hw, _, hw2, htz, _, _, _, ⟨q, hq⟩, hwC, _, _, hnc⟩ :=
    d.exists_normalizer_three_fixed_generators h hN hproper Q
  have hwv : w = v := involution_eq_of_mem_zpowers hv hw2 (hfix ▸ ⟨hw.2, hwC⟩)
  subst w
  have hzt : IsConj z t := isConj_iff.mpr ⟨((q : normalizer (d.F : Set G)) : G), hq⟩
  have htv : ¬ IsConj t v := fun hh => hnc (hzt.trans hh)
  have hvz : v ∉ zpowers z := by
    intro hh
    have heq := involution_eq_of_mem_zpowers h.involution hv hh
    apply hnc
    rw [heq]
  refine ⟨hnc, ?_⟩
  intro u hu hu2
  by_cases huz : u ∈ zpowers z
  · have heq := involution_eq_of_mem_zpowers h.involution hu2 huz
    exact ⟨1, Or.inl (by simpa using heq.symm)⟩
  rcases derived_fusion_of_distinct_representatives h t v ht.1 htz hw.1 hvz htv
      u hu huz with ⟨a, ha⟩ | ⟨a, ha⟩
  · let qL : L := ⟨((q : normalizer (d.F : Set G)) : G),
      mem_sup_right (q : normalizer (d.F : Set G)).property⟩
    let aL : L := ⟨(a : G), mem_sup_left a.property⟩
    refine ⟨aL * qL, Or.inl ?_⟩
    change ((a : G) * ((q : normalizer (d.F : Set G)) : G)) * z *
      ((a : G) * ((q : normalizer (d.F : Set G)) : G))⁻¹ = u
    rw [mul_inv_rev]
    calc
      _ = (a : G) * (((q : normalizer (d.F : Set G)) : G) * z *
          ((q : normalizer (d.F : Set G)) : G)⁻¹) * (a : G)⁻¹ := by group
      _ = u := by rw [hq, ha]
  · exact ⟨⟨(a : G), mem_sup_left a.property⟩, Or.inr ha⟩

/-- Ambient completeness is a consequence of fusion in the supplied Sylow;
the local premise retains the conjugators needed for the later generation step. -/
public theorem involution_classes_of_sylow_fusion
    (d : ParrottSecondElementaryData z) (v : G)
    (hfusion : ∀ u : G, u ∈ (d.sylow : Subgroup G) → orderOf u = 2 →
      ∃ l : (centralizer ({z} : Set G) ⊔ normalizer (d.F : Set G) : Subgroup G),
        (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u) :
    ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u := by
  intro u hu
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, huw⟩ := d.sylow.exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa only [pow_one] using hu)
  have hw : orderOf (w : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp huw
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq u).trans hu
  obtain ⟨l, hl | hl⟩ := hfusion w w.property hw
  · exact Or.inl ((isConj_iff.mpr ⟨(l : G), hl⟩).trans huw.symm)
  · exact Or.inr ((isConj_iff.mpr ⟨(l : G), hl⟩).trans huw.symm)



/-- The two remaining local branches suffice for both Sylow fusion with
conjugators in the join and the ambient two-class assertion. -/
public theorem involution_fusion_of_core_and_outer
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let L := H ⊔ normalizer (d.F : Set G)
    (∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) →
    (∀ u : G, u ∈ (d.sylow : Subgroup G) → u ∉ J.map H.subtype → orderOf u = 2 →
      ∃ l : L, (l : G) * u * (l : G)⁻¹ ∈ E) →
    ¬ IsConj z v ∧
      (∀ u : G, u ∈ (d.sylow : Subgroup G) → orderOf u = 2 →
        ∃ l : L, (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u) ∧
      (∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u) := by
  intro H J E L hcore houter
  obtain ⟨hnc, hderived⟩ := d.derived_involution_fusion_in_join h hN hproper Q v hv hfix
  have hfusion (u : G) (huT : u ∈ (d.sylow : Subgroup G)) (hu2 : orderOf u = 2) :
      ∃ l : L, (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u := by
    by_cases huE : u ∈ E
    · exact hderived u huE hu2
    by_cases huJ : u ∈ J.map H.subtype
    · obtain ⟨l, hl⟩ := hcore u huJ huE hu2
      exact ⟨l, Or.inr hl⟩
    obtain ⟨a, ha⟩ := houter u huT huJ hu2
    have hau2 : orderOf ((a : G) * u * (a : G)⁻¹) = 2 :=
      ((MulAut.conj (a : G)).orderOf_eq u).trans hu2
    obtain ⟨b, hb | hb⟩ := hderived _ ha hau2
    · refine ⟨a⁻¹ * b, Or.inl ?_⟩
      change ((a : G)⁻¹ * (b : G)) * z * ((a : G)⁻¹ * (b : G))⁻¹ = u
      calc
        _ = (a : G)⁻¹ * ((b : G) * z * (b : G)⁻¹) * (a : G) := by group
        _ = u := by rw [hb]; group
    · refine ⟨a⁻¹ * b, Or.inr ?_⟩
      change ((a : G)⁻¹ * (b : G)) * v * ((a : G)⁻¹ * (b : G))⁻¹ = u
      calc
        _ = (a : G)⁻¹ * ((b : G) * v * (b : G)⁻¹) * (a : G) := by group
        _ = u := by rw [hb]; group
  exact ⟨hnc, hfusion, d.involution_classes_of_sylow_fusion v hfusion⟩



/-- Every core involution outside the derived core can be moved into the
supplied elementary subgroup, still outside the derived core, inside H. -/
public theorem core_involution_transport_to_elementary
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
      ∃ a : H, (a : G) * u * (a : G)⁻¹ ∈ d.F ∧
        (a : G) * u * (a : G)⁻¹ ∉ E := by
  intro H J E u hu huE hu2
  obtain ⟨uH, huJ, rfl⟩ := hu
  let DH := (commutator J).map J.subtype
  have huDH : uH ∉ DH := by
    intro hh
    apply huE
    have hm := mem_map_of_mem H.subtype hh
    rwa [map_map] at hm
  have huH2 : orderOf uH = 2 := (Subgroup.orderOf_coe uH).symm.trans hu2
  obtain ⟨e, he⟩ := parrott_second_elementary_of_core_involution z h uH huJ huH2 huDH
  have huF : (uH : G) ∈ e.F := by
    rw [e.fixed_join, he]
    exact mem_sup_left (mem_zpowers (uH : G))
  obtain ⟨a, ha⟩ := e.exists_conjugate_fixed_join d h
  have haN : (a : G) ∈ normalizer (E : Set G) := by
    rw [parrott_derived_normalizer_of_nTwo hN z h]
    exact a.property
  refine ⟨a, ?_, ?_⟩
  · rw [← ha]
    exact mem_map.mpr ⟨(uH : G), huF, rfl⟩
  · exact fun hh => huE ((mem_normalizer_iff.mp haN (uH : G)).mpr hh)

/-- Fusion of F outside the central four-group supplies the entire original
core branch. The inverse transporter keeps the resulting conjugator in the join. -/
public theorem core_involution_fusion_of_elementary
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) (v : G) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let L := H ⊔ N
    (∀ u : G, u ∈ d.F → u ∉ ZK → orderOf u = 2 →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) →
    ∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u := by
  intro H J E N K ZK L hF u hu huE hu2
  obtain ⟨a, haF, haE⟩ := d.core_involution_transport_to_elementary h hN u hu huE hu2
  have haZ : (a : G) * u * (a : G)⁻¹ ∉ ZK :=
    fun hh => haE ((d.normalizer_core_center_le_inf h hN hproper hh).1)
  have ha2 : orderOf ((a : G) * u * (a : G)⁻¹) = 2 :=
    ((MulAut.conj (a : G)).orderOf_eq u).trans hu2
  obtain ⟨b, hb⟩ := hF _ haF haZ ha2
  let aL : L := ⟨(a : G), mem_sup_left a.property⟩
  refine ⟨aL⁻¹ * b, ?_⟩
  change ((a : G)⁻¹ * (b : G)) * v * ((a : G)⁻¹ * (b : G))⁻¹ = u
  calc
    _ = (a : G)⁻¹ * ((b : G) * v * (b : G)⁻¹) * (a : G) := by group
    _ = u := by rw [hb]; group

/-- Every involution of the original core outside its derived subgroup belongs
to the prescribed fixed involution's class, with a conjugator in H∨N. -/
public theorem core_involution_fusion_in_join
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    let L := H ⊔ N
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u := by
  intro H J E N X D A L hCD v hv hfix
  have hF := (d.normalizer_elementary_fusion_in_join h hN hproper Q hCD v hv hfix).2
  exact d.core_involution_fusion_of_elementary h hN hproper v
    (fun u hu huZ _ => hF u hu huZ)

/-- Parrott's two involution classes and finer local fusion for the supplied
normalizer data. The Sylow, elementary, and original-core assertions retain
actual conjugators in H∨N; Sylow conjugacy gives ambient completeness.
Normalizer growth and the derived-centralizer containment are the only local
inputs still to be discharged by the unconditional realization theorem. -/
public theorem normalizer_involution_fusion_from_local_data
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let L := H ⊔ N
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ¬ IsConj z v ∧
      (∀ u : G, u ∈ (d.sylow : Subgroup G) → orderOf u = 2 →
        ∃ l : L, (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u) ∧
      (∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u) ∧
      (∀ u : G, u ∈ ZK → orderOf u = 2 →
        ∃ l : L, (l : G) * z * (l : G)⁻¹ = u) ∧
      (∀ u : G, u ∈ d.F → u ∉ ZK →
        ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) ∧
      (∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
        ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) := by
  intro H J E N K X D A ZK L hCD v hv hfix
  have hcore := d.core_involution_fusion_in_join h hN hproper Q hCD v hv hfix
  obtain ⟨hnc, hSylow, hG⟩ := d.involution_fusion_of_core_and_outer h hN hproper Q v hv hfix
    hcore (d.outer_involution_transport h hN hproper Q hCD v hv hfix)
  obtain ⟨hZK, hF⟩ := d.normalizer_elementary_fusion_in_join h hN hproper Q hCD v hv hfix
  exact ⟨hnc, hSylow, hG, hZK, hF, hcore⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
