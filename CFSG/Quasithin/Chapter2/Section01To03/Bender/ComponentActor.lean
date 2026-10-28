module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentGeometry
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.OnanExclusion

/-!
# The literal component action and the Bender GO application

The actor is the image of N_L(U) = L ∩ M in the actual Aut_M(U). Its kernel
is all of N_L(U) ∩ C_G(U); in particular, an odd torus kernel is retained.
The source product split and normalizer transitivity identify the fixed
space with C_U(L). Displacements lie in U ∩ L because U normalizes L.
Component rigidity then proves both the TI orbit and normality of the actor
in the actual fixed-space stabilizer. These facts construct the GO Input
consumed by the already proved bad-centralizer obstruction.

The final theorem is conditional on genuine earlier source mathematics:
the projected-factor split, I.3.2 containment, an odd-rank-three witness
inside a two-local for three commuting components, and the cyclic odd
normalizer action in the Bender models (with |U ∩ L| > 2). None of its
premises asserts TI, GO alternatives or Bender recognition. Their source
construction, and the Shult recognition branch, remain with the Bender
assembly; this is not Proposition 2.2.2(2) or Theorem 2.2.5.

Source: Aschbacher–Smith, Proposition 2.2.2, printed pp.519–520.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The actual action of N_L(U) = L ∩ M into Aut_M(U). -/
abbrev componentActionHom (w : LocalControlWitness T M) (L : Subgroup G) :
    (L ⊓ M : Subgroup G) →* sourceActionImage w :=
  (conjugationAction M w.U w.normalizes).rangeRestrict.comp (inclusion inf_le_right)

/-- The source actor Aut_L(U) means this image of N_L(U), not an action of all L. -/
abbrev componentActor (w : LocalControlWitness T M) (L : Subgroup G) :
    Subgroup (sourceActionImage w) := (componentActionHom w L).range

omit [Finite G] in
/-- The domain of the component action is the source normalizer N_L(U). -/
theorem componentAction_domain (w : LocalControlWitness T M) (L : Subgroup G) :
    L ⊓ normalizer (w.U : Set G) = L ⊓ M := by
  rw [w.normalizer_eq]

omit [Finite G] in
theorem componentActionHom_ker (w : LocalControlWitness T M) (L : Subgroup G) :
    (componentActionHom w L).ker =
      (centralizer (w.U : Set G)).subgroupOf (L ⊓ M) := by
  ext a
  change componentActionHom w L a = 1 ↔ _
  rw [Subtype.ext_iff]
  change w.U.normalizerMonoidHom ⟨(a : G), w.normalizes a.property.2⟩ = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

omit [Finite G] in
theorem componentActor_eq_map (w : LocalControlWitness T M) (L : Subgroup G) :
    componentActor w L =
      (L.subgroupOf M).map (conjugationAction M w.U w.normalizes).rangeRestrict := by
  ext a
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨⟨l, l.property.2⟩, l.property.1, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl, l.property⟩, rfl⟩

omit [Finite G] in
/-- The image has exactly the subgroup/map presentation used by the source. -/
theorem componentActor_eq_intersection_map (w : LocalControlWitness T M) (L : Subgroup G) :
    componentActor w L = ((L ⊓ M).subgroupOf M).map
      (conjugationAction M w.U w.normalizes).rangeRestrict := by
  rw [componentActor_eq_map]
  congr 1
  ext x
  exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩

omit [Finite G] in
theorem componentActor_normalized_of_component_normalized
    (w : LocalControlWitness T M) (L : Subgroup G) (m : M)
    (hm : (m : G) ∈ normalizer (L : Set G)) :
    (componentActor w L).map
      (MulAut.conj ((conjugationAction M w.U w.normalizes).rangeRestrict m)).toMonoidHom =
      componentActor w L := by
  apply mem_normalizer_iff_map_conj_eq.mp
  rw [componentActor_eq_map]
  apply le_normalizer_map _
  apply mem_map_of_mem
  rw [mem_normalizer_iff]
  intro l
  exact mem_normalizer_iff.mp hm l

section Linear
variable (w : LocalControlWitness T M) [IsElementaryAbelian 2 w.U]
open Representation.BinaryOffender Representation.RegularCyclicNormalClosure

omit [Finite G] in
/-- The fixed vectors are the actual centralizer of N_L(U), without any
claim that its kernel is only the two-core. -/
theorem mem_componentActor_fixedSpace (L : Subgroup G) (v : Additive w.U) :
    v ∈ fixedSpace (sourceImageRepresentation w) (componentActor w L) ↔
      (v.toMul : G) ∈ centralizer (L ⊓ M : Set G) := by
  constructor
  · intro hv l hl
    have he := congrArg (fun a : Additive w.U => (a.toMul : G))
      (hv ⟨componentActionHom w L ⟨l, hl⟩, ⟨⟨l, hl⟩, rfl⟩⟩)
    change l * (v.toMul : G) * l⁻¹ = (v.toMul : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  · intro hv y
    obtain ⟨l, hl⟩ := y.property
    change sourceImageRepresentation w (y : sourceActionImage w) v = v
    rw [← hl]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (v.toMul : G) * (l : G)⁻¹ = (v.toMul : G)
    rw [hv l l.property, mul_inv_cancel_right]

end Linear

variable (w : LocalControlWitness T M) [IsElementaryAbelian 2 w.U]
open Representation.BinaryOffender Representation.RegularCyclicNormalClosure

omit [Finite G] in
private theorem fixedSpace_mem_of_centralizers (L : Subgroup G)
    (hc : w.U ⊓ centralizer (L ⊓ M : Set G) = componentFixedSubgroup w L)
    (v : Additive w.U) :
    v ∈ fixedSpace (sourceImageRepresentation w) (componentActor w L) ↔
      (v.toMul : G) ∈ componentFixedSubgroup w L := by
  rw [mem_componentActor_fixedSpace]
  exact ⟨fun hv => hc ▸ (show (v.toMul : G) ∈ w.U ⊓ centralizer (L ⊓ M : Set G)
      from ⟨v.toMul.property, hv⟩), fun hv => (hc.symm ▸ hv).2⟩

omit [Finite G] in
private theorem fixedSpace_map_mem (L : Subgroup G)
    (hc : w.U ⊓ centralizer (L ⊓ M : Set G) = componentFixedSubgroup w L)
    (m : M) (v : Additive w.U) :
    v ∈ (fixedSpace (sourceImageRepresentation w) (componentActor w L)).map
      (sourceImageRepresentation w ((conjugationAction M w.U w.normalizes).rangeRestrict m)) ↔
      (v.toMul : G) ∈ componentConjugate (componentFixedSubgroup w L) m := by
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨a.toMul, (fixedSpace_mem_of_centralizers w L hc a).mp ha, ?_⟩
    exact congrArg (fun a : Additive w.U => (a.toMul : G)) he
  · rintro ⟨a, ha, he⟩
    let av : Additive w.U := Additive.ofMul ⟨a, ha.1⟩
    refine ⟨av, (fixedSpace_mem_of_centralizers w L hc av).mpr ha, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext he

omit [Finite G] in
/-- The actual image actor satisfies the two GO geometry clauses once the
source component-intersection rigidity has been proved. -/
theorem componentActor_ti_and_normal
    (L : Subgroup G) (hne : componentFixedSubgroup w L ≠ ⊥)
    (hc : w.U ⊓ centralizer (L ⊓ M : Set G) = componentFixedSubgroup w L)
    (hrigid : ∀ x y : M,
      componentFixedSubgroup w (componentConjugate L x) ⊓
        componentFixedSubgroup w (componentConjugate L y) ≠ ⊥ →
      componentConjugate L x = componentConjugate L y) :
    (∀ A ∈ Representation.GoldschmidtONan.fixedOrbit (sourceImageRepresentation w) (componentActor w L),
      ∀ B ∈ Representation.GoldschmidtONan.fixedOrbit (sourceImageRepresentation w) (componentActor w L),
      A ≠ B → Disjoint A B) ∧
    (∀ a : sourceActionImage w,
      (fixedSpace (sourceImageRepresentation w) (componentActor w L)).map
        (sourceImageRepresentation w a) = fixedSpace (sourceImageRepresentation w) (componentActor w L) →
      (componentActor w L).map (MulAut.conj a).toMonoidHom = componentActor w L) := by
  let f := (conjugationAction M w.U w.normalizes).rangeRestrict
  have hm (m : M) (v : Additive w.U) :
      v ∈ (fixedSpace (sourceImageRepresentation w) (componentActor w L)).map
        (sourceImageRepresentation w (f m)) ↔
      (v.toMul : G) ∈ componentFixedSubgroup w (componentConjugate L m) := by
    rw [componentFixedSubgroup_conjugate]
    exact fixedSpace_map_mem w L hc m v
  constructor
  · rintro A ⟨a, rfl⟩ B ⟨b, rfl⟩ hab
    obtain ⟨m, rfl⟩ := (conjugationAction M w.U w.normalizes).rangeRestrict_surjective a
    obtain ⟨n, rfl⟩ := (conjugationAction M w.U w.normalizes).rangeRestrict_surjective b
    apply Submodule.disjoint_def.mpr
    intro v hv hv'
    by_contra hv0
    have hi : componentFixedSubgroup w (componentConjugate L m) ⊓
        componentFixedSubgroup w (componentConjugate L n) ≠ ⊥ := by
      intro he
      have hh := show (v.toMul : G) ∈ componentFixedSubgroup w (componentConjugate L m) ⊓
          componentFixedSubgroup w (componentConjugate L n) from ⟨(hm m v).mp hv, (hm n v).mp hv'⟩
      rw [he, mem_bot] at hh
      exact hv0 (Additive.toMul.injective (Subtype.ext hh))
    have he := hrigid m n hi
    apply hab
    ext v
    exact (hm m v).trans (he ▸ (hm n v).symm)
  · intro a ha
    obtain ⟨m, rfl⟩ := (conjugationAction M w.U w.normalizes).rangeRestrict_surjective a
    have he : componentFixedSubgroup w (componentConjugate L m) = componentFixedSubgroup w L := by
      ext g
      constructor
      · intro hg
        let v : Additive w.U := Additive.ofMul ⟨g, hg.1⟩
        exact (fixedSpace_mem_of_centralizers w L hc v).mp (ha ▸ (hm m v).mpr hg)
      · intro hg
        let v : Additive w.U := Additive.ofMul ⟨g, hg.1⟩
        exact (hm m v).mp (ha.symm ▸ (fixedSpace_mem_of_centralizers w L hc v).mpr hg)
    have hi : componentFixedSubgroup w (componentConjugate L m) ⊓
        componentFixedSubgroup w (componentConjugate L (1 : M)) ≠ ⊥ := by
      simpa only [he, componentConjugate_one, inf_idem] using hne
    have hL := hrigid m 1 hi
    rw [componentConjugate_one] at hL
    exact componentActor_normalized_of_component_normalized w L m
      (mem_normalizer_iff_map_conj_eq.mpr hL)



omit [Finite G] in
/-- The moved space lies in the literal U∩L. This uses that U normalizes
L, not the false assertion that all of L normalizes U. -/
theorem component_displacement_mem (L : Subgroup G)
    (hUL : w.U ≤ normalizer (L : Set G))
    {v : Additive w.U}
    (hv : v ∈ displacementSpan (sourceImageRepresentation w) (componentActor w L) ⊤) :
    (v.toMul : G) ∈ w.U ⊓ L := by
  let D : Submodule (ZMod 2) (Additive w.U) := AddSubgroup.toZModSubmodule 2
    ((w.U ⊓ L).subgroupOf w.U).toAddSubgroup
  have hle : displacementSpan (sourceImageRepresentation w) (componentActor w L) ⊤ ≤ D := by
    apply Submodule.span_le.mpr
    rintro v ⟨y, hy, a, _, rfl⟩
    obtain ⟨l, rfl⟩ := hy
    change (((l : G) * (a.toMul : G) * (l : G)⁻¹) / (a.toMul : G)) ∈ w.U ⊓ L
    rw [div_eq_mul_inv]
    constructor
    · exact w.U.mul_mem
        (show (l : G) * (a.toMul : G) * (l : G)⁻¹ ∈ w.U from
          (conjugationAction M w.U w.normalizes ⟨l, l.property.2⟩ a.toMul).property)
        (w.U.inv_mem a.toMul.property)
    · change (((l : G) * (a.toMul : G) * (l : G)⁻¹) * (a.toMul : G)⁻¹) ∈ L
      have hh := (mem_normalizer_iff.mp (hUL a.toMul.property) (l : G)⁻¹).mp
        (L.inv_mem l.property.1)
      simpa only [mul_assoc, Subgroup.mem_toSubmonoid] using L.mul_mem l.property.1 hh
  exact hle hv

omit [Finite G] in
/-- A genuine normalizer conjugacy witness on (U∩L)# gives transitivity on
the actual displacement space of the faithful image. -/
theorem componentActor_transitive_of_local (L : Subgroup G)
    (hUL : w.U ≤ normalizer (L : Set G))
    (hlocal : ∀ a ∈ w.U ⊓ L, a ≠ 1 → ∀ b ∈ w.U ⊓ L, b ≠ 1 →
      ∃ l ∈ L ⊓ M, l * a * l⁻¹ = b) :
    ∀ v ∈ displacementSpan (sourceImageRepresentation w) (componentActor w L) ⊤,
      v ≠ 0 → ∀ a ∈ displacementSpan (sourceImageRepresentation w) (componentActor w L) ⊤,
      a ≠ 0 → ∃ y : componentActor w L, sourceImageRepresentation w y v = a := by
  intro v hv hv0 a ha ha0
  have hv1 : (v.toMul : G) ≠ 1 := fun he => hv0 (Additive.toMul.injective (Subtype.ext he))
  have ha1 : (a.toMul : G) ≠ 1 := fun he => ha0 (Additive.toMul.injective (Subtype.ext he))
  obtain ⟨l, hl, he⟩ := hlocal v.toMul (component_displacement_mem w L hUL hv) hv1
    a.toMul (component_displacement_mem w L hUL ha) ha1
  refine ⟨⟨componentActionHom w L ⟨l, hl⟩, ⟨⟨l, hl⟩, rfl⟩⟩, ?_⟩
  exact Additive.toMul.injective (Subtype.ext he)


/-- The Bender normalizer action identifies its fixed subgroup with C_U(L).
The proof uses the actual product decomposition and transitivity on (U∩L)#;
no fixed-space identity is assumed. The size bound is supplied by q ≥ 4
in the source Bender rows. -/
theorem component_centralizers_eq (L : Subgroup G)
    (hsplit : w.U = componentFixedSubgroup w L ⊔ (w.U ⊓ L))
    (hsize : 2 < Nat.card (w.U ⊓ L : Subgroup G))
    (hlocal : ∀ a ∈ w.U ⊓ L, a ≠ 1 → ∀ b ∈ w.U ⊓ L, b ≠ 1 →
      ∃ l ∈ L ⊓ M, l * a * l⁻¹ = b) :
    w.U ⊓ centralizer (L ⊓ M : Set G) = componentFixedSubgroup w L := by
  classical
  let A := componentFixedSubgroup w L
  let B := w.U ⊓ L
  have hn : B ≤ normalizer (A : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    exact (inf_le_left : B ≤ w.U).trans
      ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le inf_le_left))
  apply le_antisymm
  · intro v hv
    have hvp : v ∈ (A : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A B hn]
      change v ∈ componentFixedSubgroup w L ⊔ (w.U ⊓ L)
      rw [← hsplit]
      exact hv.1
    obtain ⟨c, hc, d, hd, he⟩ := hvp
    have hcC : c ∈ centralizer (L ⊓ M : Set G) := centralizer_le inf_le_left hc.2
    have hdC : d ∈ centralizer (L ⊓ M : Set G) := by
      have hh := (centralizer (L ⊓ M : Set G)).mul_mem
        ((centralizer (L ⊓ M : Set G)).inv_mem hcC) hv.2
      rw [← he, inv_mul_cancel_left] at hh
      exact hh
    have hd1 : d = 1 := by
      by_contra hd1
      let _ : Fintype B := Fintype.ofFinite B
      have h3 : 3 ≤ ENat.card B := by
        rw [ENat.card_eq_coe_fintype_card]
        have hh : 3 ≤ Fintype.card B := by
          rw [← Nat.card_eq_fintype_card]
          change 3 ≤ Nat.card (w.U ⊓ L : Subgroup G)
          omega
        exact_mod_cast hh
      obtain ⟨b, hb1, hbd⟩ := ENat.exists_ne_ne_of_three_le h3 (1 : B) ⟨d, hd⟩
      have hbG : (b : G) ≠ 1 := fun hh => hb1 (Subtype.ext hh)
      obtain ⟨l, hl, hlb⟩ := hlocal d hd hd1 b b.property hbG
      have hld : l * d * l⁻¹ = d := by rw [hdC l hl, mul_inv_cancel_right]
      exact hbd (Subtype.ext (hlb.symm.trans hld))
    have hcv : c = v := by simpa only [hd1, mul_one] using he
    exact hcv ▸ hc
  · intro v hv
    exact ⟨hv.1, centralizer_le inf_le_left hv.2⟩

omit [IsElementaryAbelian 2 w.U] in
/-- A bad component with the genuine earlier component, local-rank and
Bender normalizer-action inputs contradicts the completed GO obstruction.
The fixed-space TI and stabilizer-normality clauses are proved here, not
included among the premises. The remaining model and balance inputs must
still be discharged in Proposition 2.2.2. -/
theorem LocalControlWitness.false_of_maximal_component_geometry
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (hTM : (T : Subgroup G) ≤ M)
    (L : Subgroup G)
    (hmax : Maximal (fun K => K ∈ badCentralizerComponents w) L)
    (hsplit : w.U = componentFixedSubgroup w L ⊔ (w.U ⊓ L))
    (hbalance : ∀ v ∈ componentFixedSubgroup w L, v ≠ 1 →
      ∃ K : Subgroup G, IsComponentIn K (centralizer ({v} : Set G)) ∧ L ≤ K)
    (hthree : ∀ x y z : M,
      componentConjugate L x ≠ componentConjugate L y →
      componentConjugate L x ≠ componentConjugate L z →
      componentConjugate L y ≠ componentConjugate L z →
      componentConjugate L x ≤ centralizer (componentConjugate L y : Set G) →
      componentConjugate L x ≤ centralizer (componentConjugate L z : Set G) →
      componentConjugate L y ≤ centralizer (componentConjugate L z : Set G) →
      ∃ H : Subgroup G, IsTwoLocal H ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 ≤ primeRank p H)
    (hsize : 2 < Nat.card (w.U ⊓ L : Subgroup G))
    (hcyclic : IsCyclic (componentActor w L)) (hodd : Odd (Nat.card (componentActor w L)))
    (hUL : w.U ≤ normalizer (L : Set G))
    (hlocal : ∀ a ∈ w.U ⊓ L, a ≠ 1 → ∀ b ∈ w.U ⊓ L, b ≠ 1 →
      ∃ l ∈ L ⊓ M, l * a * l⁻¹ = b) : False := by
  let _ : IsElementaryAbelian 2 w.U := w.elementary
  have hc := component_centralizers_eq w L hsplit hsize hlocal
  have htrans := componentActor_transitive_of_local w L hUL hlocal
  have hselected := fun v hv hv1 =>
    maximal_component_in_centralizer w hmax hv hv1 (hbalance v hv hv1)
  have hrigid := component_eq_of_twoLocal_rank w hG.quasithin L hmax.1.1 hsplit hselected hthree
  have hCne := componentFixedSubgroup_ne_bot_of_bad w hmax.1
  obtain ⟨hti, hnormal⟩ := componentActor_ti_and_normal w L hCne hc hrigid
  have hactor : componentActor w L ≠ ⊥ := by
    intro he
    have hU : w.U ≤ componentFixedSubgroup w L := by
      intro v hv
      apply (fixedSpace_mem_of_centralizers w L hc (Additive.ofMul ⟨v, hv⟩)).mp
      rw [he, fixedSpace_bot]
      trivial
    exact componentFixedSubgroup_ne_self w L hmax.1.1 (le_antisymm inf_le_left hU)
  have hfixed : fixedSpace (sourceImageRepresentation w) (componentActor w L) ≠ ⊥ := by
    intro he
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
    let a : Additive w.U := Additive.ofMul ⟨(v : G), v.property.1⟩
    have ha := (fixedSpace_mem_of_centralizers w L hc a).mpr v.property
    rw [he, Submodule.mem_bot] at ha
    exact hv1 (Subtype.ext (congrArg (fun b : Additive w.U => (b.toMul : G)) ha))
  have hbad : ∃ v ∈ w.U, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ M := by
    obtain ⟨hLM, v, hv, hv1, hLc⟩ := hmax.1
    exact ⟨v, hv, hv1, fun hCM => hLM (hLc.1.trans hCM)⟩
  exact w.not_onanInput_of_bad_centralizer hG hTM hbad (componentActor w L)
    { faithful := sourceImageRepresentation_injective w
      nontrivial := hactor
      cyclic := hcyclic
      odd := hodd
      transitive := htrans
      fixed_nontrivial := hfixed
      ti := hti
      normal_in_stabilizer := hnormal }

end CFSG.Quasithin.Chapter2.BenderFusion
