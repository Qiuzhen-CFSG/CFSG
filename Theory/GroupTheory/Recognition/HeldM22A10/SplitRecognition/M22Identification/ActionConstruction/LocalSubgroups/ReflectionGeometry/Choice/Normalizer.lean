module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.Basic
/-!
# The actual complement in the normalizer of EQ*

Write C = N(⟨w⟩) ∩ N(E). The fixed-point-free action of w on E gives
E ∩ C = 1. Frattini's argument, applied to the Sylow three-subgroup ⟨w⟩
of B = E⟨w⟩ inside N(B), gives N(B) = EC. All normality is relative
to the indicated normalizer.

The split local data construct the genuine quotient map N(E) → A6 with
kernel E. The preimage of ⟨q⟩, where q is the image of w, is exactly B.
Surjectivity therefore identifies the preimage of N_A6(⟨q⟩) with N(B).
Restricting the quotient map to C gives an actual isomorphism with this
normalizer and sends the marked actor to q. No reflection is assumed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, p.16;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer) (w : FusedNineIntersectionActor D k)

/-- Janko’s actual complement N(⟨w⟩) ∩ N(E). -/
@[expose] public def reflectionComplement : Subgroup G :=
  normalizer (zpowers w.actor : Set G) ⊓ normalizer (CaseII.E D k : Set G)

omit [Finite G] in
/-- The fixed-point-free action makes the intersection of E with the complement trivial. -/
public theorem E_disjoint_reflectionComplement : Disjoint (CaseII.E D k) (reflectionComplement D k w) := by
  apply Subgroup.disjoint_def.mpr
  intro e he hn
  apply w.fixed_point_free e he
  have hdis : Disjoint (CaseII.E D k) (zpowers w.actor) :=
    disjoint_of_coprime_natCard (by rw [CaseII.E_card, Nat.card_zpowers, w.actor_order]; decide)
  have hE : ⁅e, w.actor⁆ ∈ CaseII.E D k := by
    have h := (mem_normalizer_iff.mp w.normalizes_E e⁻¹).mp ((CaseII.E D k).inv_mem he)
    simpa only [commutatorElement_def, mul_assoc] using (CaseII.E D k).mul_mem he h
  have hQ : ⁅e, w.actor⁆ ∈ zpowers w.actor := by
    have h := (mem_normalizer_iff.mp hn.1 w.actor).mp (mem_zpowers w.actor)
    exact (zpowers w.actor).mul_mem h ((zpowers w.actor).inv_mem (mem_zpowers w.actor))
  exact (commutatorElement_eq_one_iff_commute.mp
    (Subgroup.disjoint_def.mp hdis hE hQ)).symm

/-- Frattini’s argument gives the literal product decomposition of N(B). -/
public theorem normalizer_B_eq_E_sup_reflectionComplement :
    normalizer (B D k w : Set G) = CaseII.E D k ⊔ reflectionComplement D k w := by
  let NB := normalizer (B D k w : Set G)
  let J := (B D k w).subgroupOf NB
  let Q := (zpowers w.actor).subgroupOf NB
  have hQB : zpowers w.actor ≤ B D k w := le_sup_right
  have hQN : zpowers w.actor ≤ NB := hQB.trans le_normalizer
  have hQJ : Q ≤ J := subgroupOf_mono NB hQB
  have hQcard : Nat.card Q = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQN).toEquiv, Nat.card_zpowers, w.actor_order]
  have hJcard : Nat.card J = 48 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (B D k w).le_normalizer).toEquiv, B_card]
  have hPcard : Nat.card (Q.subgroupOf J) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQJ).toEquiv, hQcard]
  have hPindex : (Q.subgroupOf J).index = 16 := by
    have h := (Q.subgroupOf J).card_mul_index
    rw [hPcard, hJcard] at h
    omega
  let P : Sylow 3 J := (IsPGroup.of_card (p := 3) (n := 1)
    (by simpa using hPcard)).toSylow (by rw [hPindex]; decide)
  have hFr := P.normalizer_sup_eq_top
  have hPmap : P.map J.subtype = Q := map_subgroupOf_eq_of_le hQJ
  rw [hPmap, ← subgroupOf_normalizer_eq hQN] at hFr
  have hm := congrArg (Subgroup.map NB.subtype) hFr
  rw [Subgroup.map_sup, subgroupOf_map_subtype, map_subgroupOf_eq_of_le (B D k w).le_normalizer,
    ← MonoidHom.range_eq_map, NB.range_subtype] at hm
  have hCN : reflectionComplement D k w ≤ NB := by
    intro x hx
    exact normalizes_B_of_normalizes_E_and_actor D k w x hx.2 hx.1
  have hCeq : normalizer (zpowers w.actor : Set G) ⊓ NB = reflectionComplement D k w := by
    apply le_antisymm
    · exact inf_le_inf_left _ (normalizer_B_le_normalizer_E D k w)
    · exact le_inf inf_le_left hCN
  rw [hCeq] at hm
  have hQC : zpowers w.actor ≤ reflectionComplement D k w :=
    le_inf le_normalizer (zpowers_le.mpr w.normalizes_E)
  calc
    NB = reflectionComplement D k w ⊔ B D k w := hm.symm
    _ = CaseII.E D k ⊔ reflectionComplement D k w := by
      dsimp only [B]
      rw [sup_left_comm, sup_of_le_left hQC]

omit [Finite G] in
/-- The source splitting gives a surjective A6 projection with the actual relative E kernel. -/
public theorem exists_ENormalizerProjection (L : LocalAnalysisData D k) :
    ∃ f : normalizer (CaseII.E D k : Set G) →* alternatingGroup (Fin 6),
      Function.Surjective f ∧
      f.ker = (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) := by
  let N := normalizer (CaseII.E D k : Set G)
  let R := (CaseII.E D k).subgroupOf N
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  let e : N ⧸ R ≃* alternatingGroup (Fin 6) := hK.symm.QuotientMulEquiv.trans eK
  let f : N →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' R)
  refine ⟨f, e.surjective.comp (QuotientGroup.mk'_surjective R), ?_⟩
  ext x
  change e (QuotientGroup.mk' R x) = 1 ↔ x ∈ R
  rw [e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

omit [Finite G] in
/-- The chosen common actor belongs to its actual complement. -/
public theorem actor_mem_reflectionComplement : w.actor ∈ reflectionComplement D k w :=
  ⟨le_normalizer (mem_zpowers w.actor), w.normalizes_E⟩

/-- Restricting the actual E quotient identifies the complement and preserves the actor. -/
public theorem exists_reflectionComplement_equiv (L : LocalAnalysisData D k) :
    ∃ (q : alternatingGroup (Fin 6))
      (e : reflectionComplement D k w ≃* normalizer (zpowers q : Set (alternatingGroup (Fin 6)))),
      orderOf q = 3 ∧ (e ⟨w.actor, actor_mem_reflectionComplement D k w⟩ : alternatingGroup (Fin 6)) = q := by
  let N := normalizer (CaseII.E D k : Set G)
  let R := (CaseII.E D k).subgroupOf N
  let C := reflectionComplement D k w
  let CN := C.subgroupOf N
  let BN := (B D k w).subgroupOf N
  have hCN : C ≤ N := inf_le_right
  have hBN : B D k w ≤ N := B_le_normalizer_E D k w
  let qN : N := ⟨w.actor, w.normalizes_E⟩
  obtain ⟨f, hf, hker⟩ := exists_ENormalizerProjection D k L
  change f.ker = R at hker
  let q := f qN
  have hq3 : orderOf q = 3 := by
    apply orderOf_eq_prime
    · change f qN ^ 3 = 1
      rw [← map_pow]
      have hp : qN ^ 3 = 1 := Subtype.ext (w.actor_order ▸ pow_orderOf_eq_one w.actor)
      rw [hp, map_one]
    · intro hq
      have he : qN ∈ R := by
        rw [← hker]
        exact hq
      have hd := (CaseII.E D k).orderOf_dvd_natCard he
      change orderOf w.actor ∣ Nat.card (CaseII.E D k) at hd
      rw [w.actor_order, CaseII.E_card] at hd
      norm_num at hd
  have hzp : (zpowers w.actor).subgroupOf N = zpowers qN := by
    apply (map_injective N.subtype_injective)
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr w.normalizes_E), MonoidHom.map_zpowers]
    rfl
  have hpre : (zpowers q).comap f = BN := by
    change (zpowers (f qN)).comap f = _
    rw [← MonoidHom.map_zpowers, comap_map_eq, hker]
    rw [sup_comm, ← hzp, ← subgroupOf_sup le_normalizer (zpowers_le.mpr w.normalizes_E)]
    rfl
  have hnorm : normalizer (BN : Set N) =
      (normalizer (zpowers q : Set (alternatingGroup (Fin 6)))).comap f := by
    rw [comap_normalizer_eq_of_surjective _ hf, hpre]
  have hsup : normalizer (BN : Set N) = R ⊔ CN := by
    rw [← subgroupOf_normalizer_eq hBN, normalizer_B_eq_E_sup_reflectionComplement D k w,
      subgroupOf_sup le_normalizer hCN]
  have hmap : CN.map f = normalizer (zpowers q : Set (alternatingGroup (Fin 6))) := by
    have hm := congrArg (Subgroup.map f) (hsup.symm.trans hnorm)
    rw [Subgroup.map_sup, show R.map f = ⊥ from by rw [← hker, Subgroup.map_ker_self], bot_sup_eq,
      map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top)] at hm
    exact hm
  let j : C →* N := inclusion hCN
  have hj : ∀ c : C, f (j c) ∈ normalizer (zpowers q : Set (alternatingGroup (Fin 6))) := by
    intro c
    rw [← hmap]
    exact mem_map_of_mem f c.property
  let φ : C →* normalizer (zpowers q : Set (alternatingGroup (Fin 6))) :=
    (f.comp j).codRestrict _ hj
  have hi : Function.Injective φ := by
    apply (MonoidHom.ker_eq_bot_iff φ).mp
    apply bot_unique
    intro c hc
    apply mem_bot.mpr
    apply Subtype.ext
    have hcE : (c : G) ∈ CaseII.E D k := by
      have hcF : j c ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
      rwa [hker] at hcF
    exact Subgroup.disjoint_def.mp (E_disjoint_reflectionComplement D k w) hcE c.property
  have hs : Function.Surjective φ := by
    intro y
    have hy : (y : alternatingGroup (Fin 6)) ∈ CN.map f := hmap.symm ▸ y.property
    obtain ⟨n, hn, he⟩ := hy
    exact ⟨⟨n, hn⟩, Subtype.ext he⟩
  exact ⟨q, MulEquiv.ofBijective φ ⟨hi, hs⟩, hq3, rfl⟩

/-- The decomposition is a complement relative to N(B), with no ambient normality claim. -/
public theorem reflectionComplement_isComplement :
    ((CaseII.E D k).subgroupOf (normalizer (B D k w : Set G))).IsComplement'
      ((reflectionComplement D k w).subgroupOf (normalizer (B D k w : Set G))) := by
  let NB := normalizer (B D k w : Set G)
  have hEN : CaseII.E D k ≤ NB :=
    (show CaseII.E D k ≤ B D k w from le_sup_left).trans le_normalizer
  have hCN : reflectionComplement D k w ≤ NB := by
    change reflectionComplement D k w ≤ normalizer (B D k w : Set G)
    rw [normalizer_B_eq_E_sup_reflectionComplement D k w]
    exact le_sup_right
  let R := (CaseII.E D k).subgroupOf NB
  let C := (reflectionComplement D k w).subgroupOf NB
  have hn : R.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_B_le_normalizer_E D k w)
  let := hn
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro x hxE hxC
    exact Subtype.ext (Subgroup.disjoint_def.mp (E_disjoint_reflectionComplement D k w) hxE hxC)
  · have hs : R ⊔ C = ⊤ := by
      rw [← subgroupOf_sup hEN hCN, ← normalizer_B_eq_E_sup_reflectionComplement D k w,
        subgroupOf_self]
    have hnorm : C ≤ normalizer (R : Set NB) := by rw [R.normalizer_eq_top]; exact le_top
    rw [← coe_mul_of_right_le_normalizer_left R C hnorm, hs]
    rfl

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
