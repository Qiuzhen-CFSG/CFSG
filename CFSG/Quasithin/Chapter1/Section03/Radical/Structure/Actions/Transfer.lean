module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements

/-!
# Sylow transport for the radical actions

An odd p-group quotient makes a Sylow p-subgroup a complement to O₂(X).
The complement isomorphism intertwines the actual Frattini actions. Frattini's
argument transfers irreducibility from an actor containing O₂(X) to its
normalizer of the complement. These lemmas use no membership in Ξ and hence
no previously assumed irreducibility.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
1.3.2 and the radical construction on p.509, and the normalizer action on
p.514. The complement and Frattini calculations adapt the proofs in
`Chapter1.Section03.Basic`, removing their unused Ξ hypotheses.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalActions
variable {G : Type*} [Group G]

/-- Every Sylow p-subgroup supplements O₂(X) when the quotient is a p-group. -/
theorem sylow_sup [Finite G] {X : Subgroup G}
    {p : ℕ} [Fact p.Prime] (hq : IsPGroup p (XiQuotient X)) (P : Sylow p X) :
    X.pCoreIn 2 ⊔ (P : Subgroup X).map X.subtype = X := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have htop : (P : Subgroup X).map q = ⊤ :=
    top_unique ((hq.to_subgroup ⊤).le_sylow_of_normal
      (P.mapSurjective (QuotientGroup.mk'_surjective _)))
  have hsup : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
    have hh := congrArg (fun A : Subgroup (XiQuotient X) => A.comap q) htop
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using hh
  have hh := congrArg (fun A : Subgroup X => A.map X.subtype) hsup
  simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, X.range_subtype, pCoreIn] using hh

/-- Frattini factorization using only normality, a p-group quotient and containment of O₂(X). -/
theorem normalizer_factor [Finite G] {T X : Subgroup G}
    (hn : T ≤ normalizer X) (hcT : X.pCoreIn 2 ≤ T)
    {p : ℕ} [Fact p.Prime] (hq : IsPGroup p (XiQuotient X)) (P : Sylow p X) :
    T = X.pCoreIn 2 ⊔ (T ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G)) := by
  let W := X ⊔ T
  let N := X.subgroupOf W
  let e : X ≃* N := (subgroupOfEquivOfLe (show X ≤ W from le_sup_left)).symm
  let R : Sylow p N := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let _ : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hn)
  have hm : ((R : Subgroup N).map N.subtype).map W.subtype =
      (P : Subgroup X).map X.subtype := by
    change (((P : Subgroup X).map e.toMonoidHom).map N.subtype).map W.subtype = _
    rw [map_map, map_map]
    rfl
  have hfr : N ⊔ normalizer ((R : Subgroup N).map N.subtype : Set W) = ⊤ := by
    rw [sup_comm]
    exact R.normalizer_sup_eq_top
  apply le_antisymm ?_ (sup_le hcT inf_le_left)
  intro t ht
  have htW : t ∈ W := (show T ≤ W from le_sup_right) ht
  have htgen : (⟨t, htW⟩ : W) ∈ N ⊔
      normalizer ((R : Subgroup N).map N.subtype : Set W) := by rw [hfr]; trivial
  obtain ⟨x, hx, n, hn, hxn⟩ := mem_sup_of_normal_left.mp htgen
  have hnG : (n : G) ∈ normalizer ((P : Subgroup X).map X.subtype : Set G) := by
    rw [← hm]
    exact (((R : Subgroup N).map N.subtype).le_normalizer_map W.subtype)
      (mem_map_of_mem W.subtype hn)
  have hxX : (x : G) ∈ X := hx
  have hxgen : (⟨x, hxX⟩ : X) ∈ pCore 2 X ⊔ (P : Subgroup X) := by
    have hgen : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
      apply (map_injective X.subtype_injective)
      simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, pCoreIn]
        using sylow_sup hq P
    rw [hgen]
    trivial
  obtain ⟨c, hc, a, ha, hca⟩ := mem_sup_of_normal_left.mp hxgen
  have hcG : (c : G) ∈ X.pCoreIn 2 := mem_map_of_mem X.subtype hc
  have hprod : (c : G) * ((a : G) * (n : G)) = t := by
    have he := congrArg (fun z : X => (z : G)) hca
    have he' := congrArg (fun z : W => (z : G)) hxn
    change (c : G) * (a : G) = (x : G) at he
    change (x : G) * (n : G) = t at he'
    rw [← mul_assoc, he, he']
  have hanT : (a : G) * (n : G) ∈ T := by
    have hh := T.mul_mem (T.inv_mem (hcT hcG)) ht
    rw [← hprod] at hh
    simpa only [inv_mul_cancel_left] using hh
  have hanN : (a : G) * (n : G) ∈
      normalizer ((P : Subgroup X).map X.subtype : Set G) :=
    (normalizer _).mul_mem (le_normalizer (mem_map_of_mem X.subtype ha)) hnG
  exact hprod ▸ mul_mem_sup hcG ⟨hanT, hanN⟩

/-- The complement identifies P with the actual quotient X/O₂(X). -/
noncomputable def sylowQuotientEquiv [Finite G] {X : Subgroup G} {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : IsPGroup p (XiQuotient X)) (P : Sylow p X) : P ≃* XiQuotient X := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let f : P →* XiQuotient X := q.comp (P : Subgroup X).subtype
  apply MulEquiv.ofBijective f
  constructor
  · apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    have hc : (a : X) ∈ pCore 2 X := (QuotientGroup.eq_one_iff _).mp ha
    have hd : Disjoint (pCore 2 X) (P : Subgroup X) :=
      pCore_isPGroup.disjoint_of_coprime P.isPGroup' (Nat.coprime_two_left.mpr ho)
    exact Subtype.ext (hd.le_bot ⟨hc, a.property⟩)
  · apply MonoidHom.range_eq_top.mp
    have htop : (P : Subgroup X).map q = ⊤ :=
      top_unique ((hq.to_subgroup ⊤).le_sylow_of_normal
        (P.mapSurjective (QuotientGroup.mk'_surjective _)))
    simpa only [f, MonoidHom.range_comp, range_subtype] using htop

/-- The complement equivalence is the quotient projection on every element. -/
theorem sylowQuotientEquiv_apply [Finite G] {X : Subgroup G} {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : IsPGroup p (XiQuotient X)) (P : Sylow p X) (a : P) :
    sylowQuotientEquiv ho hq P a = QuotientGroup.mk' (pCore 2 X) (a : X) := rfl


private theorem frattini_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    refine ⟨e.symm b, frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective hb, ?_⟩
    exact e.apply_symm_apply b

/-- The same Sylow complement equivalence for its ambient image. -/
noncomputable def ambientSylowQuotientEquiv [Finite G] {X : Subgroup G} {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : IsPGroup p (XiQuotient X)) (P : Sylow p X) :
    ((P : Subgroup X).map X.subtype) ≃* XiQuotient X := by
  let P₀ := (P : Subgroup X).map X.subtype
  let i : P₀ →* X := inclusion (map_subtype_le (P : Subgroup X))
  let f := (QuotientGroup.mk' (pCore 2 X)).comp i
  apply MulEquiv.ofBijective f
  constructor
  · apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    have hc : i a ∈ pCore 2 X := (QuotientGroup.eq_one_iff _).mp ha
    have hca : (a : G) ∈ X.pCoreIn 2 := mem_map_of_mem X.subtype hc
    exact Subtype.ext (((isPGroup_pCoreIn 2 X).disjoint_of_coprime (P.isPGroup'.map X.subtype) (Nat.coprime_two_left.mpr ho)).le_bot ⟨hca, a.property⟩)
  · intro y
    obtain ⟨a, ha⟩ := (sylowQuotientEquiv ho hq P).surjective y
    refine ⟨⟨a, mem_map_of_mem X.subtype a.property⟩, ?_⟩
    exact ha

/-- The induced equivalence of Frattini quotients, retaining the actual quotient maps. -/
noncomputable def sylowFrattiniEquiv [Finite G] {X : Subgroup G} {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : IsPGroup p (XiQuotient X)) (P : Sylow p X) :
    (((P : Subgroup X).map X.subtype) ⧸ frattini ((P : Subgroup X).map X.subtype)) ≃*
      XiFrattiniQuotient X := by
  exact QuotientGroup.congr _ _ (ambientSylowQuotientEquiv ho hq P)
    (by exact frattini_map_equiv _)

/-- Naturality of the Frattini equivalence on elements of the ambient Sylow subgroup. -/
theorem sylowFrattiniEquiv_apply_mk [Finite G] {X : Subgroup G} {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : IsPGroup p (XiQuotient X)) (P : Sylow p X)
    (a : (P : Subgroup X).map X.subtype) :
    sylowFrattiniEquiv ho hq P (QuotientGroup.mk' _ a) =
      QuotientGroup.mk' (frattini (XiQuotient X))
        (QuotientGroup.mk' (pCore 2 X) (inclusion (map_subtype_le (P : Subgroup X)) a)) := rfl

/-- Members of O₂(X) act trivially on the iterated quotient used to define Ξ. -/
theorem core_fixes_frattini {T X : Subgroup G} (invariant : T ≤ normalizer X)
    (t : T) (ht : (t : G) ∈ X.pCoreIn 2) (v : XiFrattiniQuotient X) :
    xiFrattiniAction T X invariant t v = v := by
  let _ := conjMulDistribMulActionOfLeNormalizer T X invariant
  obtain ⟨n, hn, he⟩ := ht
  change (n : G) = (t : G) at he
  induction v using QuotientGroup.induction_on with | H v =>
    induction v using QuotientGroup.induction_on with | H x =>
      change xiFrattiniAction T X invariant t
        (QuotientGroup.mk' (frattini (XiQuotient X)) (QuotientGroup.mk' (pCore 2 X) x)) =
        QuotientGroup.mk' (frattini (XiQuotient X)) (QuotientGroup.mk' (pCore 2 X) x)
      simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk]
      have heq : (MulDistribMulAction.toMulAut T X t) x = n * x * n⁻¹ := by
        apply Subtype.ext
        change (t : G) * (x : G) * (t : G)⁻¹ = (n : G) * (x : G) * (n : G)⁻¹
        rw [he]
      have hnq : QuotientGroup.mk' (pCore 2 X) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [heq]
      simp only [map_mul, map_inv, hnq, one_mul, inv_one, mul_one]

/-- The normalizer and the defining T-action agree through the Sylow complement isomorphism. -/
theorem sylowFrattiniEquiv_equivariant [Finite G] {T X : Subgroup G}
    (invariant : T ≤ normalizer X) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : IsPGroup p (XiQuotient X)) (P : Sylow p X)
    (s : (T ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G) : Subgroup G))
    (v : ((P : Subgroup X).map X.subtype) ⧸ frattini ((P : Subgroup X).map X.subtype)) :
    sylowFrattiniEquiv ho hq P
      (frattiniConjugationAction _ _ inf_le_right s v) =
      xiFrattiniAction T X invariant ⟨s, s.property.1⟩
        (sylowFrattiniEquiv ho hq P v) := by
  induction v using QuotientGroup.induction_on with | H a =>
    change sylowFrattiniEquiv ho hq P
      (frattiniConjugationAction _ _ inf_le_right s (QuotientGroup.mk' _ a)) =
      xiFrattiniAction T X invariant ⟨s, s.property.1⟩
        (sylowFrattiniEquiv ho hq P (QuotientGroup.mk' _ a))
    simp only [frattiniConjugationAction, MonoidHom.comp_apply, quotientAut_apply_mk,
      sylowFrattiniEquiv_apply_mk, xiFrattiniAction]
    rfl

/-- Frattini factorization transports a proved action to the normalizer of any Sylow complement. -/
theorem normalizer_irreducible [Finite G] {T X : Subgroup G}
    (invariant : T ≤ normalizer X) (hcT : X.pCoreIn 2 ≤ T)
    (irreducible : ∀ B : Subgroup (XiFrattiniQuotient X),
      (∀ t : T, ∀ b ∈ B, xiFrattiniAction T X invariant t b ∈ B) → B = ⊥ ∨ B = ⊤)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hq : IsPGroup p (XiQuotient X))
    (P : Sylow p X) :
    let P₀ := (P : Subgroup X).map X.subtype
    let S := T ⊓ normalizer (P₀ : Set G)
    ∀ A : Subgroup (P₀ ⧸ frattini P₀),
      (∀ s : S, ∀ a ∈ A, frattiniConjugationAction S P₀ inf_le_right s a ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  dsimp only
  intro A hA
  let e := sylowFrattiniEquiv ho hq P
  let B := A.map e.toMonoidHom
  let S := T ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G)
  have hS : S ≤ normalizer (X.pCoreIn 2 : Set G) :=
    inf_le_left.trans (invariant.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hB : ∀ t : T, ∀ b ∈ B, xiFrattiniAction T X invariant t b ∈ B := by
    intro t b hb
    have ht : (t : G) ∈ X.pCoreIn 2 ⊔ S := normalizer_factor invariant hcT hq P ▸ t.property
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hS] at ht
    obtain ⟨c, hc, s, hs, hcs⟩ := ht
    let cT : T := ⟨c, hcT hc⟩
    let sT : T := ⟨s, hs.1⟩
    have hts : t = cT * sT := Subtype.ext hcs.symm
    rw [hts, map_mul]
    change xiFrattiniAction T X invariant cT
      (xiFrattiniAction T X invariant sT b) ∈ B
    rw [core_fixes_frattini invariant cT hc]
    obtain ⟨a, ha, rfl⟩ := hb
    exact mem_map.mpr ⟨frattiniConjugationAction S _ inf_le_right ⟨s, hs⟩ a,
      hA ⟨s, hs⟩ a ha, sylowFrattiniEquiv_equivariant invariant ho hq P ⟨s, hs⟩ a⟩
  rcases irreducible B hB with hb | hb
  · left
    exact (A.map_eq_bot_iff_of_injective e.injective).mp hb
  · right
    apply (map_injective e.injective)
    change A.map e.toMonoidHom = (⊤ : Subgroup _).map e.toMonoidHom
    rw [map_top_of_surjective e.toMonoidHom e.surjective]
    exact hb



/-- Enlarging the actor enlarges its actual automizer. -/
theorem automizer_mono {S T P : Subgroup G} (hST : S ≤ T) :
    XiEmbedding.automizer S P ≤ XiEmbedding.automizer T P := by
  rintro a ⟨s, rfl⟩
  exact ⟨⟨s, hST s.property.1, s.property.2⟩, rfl⟩

/-- Noncyclicity on the Frattini quotient implies noncyclicity of the full automizer. -/
theorem automizer_not_isCyclic_of_frattini {T P : Subgroup G}
    (h : ¬ IsCyclic (frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right).range) :
    ¬ IsCyclic (XiEmbedding.automizer T P) := by
  intro hc
  let := hc
  apply h
  have he : frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right =
      (quotientAut (frattini P)).comp
        (P.normalizerMonoidHom.comp (inclusion (show T ⊓ normalizer P ≤ normalizer P from
          inf_le_right))) := rfl
  rw [he, MonoidHom.range_comp]
  exact isCyclic_of_surjective
    ((quotientAut (frattini P)).subgroupMap (XiEmbedding.automizer T P))
    ((quotientAut (frattini P)).subgroupMap_surjective _)

end CFSG.Quasithin.Chapter1.RadicalActions
