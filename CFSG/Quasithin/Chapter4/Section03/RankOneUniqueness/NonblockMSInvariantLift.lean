module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSRankBounds
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCore
public import Theory.Representation.SL3.DualInvariantLines

/-!
# A Sylow-invariant elementary lift in the original MS core

The literal MS quotient identifies every K-invariant subgroup strictly
between U and Q with one of the 2^n+1 diagonal dual lifts. All of them are
elementary of order 2^(6n), minimal above U and self-centralizing in Q.
Conjugation by the original two-group S permutes this odd family, so it
fixes a member A. Thus KS normalizes an actual elementary A with U<A<Q
and C_Q(A)=A, supplying the choice of W₁ for the action-normalizer argument.

The larger-core equality Q=O₂(KS), construction of MSData and the secondary
component, and the terminal representation exclusion remain obligations of
qt-d-1222-rankone-uniqueness-nonblock. No such conclusion is assumed here.
Source: Aschbacher--Smith, C.1.35, printed pp.137--139, applied in
original 4.3.11, printed p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open Representation.SL3ParabolicNatural
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The actual K-invariant subgroups properly between U and Q. -/
def invariantCoreLifts (c : SourceConfiguration T L) :=
  {A : Subgroup G // U c < A ∧ A < Q c ∧ K c ≤ normalizer (A : Set G)}

private def indexedLift (d : MSData c n)
    (p : Q c →* Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
      Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))
    (a : Option d.field.Carrier) : Subgroup G :=
  ((dualLine a).comap p).map (Q c).subtype

private theorem indexedLift_injective (d : MSData c n)
    (p : Q c →* Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
      Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))
    (hp : Function.Surjective p) : Function.Injective (indexedLift d p) := by
  intro a b he
  apply dualLine_injective
  apply comap_injective hp
  exact map_injective (Q c).subtype_injective he

private theorem lift_classification (d : MSData c n)
    (p : Q c →* Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
      Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))
    (hk : p.ker = (U c).subgroupOf (Q c))
    (he : ∀ (k : K c) (q r : Q c), (r : G) = k*q*(k : G)⁻¹ →
      (p r).toAdd =
        ((Representation.specialLinearNatural 3).dual.prod
          (Representation.specialLinearNatural 3).dual)
            (linearThreeActor d.model k) (p q).toAdd)
    (A : invariantCoreLifts c) : ∃ a : Option d.field.Carrier, A.val = indexedLift d p a := by
  let B := (A.val.subgroupOf (Q c)).map p
  have hker : p.ker ≤ A.val.subgroupOf (Q c) := by
    rw [hk]
    exact fun x hx => A.property.1.le hx
  have hrecover : (B.comap p).map (Q c).subtype = A.val := by
    rw [comap_map_eq_self hker,map_subgroupOf_eq_of_le A.property.2.1.le]
  have hb : B ≠ ⊥ := by
    intro hh
    have hh' := hrecover
    rw [hh,MonoidHom.comap_bot,hk,map_subgroupOf_eq_of_le d.doubleDual.1] at hh'
    exact A.property.1.ne hh'
  have ht : B ≠ ⊤ := by
    intro hh
    have hh' := hrecover
    rw [hh,comap_top,←MonoidHom.range_eq_map,range_subtype] at hh'
    exact A.property.2.1.ne hh'.symm
  have hinv : ∀ g : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier, ∀ v ∈ B,
      Multiplicative.ofAdd
        ((Representation.specialLinearNatural 3).dual g v.toAdd.1,
          (Representation.specialLinearNatural 3).dual g v.toAdd.2) ∈ B := by
    intro g v hv
    obtain ⟨k,hk'⟩ := d.model.surjective.comp (QuotientGroup.mk'_surjective _) g
    obtain ⟨q,hq,rfl⟩ := hv
    let r : Q c := ⟨(k : G)*q*(k : G)⁻¹,
      (mem_normalizer_iff.mp (d.doubleDual.2.1 k.property) q).mp q.property⟩
    refine ⟨r,?_,?_⟩
    · exact (mem_normalizer_iff.mp (A.property.2.2 k.property) q).mp hq
    · apply Multiplicative.toAdd.injective
      have hh := he k q r rfl
      rw [show linearThreeActor d.model k = g from hk'] at hh
      exact hh
  obtain ⟨a,ha⟩ := invariant_dual_subgroup_eq_line B hb ht hinv
  exact ⟨a, hrecover.symm.trans (by rw [ha]; rfl)⟩

private theorem indexedLift_properties (d : MSData c n)
    (p : Q c →* Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
      Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))
    (hl : ∀ a b : d.field.Carrier,
      IsElementaryAbelian 2 (dualLift d p a b) ∧
      U c ≤ dualLift d p a b ∧ dualLift d p a b ≤ Q c ∧
      K c ≤ normalizer (dualLift d p a b : Set G) ∧
      (a ≠ 0 ∨ b ≠ 0 → Nat.card (dualLift d p a b) = 2^(6*n)))
    (a : Option d.field.Carrier) :
    IsElementaryAbelian 2 (indexedLift d p a) ∧ Nat.card (indexedLift d p a) = 2^(6*n) ∧
      U c < indexedLift d p a ∧ indexedLift d p a < Q c ∧
      K c ≤ normalizer (indexedLift d p a : Set G) := by
  have hh : IsElementaryAbelian 2 (indexedLift d p a) ∧
      U c ≤ indexedLift d p a ∧ indexedLift d p a ≤ Q c ∧
      K c ≤ normalizer (indexedLift d p a : Set G) ∧
      Nat.card (indexedLift d p a) = 2^(6*n) := by
    cases a with
    | none => exact ⟨(hl 0 1).1,(hl 0 1).2.1,(hl 0 1).2.2.1,
        (hl 0 1).2.2.2.1,(hl 0 1).2.2.2.2 (Or.inr one_ne_zero)⟩
    | some a => exact ⟨(hl 1 a).1,(hl 1 a).2.1,(hl 1 a).2.2.1,
        (hl 1 a).2.2.2.1,(hl 1 a).2.2.2.2 (Or.inl one_ne_zero)⟩
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one d.pair.positive
  have hu : Nat.card (U c) = 2^(3*n) := by
    rw [card_map_of_injective (Q c).subtype_injective,d.center_card]
  refine ⟨hh.1,hh.2.2.2.2,lt_of_le_of_ne hh.2.1 ?_,
    lt_of_le_of_ne hh.2.2.1 ?_,hh.2.2.2.1⟩
  · intro he
    have hc := congrArg (fun B : Subgroup G => Nat.card B) he
    rw [hu,hh.2.2.2.2] at hc
    have := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    omega
  · intro he
    have hc := congrArg (fun B : Subgroup G => Nat.card B) he
    rw [hh.2.2.2.2,d.core_card] at hc
    have := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    omega

/-- The original K-invariant intermediate subgroups form a projective line
of order 2^n+1, through the original doubled-dual quotient map. -/
theorem MSData.invariantCoreLifts_card (d : MSData c n) :
    Nat.card (invariantCoreLifts c) = 2^n+1 := by
  obtain ⟨p,hp,hk,he,hl⟩ := d.exists_elementary_dual_lifts
  let f : Option d.field.Carrier → invariantCoreLifts c := fun a =>
    ⟨indexedLift d p a,(indexedLift_properties d p hl a).2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact indexedLift_injective d p hp (congrArg Subtype.val hab)
    · intro A
      obtain ⟨a,ha⟩ := lift_classification d p hk he A
      exact ⟨a,Subtype.ext ha.symm⟩
  let := Fintype.ofFinite d.field.Carrier
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_eq_fintype_card,Fintype.card_option,
    ←Nat.card_eq_fintype_card,d.field.card_eq,d.degree_eq]

/-- Every member of that intrinsic family is an elementary abelian subgroup
of the original Q, of order 2^(6n). -/
theorem MSData.invariantCoreLifts_elementary (d : MSData c n) (A : invariantCoreLifts c) :
    IsElementaryAbelian 2 A.val ∧ Nat.card A.val = 2^(6*n) := by
  obtain ⟨p,hp,hk,he,hl⟩ := d.exists_elementary_dual_lifts
  obtain ⟨a,ha⟩ := lift_classification d p hk he A
  rw [ha]
  exact ⟨(indexedLift_properties d p hl a).1,(indexedLift_properties d p hl a).2.1⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private def conjugateLift (c : SourceConfiguration T L) (s : S c)
    (A : invariantCoreLifts c) : invariantCoreLifts c := by
  let e := MulAut.conj (s : G)
  have hQ : (Q c).map e.toMonoidHom = Q c :=
    mem_normalizer_iff_map_conj_eq.mp (core_normalized c s.property.2)
  have hU : (U c).map e.toMonoidHom = U c :=
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c))
        (core_normalized c s.property.2))
  have hK : (K c).map e.toMonoidHom = K c :=
    mem_normalizer_iff_map_conj_eq.mp (c.normalizer_component.le s.property.2)
  refine ⟨A.val.map e.toMonoidHom,?_,?_,?_⟩
  · have hh := (map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr A.property.1
    rwa [hU] at hh
  · have hh := (map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr A.property.2.1
    rwa [hQ] at hh
  · have hh := map_mono (f := e.toMonoidHom) A.property.2.2
    rwa [hK,map_equiv_normalizer_eq] at hh

/-- Each member gives an irreducible K-section above the original center U. -/
theorem MSData.invariantCoreLifts_minimal [Finite G]
    (d : MSData c n) (A : invariantCoreLifts c)
    (B : Subgroup G) (hUB : U c ≤ B) (hBA : B ≤ A.val)
    (hn : K c ≤ normalizer (B : Set G)) : B = U c ∨ B = A.val := by
  by_cases he : B = U c
  · exact Or.inl he
  let E : invariantCoreLifts c :=
    ⟨B,lt_of_le_of_ne hUB (Ne.symm he),lt_of_le_of_lt hBA A.property.2.1,hn⟩
  have hcard : Nat.card A.val = Nat.card B :=
    (d.invariantCoreLifts_elementary A).2.trans (d.invariantCoreLifts_elementary E).2.symm
  exact Or.inr (eq_of_le_of_card_ge hBA hcard.le)

/-- Every member of the actual projective-line family is self-centralizing
inside Q. Its centralizer is another K-invariant intermediate subgroup, and
the common order forces equality. -/
theorem MSData.invariantCoreLifts_selfCentralizing [Finite G]
    (d : MSData c n) (A : invariantCoreLifts c) :
    Q c ⊓ Subgroup.centralizer (A.val : Set G) = A.val := by
  let C := Q c ⊓ Subgroup.centralizer (A.val : Set G)
  let := (d.invariantCoreLifts_elementary A).1
  have hAC : A.val ≤ C := le_inf A.property.2.1.le (le_centralizer A.val)
  have hCQ : C < Q c := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hAU : A.val ≤ U c := by
      intro a ha
      refine ⟨⟨a,A.property.2.1.le ha⟩,?_,rfl⟩
      apply mem_center_iff.mpr
      intro q
      apply Subtype.ext
      have hq : (q : G) ∈ C := he.ge q.property
      exact (mem_centralizer_iff.mp hq.2 a ha).symm
    exact A.property.1.not_ge hAU
  have hn : K c ≤ normalizer (C : Set G) :=
    (le_inf d.doubleDual.2.1
      (A.property.2.2.trans (normalizer_le_normalizer_centralizer A.val))).trans
        inf_normalizer_le_normalizer_inf
  let B : invariantCoreLifts c := ⟨C,lt_of_lt_of_le A.property.1 hAC,hCQ,hn⟩
  have hcard : Nat.card C = Nat.card A.val :=
    (d.invariantCoreLifts_elementary B).2.trans (d.invariantCoreLifts_elementary A).2.symm
  exact (eq_of_le_of_card_ge hAC hcard.le).symm

/-- The original Sylow intersection normalizes an actual elementary lift of
an irreducible dual summand. This is the choice of W₁ in C.1.35's core argument;
no action-normalizer or larger-core equality is assumed. -/
theorem MSData.exists_sylow_invariant_elementary_lift [Finite G] (d : MSData c n) :
    ∃ A : Subgroup G, U c < A ∧ A < Q c ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 2^(6*n) ∧
      K c ⊔ S c ≤ normalizer (A : Set G) ∧
      Q c ⊓ Subgroup.centralizer (A : Set G) = A ∧
      (∀ B : Subgroup G, U c ≤ B → B ≤ A → K c ≤ normalizer (B : Set G) →
        B = U c ∨ B = A) := by
  let : MulAction (S c) (invariantCoreLifts c) := {
    smul := conjugateLift c
    one_smul := fun A => Subtype.ext (by
      change A.val.map (MulAut.conj (1 : G)).toMonoidHom = A.val
      have hi : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      rw [hi,map_id])
    mul_smul := fun s t A => Subtype.ext (by
      change A.val.map (MulAut.conj ((s : G)*(t : G))).toMonoidHom =
        (A.val.map (MulAut.conj (t : G)).toMonoidHom).map
          (MulAut.conj (s : G)).toMonoidHom
      rw [map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply,mul_assoc]) }
  have hodd : ¬2 ∣ Nat.card (invariantCoreLifts c) := by
    rw [d.invariantCoreLifts_card]
    have hn : n ≠ 0 := by have := d.pair.positive; omega
    simp [Nat.dvd_iff_mod_eq_zero,Nat.add_mod,Nat.pow_mod,hn]
  have hS := T.isPGroup'.to_le (show S c ≤ (T : Subgroup G) from inf_le_left)
  obtain ⟨A,hA⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (invariantCoreLifts c) hodd
  have hfix (s : S c) : A.val.map (MulAut.conj (s : G)).toMonoidHom = A.val :=
    congrArg Subtype.val (hA s)
  have he := d.invariantCoreLifts_elementary A
  exact ⟨A.val,A.property.1,A.property.2.1,he.1,he.2,
    sup_le A.property.2.2 (fun s hs => mem_normalizer_iff_map_conj_eq.mpr (hfix ⟨s,hs⟩)),
    d.invariantCoreLifts_selfCentralizing A,d.invariantCoreLifts_minimal A⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
