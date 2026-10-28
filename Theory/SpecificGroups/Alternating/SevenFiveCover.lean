module

public import Theory.SpecificGroups.Alternating.SevenFiveSeed
public import Theory.GroupTheory.PerfectCentralCoverLocalResidual
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The literal five-letter seed in an odd central A₇ cover

Take the perfect residual of the inverse image of the actual chosen A₅
subgroup, including each conjugate of the pointwise-two stabilizer. It maps
onto that exact subgroup. Its central kernel has odd order
because the ambient two-core is trivial. The odd-prime ranks of A₅ are at most
one, so the proved cyclic-Sylow transfer theorem makes this projection
injective. The resulting equivalence is the restriction of the original map.

This supplies the five-letter seed in the exceptional C.1.24 argument without
assuming that its ambient component is already short or that a cover splits.
Source: Aschbacher–Smith C.1.24, printed pp.130–131, and I.1.2, p.407.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.SevenFiveCover
open Theory.SpecificGroups.Alternating.SevenFiveSeed
variable {Q : Type*} [Group Q] [Finite Q]

private theorem five_perfect (F : Subgroup (alternatingGroup (Fin 7)))
    (e : F ≃* alternatingGroup (Fin 5)) : Group.IsPerfect F := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem five_odd_rank (F : Subgroup (alternatingGroup (Fin 7)))
    (e : F ≃* alternatingGroup (Fin 5)) (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p F ≤ 1 := by
  rw [primeRank_equiv p e,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 p hp (by
      intro he
      rw [he] at ho
      norm_num at ho)]
  have hthree : 3 ≤ p := by
    have htwo := hp.two_le
    have hne : p ≠ 2 := by intro he; rw [he] at ho; norm_num at ho
    omega
  exact (Nat.div_le_div_left hthree (by decide)).trans (by decide : 5 / 3 ≤ 1)

/-- The ambient perfect residual over the literal pointwise-two stabilizer. -/
def fiveLift (q : Q →* alternatingGroup (Fin 7))
    (F : Subgroup (alternatingGroup (Fin 7))) : Subgroup Q :=
  (solvableResidual (F.comap q)).map (F.comap q).subtype

instance fiveLift_perfect (q : Q →* alternatingGroup (Fin 7))
    (F : Subgroup (alternatingGroup (Fin 7))) :
    Group.IsPerfect (fiveLift q F) := Group.IsPerfect.map _

/-- The residual covers the exact marked A₅, not just an isomorphic subgroup. -/
theorem fiveLift_map (q : Q →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (F : Subgroup (alternatingGroup (Fin 7))) (e : F ≃* alternatingGroup (Fin 5)) :
    (fiveLift q F).map q = F := by
  let := five_perfect F e
  rw [fiveLift, map_solvableResidual_comap q hq, solvableResidual_eq_top,
    ← MonoidHom.range_eq_map, range_subtype]

/-- Restrict the original projection to the constructed perfect seed. -/
def fiveLiftMap (q : Q →* alternatingGroup (Fin 7))
    (F : Subgroup (alternatingGroup (Fin 7))) : fiveLift q F →* F where
  toFun x := ⟨q x, by
    obtain ⟨y, _, hy⟩ := x.property
    exact hy ▸ y.property⟩
  map_one' := Subtype.ext q.map_one
  map_mul' x y := Subtype.ext (q.map_mul x y)

/-- Surjectivity comes from preservation of the finite perfect residual. -/
theorem fiveLiftMap_surjective (q : Q →* alternatingGroup (Fin 7))
    (hq : Function.Surjective q) (F : Subgroup (alternatingGroup (Fin 7)))
    (e : F ≃* alternatingGroup (Fin 5)) : Function.Surjective (fiveLiftMap q F) := by
  intro x
  obtain ⟨y, hy, he⟩ := (fiveLift_map q hq F e).ge x.property
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- Odd central kernel and the actual A₅ odd-rank bound make the restriction injective. -/
theorem fiveLiftMap_injective [Group.IsPerfect Q]
    (q : Q →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ center Q) (hcore : pCore 2 Q = ⊥)
    (F : Subgroup (alternatingGroup (Fin 7))) (e : F ≃* alternatingGroup (Fin 5)) :
    Function.Injective (fiveLiftMap q F) := by
  let c : PerfectCentralCovering.Cover Q (alternatingGroup (Fin 7)) :=
    ⟨q, hq, inferInstance, hcentral⟩
  have hi := c.injective_on_perfect_subgroup hcore (fiveLift q F) (fun p hp ho => by
    change primeRank p ((fiveLift q F).map q) ≤ 1
    rw [fiveLift_map q hq F e]
    exact five_odd_rank F e p hp ho)
  intro x y hxy
  apply hi
  apply Subtype.ext
  change q (x : Q) = q (y : Q)
  exact congrArg (fun z : F => (z : alternatingGroup (Fin 7))) hxy

/-- The exact perfect seed is identified with the marked five-letter subgroup
by the original quotient projection. -/
noncomputable def fiveLiftEquiv [Group.IsPerfect Q]
    (q : Q →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ center Q) (hcore : pCore 2 Q = ⊥)
    (F : Subgroup (alternatingGroup (Fin 7))) (e : F ≃* alternatingGroup (Fin 5)) :
    fiveLift q F ≃* F :=
  MulEquiv.ofBijective (fiveLiftMap q F)
    ⟨fiveLiftMap_injective q hq hcentral hcore F e, fiveLiftMap_surjective q hq F e⟩

@[simp] theorem fiveLiftEquiv_apply [Group.IsPerfect Q]
    (q : Q →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ center Q) (hcore : pCore 2 Q = ⊥)
    (F : Subgroup (alternatingGroup (Fin 7))) (e : F ≃* alternatingGroup (Fin 5))
    (x : fiveLift q F) :
    (fiveLiftEquiv q hq hcentral hcore F e x : alternatingGroup (Fin 7)) = q x := rfl

/-- Application to the original central quotient of the intrinsic component,
with the same chosen A₅ subgroup and the same central-quotient marking. -/
noncomputable def fiveLiftEquivOfCentralQuotient [IsQuasisimple Q]
    (eQ : (Q ⧸ center Q) ≃* alternatingGroup (Fin 7)) (hcore : pCore 2 Q = ⊥)
    (F : Subgroup (alternatingGroup (Fin 7))) (e : F ≃* alternatingGroup (Fin 5)) :
    fiveLift (eQ.toMonoidHom.comp (QuotientGroup.mk' (center Q))) F ≃* F :=
  fiveLiftEquiv _ (eQ.surjective.comp (QuotientGroup.mk'_surjective _))
    (by rw [MonoidHom.ker_comp_of_injective _ _ eQ.injective, QuotientGroup.ker_mk'])
    hcore F e

@[simp] theorem fiveLiftEquivOfCentralQuotient_apply [IsQuasisimple Q]
    (eQ : (Q ⧸ center Q) ≃* alternatingGroup (Fin 7)) (hcore : pCore 2 Q = ⊥)
    (F : Subgroup (alternatingGroup (Fin 7))) (e : F ≃* alternatingGroup (Fin 5))
    (x : fiveLift (eQ.toMonoidHom.comp (QuotientGroup.mk' (center Q))) F) :
    (fiveLiftEquivOfCentralQuotient eQ hcore F e x : alternatingGroup (Fin 7)) =
      eQ (QuotientGroup.mk' (center Q) (x : Q)) := rfl

/-- Every actual two-subgroup over the chosen A₅ lies in its perfect lift.
The quotient of the full preimage by its residual is an odd central image. -/
theorem two_subgroup_le_fiveLift
    (q : Q →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ center Q) (hcore : pCore 2 Q = ⊥)
    (F : Subgroup (alternatingGroup (Fin 7))) (e : F ≃* alternatingGroup (Fin 5))
    (A : Subgroup Q) (hA : IsPGroup 2 A) (himage : A.map q ≤ F) :
    A ≤ fiveLift q F := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := five_perfect F e
  let R := F.comap q
  let f := q.subgroupComap F
  have hf : Function.Surjective f := q.subgroupComap_surjective_of_surjective F hq
  have hAR : A ≤ R := map_le_iff_le_comap.mp himage
  let s := QuotientGroup.mk' (solvableResidual R)
  have hsup : solvableResidual R ⊔ f.ker = ⊤ := by
    rw [← comap_map_eq, map_solvableResidual_eq f hf, solvableResidual_eq_top, comap_top]
  have hstop : f.ker.map s = ⊤ := by
    have hm := congrArg (Subgroup.map s) hsup
    have hn : (solvableResidual R).map s = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    simpa only [Subgroup.map_sup, hn, bot_sup_eq, map_top_of_surjective s
      (QuotientGroup.mk'_surjective _)] using hm
  have hodd : Odd (Nat.card f.ker) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    intro hd
    have hc : f.ker.map R.subtype ≤ center Q := by
      rintro _ ⟨x, hx, rfl⟩
      exact hcentral (congrArg (fun z : F => (z : alternatingGroup (Fin 7))) hx)
    apply PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hcore _ hc
    rwa [card_map_of_injective R.subtype_injective]
  have hp := (hA.comap_of_injective R.subtype R.subtype_injective).map s
  have hd : Disjoint ((A.subgroupOf R).map s) (f.ker.map s) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    change (Nat.card ((A.comap R.subtype).map s)).Coprime _
    rw [hn]
    exact (hodd.coprime_two_left.coprime_dvd_right (f.ker.card_map_dvd s)).pow_left n
  intro a ha
  have he : s ⟨a, hAR ha⟩ = 1 := hd.le_bot
    ⟨mem_map_of_mem s ha, hstop ▸ mem_top _⟩
  exact mem_map_of_mem R.subtype ((QuotientGroup.eq_one_iff _).mp he)

omit [Finite Q] in
/-- Every specified actor preserving the chosen A₅ image normalizes its
literal perfect-residual lift. -/
theorem normalizes_fiveLift_of_map
    (q : Q →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (F : Subgroup (alternatingGroup (Fin 7))) (A : Subgroup Q)
    (himage : A.map q ≤ normalizer (F : Set (alternatingGroup (Fin 7)))) :
    A ≤ normalizer (fiveLift q F : Set Q) := by
  have hpre : A ≤ normalizer (F.comap q : Set Q) := by
    rw [← comap_normalizer_eq_of_surjective F hq]
    exact map_le_iff_le_comap.mp himage
  exact hpre.trans (normalizer_le_normalizer_characteristic_image
    (F.comap q) (solvableResidual (F.comap q)))

end Theory.SpecificGroups.Alternating.SevenFiveCover
