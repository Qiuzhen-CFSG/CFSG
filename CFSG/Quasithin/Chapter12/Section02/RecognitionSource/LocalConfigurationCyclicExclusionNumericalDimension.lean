module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionCoreResidual
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicBlockAction
public import Theory.SpecificGroups.BinaryLinear.PrimeIndexFixedLine

/-!
# The prime and dimension in the extraspecial branch

Normality of Y=Φ(P)W and W≤T give the literal factorization Φ(P)T and its
relative index p over T. The full action on the natural module sends T to
a full Sylow subgroup of GL(V). Faithfulness of Φ(P) preserves the prime
index in this image. The chosen natural marking carries its literal fixed
subgroup of order two to the fixed line in the binary linear space.
The prime-index flag theorem then gives p=d=3.

The companion numerical-size module completes |W|=64 and the numerical
assembly applies both conclusions to the actual cyclic-block consumer.
Source: Aschbacher–Smith, 12.2.23, printed p.803.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}
namespace InvariantOddLocalAnalysis
variable (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
include S

omit [Finite G] in
/-- The canonical elementary orbit lies in the prescribed Sylow subgroup. -/
theorem module_le_sylow : W ≤ (T : Subgroup G) := by
  have hTH : (T : Subgroup G) ≤ H := S.overgroup ▸ le_sup_right
  apply S.in_core.trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
    pCoreIn_le_sylow H (T.subtype hTH)

/-- The Frattini subgroup and the prescribed Sylow form the literal product. -/
theorem extraspecial_frattini_sylow_factorization (he : IsExtraspecial p P) :
    ∀ x ∈ (frattini P).map P.subtype ⊔ (T : Subgroup G),
      ∃ a ∈ (frattini P).map P.subtype, ∃ t ∈ (T : Subgroup G), x = a * t := by
  let Φ := (frattini P).map P.subtype
  let Y := Φ ⊔ W
  have hTH : (T : Subgroup G) ≤ H := S.overgroup ▸ le_sup_right
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    hTH.trans (S.extraspecial_frattini_module_normal he)
  have hΦW : Φ ≤ normalizer (W : Set G) := S.frattini_normalizes_module
  have hjoin : Y ⊔ (T : Subgroup G) = Φ ⊔ (T : Subgroup G) := by
    change (Φ ⊔ W) ⊔ (T : Subgroup G) = _
    rw [sup_assoc, sup_eq_right.mpr S.module_le_sylow]
  intro x hx
  have hxy : x ∈ (Y : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left Y (T : Subgroup G) hTY, hjoin]
    exact hx
  obtain ⟨y, hy, t, ht, rfl⟩ := hxy
  have hyprod : y ∈ (Φ : Set G) * (W : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right Φ W hΦW]
    exact hy
  obtain ⟨a, ha, w, hw, rfl⟩ := hyprod
  exact ⟨a, ha, w * t, (T : Subgroup G).mul_mem (S.module_le_sylow hw) ht, mul_assoc ..⟩

/-- The Frattini-Sylow product has index p over the prescribed Sylow. -/
theorem extraspecial_frattini_sylow_index (he : IsExtraspecial p P) :
    (T : Subgroup G).relIndex ((frattini P).map P.subtype ⊔ (T : Subgroup G)) = p := by
  let Φ := (frattini P).map P.subtype
  let B := Φ ⊔ (T : Subgroup G)
  let m : Φ × T → B := fun z => ⟨z.1 * z.2, mul_mem_sup z.1.property z.2.property⟩
  let : Fact p.Prime := ⟨S.prime⟩
  have hd : Disjoint Φ (T : Subgroup G) :=
    (S.pgroup.to_le (map_subtype_le _)).disjoint_of_coprime T.isPGroup'
      S.odd_prime.coprime_two_right
  have hm : Function.Bijective m := ⟨fun _ _ hh =>
    mul_injective_of_disjoint hd (congrArg Subtype.val hh), by
      intro x
      obtain ⟨a, ha, t, ht, he⟩ := S.extraspecial_frattini_sylow_factorization he x x.property
      exact ⟨(⟨a,ha⟩,⟨t,ht⟩), Subtype.ext he.symm⟩⟩
  have hc : Nat.card B = p * Nat.card T := by
    rw [← Nat.card_congr (Equiv.ofBijective m hm), Nat.card_prod,
      S.frattini_card_of_extraspecial he]
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) (T : Subgroup G) B bot_le le_sup_right
  simp only [relIndex_bot_left, hc] at hi
  rw [Nat.mul_comm p] at hi
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hi

/-- The actual prime-index natural action forces p=d=3. -/
theorem extraspecial_prime_dimension_eq_three
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    p = 3 ∧ d = 3 := by
  let Φ := (frattini P).map P.subtype
  let N := normalizer (V : Set G)
  let B := Φ ⊔ (T : Subgroup G)
  have hBN : B ≤ N := sup_le S.frattini_normalizes hTV
  obtain ⟨_, E, _⟩ := A.natural
  let eAut := MulEquiv.ofBijective (Representation.binaryNaturalAut d)
    (Representation.binaryNaturalAut_bijective d)
  let c : MulAut V ≃* BinaryLinear.OuterCyclic.LinearGroup d :=
    (MulAut.congr E).trans (eAut.symm.trans (BinaryLinear.OuterCyclic.slEquivLinear d))
  have hca (b : MulAut V) (x : V) : c b (E x).toAdd = (E (b x)).toAdd := by
    have hh := congrArg (fun z : MulAut (Multiplicative (Fin d → ZMod 2)) =>
      (z (E x)).toAdd) (eAut.apply_symm_apply (MulAut.congr E b))
    change c b (E x).toAdd = (E (b (E.symm (E x)))).toAdd at hh
    simpa only [E.symm_apply_apply] using hh
  let f := c.toMonoidHom.comp V.normalizerMonoidHom
  have hsur : Function.Surjective f := by
    intro x
    obtain ⟨l, hl⟩ := A.componentAut_surjective D (c.symm x)
    refine ⟨⟨l,D.normalizes l.property⟩, ?_⟩
    change c (V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩) = x
    rw [show V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ = c.symm x from hl,
      c.apply_symm_apply]
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup d) := Finite.of_surjective f hsur
  let R := (T.subtype hTV).mapSurjective hsur
  let B' := (B.subgroupOf N).map f
  let a : Φ →* BinaryLinear.OuterCyclic.LinearGroup d :=
    f.comp (inclusion S.frattini_normalizes)
  have ha : Function.Injective a :=
    c.injective.comp (S.frattini_chosen_action_faithful A he hf)
  have hcarda : Nat.card a.range = p :=
    (Nat.card_congr (MonoidHom.ofInjective ha).toEquiv).symm.trans
      (S.frattini_card_of_extraspecial he)
  have haB : a.range ≤ B' := by
    rintro x ⟨z, rfl⟩
    exact mem_map_of_mem f (show (inclusion S.frattini_normalizes z) ∈ B.subgroupOf N from
      (le_sup_left : Φ ≤ B) z.property)
  have hRB : (R : Subgroup _) ≤ B' := map_mono (comap_mono le_sup_right)
  have hdiv : (R : Subgroup _).relIndex B' ∣ p := by
    have hi : ((T : Subgroup G).subgroupOf N).relIndex (B.subgroupOf N) = p := by
      rw [relIndex_subgroupOf hBN]
      exact S.extraspecial_frattini_sylow_index he
    rw [← hi]
    change (((T : Subgroup G).subgroupOf N).map f).relIndex ((B.subgroupOf N).map f) ∣ _
    rw [← relIndex_comap]
    exact relIndex_dvd_of_le_left (B.subgroupOf N) (le_comap_map _ _)
  have hindex : (R : Subgroup _).relIndex B' = p := by
    rcases (Nat.dvd_prime S.prime).mp hdiv with hi | hi
    · have haR : a.range ≤ (R : Subgroup _) := haB.trans (relIndex_eq_one.mp hi)
      have hp2 := R.isPGroup'.to_le haR
      obtain ⟨n, hn⟩ := hp2.exists_card_eq
      have hd : p ∣ 2 ^ n := by rw [← hn, hcarda]
      have heq : p = 2 := (Nat.prime_dvd_prime_iff_eq S.prime Nat.prime_two).mp
        (S.prime.dvd_of_dvd_pow hd)
      exact (S.odd_prime.not_two_dvd_nat (by rw [heq])).elim
    · exact hi
  have hfixed : Nat.card (BinaryLinear.fixedSpace a.range) = 2 := by
    let C := V ⊓ centralizer (Φ : Set G)
    let ef : C ≃ BinaryLinear.fixedSpace a.range := {
      toFun := fun x => ⟨(E ⟨x,x.property.1⟩).toAdd, by
        rintro z ⟨b,rfl⟩
        have hcomm := x.property.2 b b.property
        have heq : (V.normalizerMonoidHom (inclusion S.frattini_normalizes b))
            (⟨x,x.property.1⟩ : V) = ⟨x,x.property.1⟩ := by
          apply Subtype.ext
          change (b : G) * (x : G) * (b : G)⁻¹ = x
          rw [hcomm, mul_inv_cancel_right]
        change c (V.normalizerMonoidHom (inclusion S.frattini_normalizes b)) _ = _
        rw [hca, heq]⟩
      invFun := fun y => ⟨(E.symm (Multiplicative.ofAdd y.val)).val, by
        refine ⟨(E.symm (Multiplicative.ofAdd y.val)).property, ?_⟩
        intro z hz
        let b : Φ := ⟨z,hz⟩
        have hh := y.property (a b) ⟨b,rfl⟩
        have heq : (E ((V.normalizerMonoidHom (inclusion S.frattini_normalizes b))
            (E.symm (Multiplicative.ofAdd y.val)))).toAdd = y.val := by
          rw [← hca, E.apply_symm_apply]
          exact hh
        have hh' : (V.normalizerMonoidHom (inclusion S.frattini_normalizes b))
            (E.symm (Multiplicative.ofAdd y.val)) = E.symm (Multiplicative.ofAdd y.val) := by
          apply E.injective
          apply Multiplicative.toAdd.injective
          simpa only [E.apply_symm_apply, toAdd_ofAdd] using heq
        have hval := congrArg Subtype.val hh'
        change z * (E.symm (Multiplicative.ofAdd y.val)).val * z⁻¹ =
          (E.symm (Multiplicative.ofAdd y.val)).val at hval
        exact mul_inv_eq_iff_eq_mul.mp hval⟩
      left_inv := fun x => by
        apply Subtype.ext
        change (E.symm (Multiplicative.ofAdd ((E ⟨x,x.property.1⟩).toAdd))).val = x.val
        rw [ofAdd_toAdd]
        exact congrArg (fun z : V => z.val) (E.symm_apply_apply ⟨x,x.property.1⟩)
      right_inv := fun y => by
        apply Subtype.ext
        change (E (E.symm (Multiplicative.ofAdd y.val))).toAdd = y.val
        rw [E.apply_symm_apply, toAdd_ofAdd] }
    rw [← Nat.card_congr ef]
    exact (S.chosen_split_frattini D A hf).2.2
  exact BinaryLinear.small_prime_index_fixed_line S.prime A.dimension R B' a.range
    hRB hindex haB hcarda hfixed

end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
