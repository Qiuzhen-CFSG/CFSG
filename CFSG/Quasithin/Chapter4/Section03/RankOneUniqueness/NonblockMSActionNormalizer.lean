module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSLiftAction
public import Theory.Representation.FirstCohomologyNormalizer
public import Theory.Representation.SL3.DualFirstCohomology
public import Theory.GroupTheory.AutomorphismSectionNormalizer

/-!
# The original nonbinary MS action normalizer

For each invariant elementary lift A, projection from the doubled dual
constructs the literal quotient Q/A. Its self-centralizer identifies Q's
action image with that dual module. The action on U recovers the original
SL₃ quotient of the K-action, with the two-section kernel as its kernel.

First cohomology of the nonbinary dual module vanishes. Together with the
previously proved trivial centralizer in the two-section kernel, this gives
N_R(Kᴬ)=Qᴬ, where R fixes both U and A/U pointwise. In particular O₂(K)
and Q have identical images on A. All maps are the original conjugation maps;
neither Q=O₂(KS) nor a chosen splitting is an assumption.

The larger-core equality, original MS/secondary witness construction and
terminal exclusions remain with qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher–Smith C.1.35, printed p.138, applied at 4.3.11, p.617.
-/


@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open Representation.SL3ParabolicNatural
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private def dualQuotient {F : Type*} [Field F] (i : Option F) :
    Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)) →*
      Multiplicative (Module.Dual F (Fin 3 → F)) where
  toFun v := Multiplicative.ofAdd (match i with
    | none => v.toAdd.1
    | some t => v.toAdd.2 - t • v.toAdd.1)
  map_one' := by cases i <;> simp
  map_mul' v w := by
    cases i with
    | none => rfl
    | some t =>
      apply Multiplicative.toAdd.injective
      change (v.toAdd.2+w.toAdd.2)-t • (v.toAdd.1+w.toAdd.1) = _
      rw [smul_add]
      change _ = (v.toAdd.2-t • v.toAdd.1)+(w.toAdd.2-t • w.toAdd.1)
      abel

theorem MSData.invariantCoreLifts_complement_coordinates (d : MSData c n)
    (A : invariantCoreLifts c) :
    ∃ p : Q c →* Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
      Function.Surjective p ∧ p.ker = A.val.subgroupOf (Q c) ∧
      ∀ (k : K c) (q r : Q c), (r : G) = k*q*(k : G)⁻¹ →
        (p r).toAdd = (Representation.specialLinearNatural 3).dual
          (linearThreeActor d.model k) (p q).toAdd := by
  obtain ⟨p,hp,hk,he,_⟩ := d.exists_elementary_dual_lifts
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
  obtain ⟨i,hi⟩ := invariant_dual_subgroup_eq_line B hb ht hinv
  let f := (dualQuotient i).comp p
  have hmem (q : Q c) : p q ∈ B ↔ (q : G) ∈ A.val := by
    change q ∈ B.comap p ↔ _
    rw [←hrecover]
    exact (mem_map_iff_mem (Q c).subtype_injective).symm
  refine ⟨f,?_,?_,?_⟩
  · intro v
    cases i with
    | none =>
      obtain ⟨q,hq⟩ := hp (Multiplicative.ofAdd (v.toAdd,0))
      exact ⟨q,congrArg (dualQuotient none) hq⟩
    | some t =>
      obtain ⟨q,hq⟩ := hp (Multiplicative.ofAdd (0,v.toAdd))
      refine ⟨q,?_⟩
      change dualQuotient (some t) (p q) = v
      rw [hq]
      simp [dualQuotient]
  · ext q
    change f q = 1 ↔ (q : G) ∈ A.val
    rw [←hmem,hi]
    cases i with
    | none => exact (mem_dualLine_none (p q)).symm
    | some t =>
      rw [mem_dualLine_some]
      change (p q).toAdd.2 - t • (p q).toAdd.1 = 0 ↔ _
      exact sub_eq_zero
  · intro k q r hqr
    have hh := he k q r hqr
    cases i with
    | none => exact congrArg Prod.fst hh
    | some t =>
      change (p r).toAdd.2 - t • (p r).toAdd.1 = _
      rw [hh]
      simp [f,dualQuotient,Representation.prod,map_sub,map_smul]

private theorem center_coordinates (d : MSData c n) :
    ∃ e : U c ≃* Multiplicative (Fin 3 → d.field.Carrier),
      ∀ (k : K c) (u v : U c), (v : G) = k*u*(k : G)⁻¹ →
        (e v).toAdd = Representation.specialLinearNatural 3
          (linearThreeActor d.model k) (e u).toAdd := by
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,e,he⟩ := hm
  let := hn
  exact ⟨QuotientGroup.quotientBot.symm.trans e,he⟩

private theorem action_mem_sectionKernel_iff (d : MSData c n)
    (A : invariantCoreLifts c) (k : K c) :
    invariantLiftAction A k ∈ sectionKernel ((U c).subgroupOf A.val) ↔
      linearThreeActor d.model k = 1 := by
  obtain ⟨e,he⟩ := center_coordinates d
  obtain ⟨p,hp,hpker,heP⟩ := d.invariantCoreLifts_coordinates A
  constructor
  · intro hk
    apply Representation.specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    let u := e.symm (Multiplicative.ofAdd v)
    let a : A.val := ⟨u,A.property.1.le u.property⟩
    have ha := congrArg Subtype.val (hk.2 a u.property)
    have hh := he k u u ha.symm
    simpa [u] using hh.symm
  · intro hk
    constructor
    · intro a
      let b := invariantLiftAction A k a
      have hh := heP k a b rfl
      rw [hk,map_one] at hh
      have heq : p b = p a := Multiplicative.toAdd.injective (by simpa using hh)
      have hd : b * a⁻¹ ∈ p.ker := by
        change p (b*a⁻¹) = 1
        rw [map_mul,map_inv,heq,mul_inv_cancel]
      rwa [hpker] at hd
    · intro a ha
      let u : U c := ⟨a,ha⟩
      let v : U c := ⟨(k : G)*a*(k : G)⁻¹,
        (mem_normalizer_iff.mp (d.natural.2.1 k.property) a).mp ha⟩
      have hh := he k u v rfl
      rw [hk] at hh
      have huv : v = u := e.injective (Multiplicative.toAdd.injective (by simpa using hh))
      exact Subtype.ext (congrArg (fun z : U c => (z : G)) huv)

/-- The action on the lower natural section recovers exactly the original
SL₃ quotient, even though the action on the full elementary lift has kernel. -/
theorem MSData.invariantLift_quotient_actor (d : MSData c n)
    (A : invariantCoreLifts c) :
    ∃ f : (invariantLiftAction A).range →*
        Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier,
      Function.Surjective f ∧
      (∀ k : K c, f ((invariantLiftAction A).rangeRestrict k) = linearThreeActor d.model k) ∧
      f.ker = (sectionKernel ((U c).subgroupOf A.val)).subgroupOf
        (invariantLiftAction A).range := by
  let j := invariantLiftAction A
  let g := linearThreeActor d.model
  have hk : j.rangeRestrict.ker ≤ g.ker := by
    intro k hk
    apply (action_mem_sectionKernel_iff d A k).mp
    have hh : j k = 1 := congrArg Subtype.val hk
    rw [show invariantLiftAction A k = 1 from hh]
    exact one_mem _
  let f := j.rangeRestrict.liftOfSurjective j.rangeRestrict_surjective ⟨g,hk⟩
  have hf (k : K c) : f (j.rangeRestrict k) = g k :=
    j.rangeRestrict.liftOfRightInverse_comp_apply _
      (Function.rightInverse_surjInv j.rangeRestrict_surjective) ⟨g,hk⟩ k
  refine ⟨f,?_,hf,?_⟩
  · intro b
    obtain ⟨k,hk⟩ := d.model.surjective.comp (QuotientGroup.mk'_surjective _) b
    exact ⟨j.rangeRestrict k,(hf k).trans hk⟩
  · ext a
    obtain ⟨k,rfl⟩ := j.rangeRestrict_surjective a
    change f (j.rangeRestrict k) = 1 ↔ _
    rw [hf]
    exact (action_mem_sectionKernel_iff d A k).symm

private theorem core_le_original (c : SourceConfiguration T L) : Q c ≤ K c :=
  (Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 _) le_rfl)

/-- Q acts on the original invariant lift through the same ambient conjugation. -/
def invariantLiftCoreAction (A : invariantCoreLifts c) : Q c →* MulAut A.val :=
  (invariantLiftAction A).comp (inclusion
    ((Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 _) le_rfl)))

private theorem core_action_kernel [Finite G] (d : MSData c n)
    (A : invariantCoreLifts c) :
    (invariantLiftCoreAction A).ker = A.val.subgroupOf (Q c) := by
  ext q
  constructor
  · intro hq
    have he : invariantLiftCoreAction A q = 1 := hq
    have hc : (q : G) ∈ Subgroup.centralizer (A.val : Set G) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      have hh := congrArg (fun f : MulAut A.val => (f ⟨a,ha⟩ : G)) he
      change (q : G)*a*(q : G)⁻¹ = a at hh
      have hh' := congrArg (fun x : G => x*(q : G)) hh
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh'.symm
    exact (d.invariantCoreLifts_selfCentralizing A).le ⟨q.property,hc⟩
  · intro hq
    let := (d.invariantCoreLifts_elementary A).1
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change (q : G)*(a : G)*(q : G)⁻¹ = a
    have hh := congrArg Subtype.val (mul_comm (⟨q,hq⟩ : A.val) a)
    change (q : G)*(a : G) = (a : G)*(q : G) at hh
    rw [hh,mul_inv_cancel_right]

/-- The action image of Q is the original dual quotient Q/A. -/
theorem MSData.invariantLift_coreImage_coordinates [Finite G] (d : MSData c n)
    (A : invariantCoreLifts c) :
    ∃ e : (invariantLiftCoreAction A).range ≃*
        Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
      ∀ (k : K c) (a b : (invariantLiftCoreAction A).range),
        (b : MulAut A.val) = invariantLiftAction A k * a * (invariantLiftAction A k)⁻¹ →
        (e b).toAdd = (Representation.specialLinearNatural 3).dual
          (linearThreeActor d.model k) (e a).toAdd := by
  obtain ⟨p,hp,hk,he⟩ := d.invariantCoreLifts_complement_coordinates A
  let r := invariantLiftCoreAction A
  let e := (QuotientGroup.quotientKerEquivRange r).symm.trans
    (QuotientGroup.liftEquiv r.ker hp ((core_action_kernel d A).trans hk.symm))
  have heq (q : Q c) : e (r.rangeRestrict q) = p q := by
    change QuotientGroup.liftEquiv r.ker hp ((core_action_kernel d A).trans hk.symm)
      ((QuotientGroup.quotientKerEquivRange r).symm (r.rangeRestrict q)) = p q
    rw [show (QuotientGroup.quotientKerEquivRange r).symm (r.rangeRestrict q) =
        QuotientGroup.mk' r.ker q from
      (QuotientGroup.quotientKerEquivRange r).symm_apply_apply (QuotientGroup.mk' r.ker q)]
    rfl
  refine ⟨e,?_⟩
  intro k a b hab
  obtain ⟨q,rfl⟩ := r.rangeRestrict_surjective a
  let q' : Q c := ⟨(k : G)*q*(k : G)⁻¹,
    (mem_normalizer_iff.mp (d.doubleDual.2.1 k.property) q).mp q.property⟩
  have hb : b = r.rangeRestrict q' := by
    apply Subtype.ext
    rw [hab]
    change invariantLiftAction A k * invariantLiftAction A (inclusion (core_le_original c) q) *
      (invariantLiftAction A k)⁻¹ = invariantLiftAction A (inclusion (core_le_original c) q')
    rw [←map_inv,←map_mul,←map_mul]
    congr 1
  rw [hb,heq,heq]
  exact he k q q' rfl


private theorem core_le_original_core (c : SourceConfiguration T L) :
    Q c ≤ (K c).pCoreIn 2 :=
  le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))

private theorem actor_eq_one_iff (d : MSData c n) (k : K c) :
    linearThreeActor d.model k = 1 ↔ k ∈ pCore 2 (K c) := by
  change d.model (QuotientGroup.mk' (pCore 2 (K c)) k) = 1 ↔ _
  rw [d.model.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff k

private theorem coreAction_conjugate (_d : MSData c n) (A : invariantCoreLifts c)
    (k : K c) (q q' : Q c) (he : (q' : G) = k*q*(k : G)⁻¹) :
    invariantLiftCoreAction A q' =
      invariantLiftAction A k * invariantLiftCoreAction A q * (invariantLiftAction A k)⁻¹ := by
  change invariantLiftAction A (inclusion (core_le_original c) q') =
    invariantLiftAction A k * invariantLiftAction A (inclusion (core_le_original c) q) *
      (invariantLiftAction A k)⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  exact congrArg (invariantLiftAction A) (Subtype.ext he)

/-- C.1.35's action-normalizer identity on each actual invariant elementary
lift: every automorphism fixing U and A/U and normalizing the K-action is
already induced by Q. No larger-core identity is assumed. -/
theorem MSData.invariantLift_sectionKernel_normalizer [Finite G]
    (d : MSData c n) (hn : 1 < n) (A : invariantCoreLifts c) :
    sectionKernel ((U c).subgroupOf A.val) ⊓
      normalizer ((invariantLiftAction A).range : Set (MulAut A.val)) =
        (invariantLiftCoreAction A).range := by
  let j := invariantLiftAction A
  let r := invariantLiftCoreAction A
  let R := sectionKernel ((U c).subgroupOf A.val)
  let H := j.range
  let D := r.range
  let := d.invariantLift_sectionKernel_commutative A
  have hF : 2 < Nat.card d.field.Carrier := by
    rw [d.field.card_eq,d.degree_eq]
    exact (show (2 : ℕ)^1 < 2^n from pow_lt_pow_right₀ (by decide) hn)
  let := Representation.OneCohomology.SLHigherNatural.H1_subsingleton_sl3_dual_large_field hF
  obtain ⟨f,hf,hfj,hfk⟩ := d.invariantLift_quotient_actor A
  obtain ⟨e,he⟩ := d.invariantLift_coreImage_coordinates A
  have hHR : H ≤ normalizer (R : Set (MulAut A.val)) := by
    rintro _ ⟨k,rfl⟩
    apply mem_normalizer_sectionKernel
    intro a
    exact mem_normalizer_iff.mp (d.natural.2.1 k.property) (a : G)
  have hDH : D ≤ H := by
    rintro _ ⟨q,rfl⟩
    exact ⟨inclusion (core_le_original c) q,rfl⟩
  have hDR : D ≤ R := by
    rintro _ ⟨q,rfl⟩
    apply (action_mem_sectionKernel_iff d A (inclusion (core_le_original c) q)).mpr
    apply (actor_eq_one_iff d _).mpr
    have hq := core_le_original_core c q.property
    obtain ⟨q₀,hq₀,heq⟩ := hq
    exact (show inclusion (core_le_original c) q = q₀ from Subtype.ext heq.symm) ▸ hq₀
  apply Representation.OneCohomology.inf_normalizer_eq_of_H1_section H R D
    hHR f hf hfk hDH hDR e (Representation.specialLinearNatural 3).dual
  · intro a v
    obtain ⟨k,rfl⟩ := j.rangeRestrict_surjective a
    rw [hfj]
    let a₀ := e.symm (Multiplicative.ofAdd v)
    obtain ⟨q,hq⟩ := r.rangeRestrict_surjective a₀
    let q' : Q c := ⟨(k : G)*q*(k : G)⁻¹,
      (mem_normalizer_iff.mp (d.doubleDual.2.1 k.property) q).mp q.property⟩
    have hb := coreAction_conjugate d A k q q' rfl
    have hh := he k (r.rangeRestrict q) (r.rangeRestrict q') hb
    rw [hq] at hh
    have hh' : e (r.rangeRestrict q') = Multiplicative.ofAdd
        ((Representation.specialLinearNatural 3).dual (linearThreeActor d.model k) v) :=
      Multiplicative.toAdd.injective (by simpa [a₀] using hh)
    rw [←hh',e.symm_apply_apply]
    change r q' = j k * (a₀ : MulAut A.val) * (j k)⁻¹
    rw [←hq]
    exact hb
  · intro a u
    obtain ⟨k,rfl⟩ := j.rangeRestrict_surjective a
    obtain ⟨l,hl⟩ := j.rangeRestrict_surjective ⟨u,u.property.2⟩
    have hlv : j l = (u : MulAut A.val) := congrArg Subtype.val hl
    have hlR : j l ∈ R := hlv.symm ▸ u.property.1
    have hlK := (actor_eq_one_iff d l).mp ((action_mem_sectionKernel_iff d A l).mp hlR)
    have hq : (k : G)*(l : G)*(k : G)⁻¹*(l : G)⁻¹ ∈ Q c := by
      change ⁅(k : G),(l : G)⁆ ∈ ⁅(K c).pCoreIn 2,K c⁆
      rw [commutator_comm]
      exact commutator_mem_commutator k.property (mem_map_of_mem _ hlK)
    change j k * (u : MulAut A.val) * (j k)⁻¹ * (u : MulAut A.val)⁻¹ ∈ D
    rw [←hlv]
    refine ⟨⟨_,hq⟩,?_⟩
    change j (inclusion (core_le_original c) ⟨_,hq⟩) = j k*j l*(j k)⁻¹*(j l)⁻¹
    rw [←map_inv,←map_inv,←map_mul,←map_mul,←map_mul]
    rfl
  · exact d.invariantLift_sectionKernel_centralizer A


/-- In particular the entire original O₂(K) has exactly Q's image on A.
This is the action-image equality used in the larger-core argument. -/
theorem MSData.invariantLift_originalCore_image [Finite G]
    (d : MSData c n) (hn : 1 < n) (A : invariantCoreLifts c) :
    (pCore 2 (K c)).map (invariantLiftAction A) = (invariantLiftCoreAction A).range := by
  apply le_antisymm
  · rintro _ ⟨k,hk,rfl⟩
    apply (d.invariantLift_sectionKernel_normalizer hn A).le
    exact ⟨(action_mem_sectionKernel_iff d A k).mpr ((actor_eq_one_iff d k).mpr hk),
      (invariantLiftAction A).range.le_normalizer ⟨k,rfl⟩⟩
  · rintro _ ⟨q,rfl⟩
    have hq := core_le_original_core c q.property
    obtain ⟨q₀,hq₀,heq⟩ := hq
    refine ⟨q₀,hq₀,?_⟩
    apply congrArg (invariantLiftAction A)
    exact Subtype.ext heq

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
