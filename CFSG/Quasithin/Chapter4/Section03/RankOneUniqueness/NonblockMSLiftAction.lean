module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSInvariantLift
public import Theory.Representation.SL3.NaturalDualAutomorphisms
public import Theory.GroupTheory.AutomorphismSectionKernel

/-!
# The dual quotient action on the original invariant elementary lift

Every K-invariant subgroup A properly between U=Z(Q) and Q corresponds to
an actual diagonal line in the doubled-dual quotient. Projection onto a
nonzero coordinate gives a surjection A → U* with kernel U and the literal
K-conjugation action. Thus the Sylow-invariant lift of C.1.35 carries the
same dual marking as the original MS configuration.

The covector-stabilizer calculation then proves that an automorphism of A
fixing U and A/U and commuting with K is trivial. This supplies the
trivial-centralizer step of C.1.35's action-normalizer argument. The larger
normalizer identity, Q=O₂(KS), MSData construction and final nonblock
contradiction remain with qt-d-1222-rankone-uniqueness-nonblock.

Source: Aschbacher–Smith C.1.35, printed p.138; original 4.3.10–11, p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open Representation.SL3ParabolicNatural
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private def dualProjection {F : Type*} [Field F] (b : Bool) :
    Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)) →*
      Multiplicative (Module.Dual F (Fin 3 → F)) where
  toFun v := Multiplicative.ofAdd (if b then v.toAdd.1 else v.toAdd.2)
  map_one' := by cases b <;> rfl
  map_mul' v w := by cases b <;> rfl

/-- Every intrinsic intermediate lift has the original dual quotient action. -/
theorem MSData.invariantCoreLifts_coordinates (d : MSData c n) (A : invariantCoreLifts c) :
    ∃ p : A.val →* Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
      Function.Surjective p ∧ p.ker = (U c).subgroupOf A.val ∧
      ∀ (k : K c) (a b : A.val), (b : G) = k*a*(k : G)⁻¹ →
        (p b).toAdd = (Representation.specialLinearNatural 3).dual
          (linearThreeActor d.model k) (p a).toAdd := by
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
  let inc : A.val →* Q c := inclusion A.property.2.1.le
  let f := p.comp inc
  have hr : f.range = B := by
    ext v
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨inc a,a.property,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨q,hq⟩,rfl⟩
  have hmodel (k : K c) (a b : A.val) (hh : (b : G) = k*a*(k : G)⁻¹) :=
    he k (inc a) (inc b) hh
  have hmem (a : A.val) : f a ∈ dualLine i := hi ▸ (hr ▸ (show f a ∈ f.range from ⟨a,rfl⟩))
  have hzero (a : A.val) : f a = 1 ↔ (a : G) ∈ U c := by
    change inc a ∈ p.ker ↔ _
    rw [hk]
    rfl
  cases i with
  | none =>
    let f' := (dualProjection false).comp f
    refine ⟨f',?_,?_,?_⟩
    · intro v
      have hm : Multiplicative.ofAdd (0,v.toAdd) ∈ f.range := by
        rw [hr,hi,mem_dualLine_none]
        rfl
      obtain ⟨a,ha⟩ := hm
      exact ⟨a,congrArg (dualProjection false) ha⟩
    · ext a
      change (f a).toAdd.2 = 0 ↔ (a : G) ∈ U c
      rw [←hzero]
      constructor
      · intro hh
        apply Multiplicative.toAdd.injective
        exact Prod.ext ((mem_dualLine_none _).mp (hmem a)) hh
      · intro hh
        exact congrArg (fun v => v.toAdd.2) hh
    · intro k a b hh
      exact congrArg Prod.snd (hmodel k a b hh)
  | some t =>
    let f' := (dualProjection true).comp f
    refine ⟨f',?_,?_,?_⟩
    · intro v
      have hm : Multiplicative.ofAdd (v.toAdd,t • v.toAdd) ∈ f.range := by
        rw [hr,hi,mem_dualLine_some]
        rfl
      obtain ⟨a,ha⟩ := hm
      exact ⟨a,congrArg (dualProjection true) ha⟩
    · ext a
      change (f a).toAdd.1 = 0 ↔ (a : G) ∈ U c
      rw [←hzero]
      constructor
      · intro hh
        apply Multiplicative.toAdd.injective
        apply Prod.ext hh
        rw [(mem_dualLine_some _ _).mp (hmem a),hh,smul_zero]
        rfl
      · intro hh
        exact congrArg (fun v => v.toAdd.1) hh
    · intro k a b hh
      exact congrArg Prod.fst (hmodel k a b hh)

/-- The quotient marking is on A/U, with the same SL₃ identification as Q/U. -/
theorem MSData.invariantCoreLifts_dual (d : MSData c n) (A : invariantCoreLifts c) :
    HasSectionModel (K c) A.val (U c) (linearThreeActor d.model)
      (Representation.specialLinearNatural 3).dual := by
  obtain ⟨p,hp,hk,he⟩ := d.invariantCoreLifts_coordinates A
  let hn : ((U c).subgroupOf A.val).Normal := hk ▸ p.normal_ker
  let := hn
  exact ⟨A.property.1.le,A.property.2.2,d.natural.2.1,hn,
    QuotientGroup.liftEquiv _ hp hk.symm,he⟩

/-- In the literal elementary lift, the centralizer of the K-action has no
nontrivial automorphism fixing U and inducing the identity on A/U. -/
theorem MSData.invariantCoreLifts_automorphism_eq_one
    (d : MSData c n) (A : invariantCoreLifts c)
    (τ : MulAut A.val)
    (hquot : ∀ a : A.val, ((τ a : A.val) : G) * (a : G)⁻¹ ∈ U c)
    (hfix : ∀ a : A.val, (a : G) ∈ U c → τ a = a)
    (hcomm : ∀ (k : K c) (a b : A.val), (b : G) = k*a*(k : G)⁻¹ →
      ((τ b : A.val) : G) = (k : G)*τ a*(k : G)⁻¹) : τ = 1 := by
  obtain ⟨p,hp,hk,he⟩ := d.invariantCoreLifts_coordinates A
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,e,heU⟩ := hm
  let := hn
  let u₀ : U c ≃* Multiplicative (Fin 3 → d.field.Carrier) :=
    QuotientGroup.quotientBot.symm.trans e
  let uk : p.ker ≃* U c :=
    (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe A.property.1.le)
  let u := uk.trans u₀
  let := conjMulDistribMulActionOfLeNormalizer (K c) A.val A.property.2.2
  apply natural_dual_automorphism_eq_one (linearThreeActor d.model)
    (d.model.surjective.comp (QuotientGroup.mk'_surjective _)) p u
    (fun k a => he k a (k • a) rfl) ?_ τ ?_ ?_ ?_
  · intro k x y hy
    exact heU k (uk x) (uk y) (congrArg Subtype.val hy)
  · intro a
    have hh : τ a * a⁻¹ ∈ p.ker := by rw [hk]; exact hquot a
    exact mul_inv_eq_one.mp (by simpa only [MonoidHom.mem_ker,map_mul,map_inv] using hh)
  · intro a ha
    apply hfix
    rwa [hk] at ha
  · intro k a
    apply Subtype.ext
    exact hcomm k a (k • a) rfl

/-- Choose the source W₁ with its full dual action marking, retaining the
same center, original quotient actor and Sylow normalization. -/
theorem MSData.exists_sylow_invariant_marked_lift [Finite G] (d : MSData c n) :
    ∃ A : Subgroup G, U c < A ∧ A < Q c ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 2^(6*n) ∧
      K c ⊔ S c ≤ normalizer (A : Set G) ∧
      Q c ⊓ Subgroup.centralizer (A : Set G) = A ∧
      HasSectionModel (K c) A (U c) (linearThreeActor d.model)
        (Representation.specialLinearNatural 3).dual := by
  obtain ⟨A,hUA,hAQ,hE,hcard,hn,hc,_⟩ := d.exists_sylow_invariant_elementary_lift
  exact ⟨A,hUA,hAQ,hE,hcard,hn,hc,
    d.invariantCoreLifts_dual ⟨A,hUA,hAQ,le_sup_left.trans hn⟩⟩

/-- The literal K-action on the invariant lift, through its ambient normalizer. -/
def invariantLiftAction (A : invariantCoreLifts c) : K c →* MulAut A.val :=
  A.val.normalizerMonoidHom.comp (inclusion A.property.2.2)

/-- The original two-section kernel is abelian, without choosing a complement. -/
theorem MSData.invariantLift_sectionKernel_commutative
    (d : MSData c n) (A : invariantCoreLifts c) :
    IsMulCommutative (sectionKernel ((U c).subgroupOf A.val)) := by
  let := (d.invariantCoreLifts_elementary A).1
  exact sectionKernel_commutative _

/-- The trivial centralizer in C.1.35, for the actual K-action and the
actual kernel fixing U and A/U. -/
theorem MSData.invariantLift_sectionKernel_centralizer
    (d : MSData c n) (A : invariantCoreLifts c) :
    sectionKernel ((U c).subgroupOf A.val) ⊓
      Subgroup.centralizer ((invariantLiftAction A).range : Set (MulAut A.val)) = ⊥ := by
  apply bot_unique
  rintro τ ⟨hτ,hc⟩
  apply mem_bot.mpr
  apply d.invariantCoreLifts_automorphism_eq_one A τ hτ.1 hτ.2
  intro k a b hab
  have hh := mem_centralizer_iff.mp hc (invariantLiftAction A k) ⟨k,rfl⟩
  have he := congrArg (fun f : MulAut A.val => f a) hh
  have hba : invariantLiftAction A k a = b := Subtype.ext hab.symm
  change invariantLiftAction A k (τ a) = τ (invariantLiftAction A k a) at he
  rw [hba] at he
  exact (congrArg Subtype.val he).symm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
