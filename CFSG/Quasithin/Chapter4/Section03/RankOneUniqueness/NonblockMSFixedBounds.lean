module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSThompson
public import Theory.Representation.SL3.NaturalNormalizerFixed
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Fixed-space deficits for the original nonbinary MS lift

The action of KS on its natural center U has kernel O₂(KS). The same
holds on the dual quotient A/U of a KS-invariant elementary lift A.
Both kernel identities follow from the faithful full SL₃ restriction and
the two-group supplement; neither assumes the desired equality O₂(KS)=Q.

Conjugation preserves the marked natural action. Its scalar commutant
therefore makes every actor semilinear over the original field. Each
nonidentity actor fixes at most 2^(2n) vectors. Applied on U and A/U,
this bounds C_A(E) by 2^(4n) for every E outside O₂(KS), including actors
with a field twist. The literal quotient map has kernel U throughout.

The final theorem applies the bound to the maximum elementary subgroup
from MS3 and the original centralizer factor C, proving the first 2n
fixed-codimension estimate in C.1.35. The sharper 3n estimate for a larger
outside image and the equality argument forcing C=A remain necessary.
Actual MSData, secondary data, the original A₅ application and terminal
exclusions remain with qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher–Smith C.1.35, printed pp.138–139, used in 4.3.11, p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

omit [Finite G] in
/-- The original KS normalizes the center of the intrinsic commutator core. -/
theorem join_normalizes_coreCenter :
    K c ⊔ S c ≤ normalizer (U c : Set G) :=
  ((sup_le (map_subtype_le _) inf_le_right).trans (core_normalized c)).trans
    (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c)))

/-- Conjugation by the original KS on the original natural center. -/
def joinCenterAction (c : SourceConfiguration T L) :
    (K c ⊔ S c : Subgroup G) →* MulAut (U c) :=
  (U c).normalizerMonoidHom.comp (inclusion join_normalizes_coreCenter)

omit [Finite G] in
private theorem center_coordinates (d : MSData c n) :
    ∃ u : U c ≃* Multiplicative (Fin 3 → d.field.Carrier),
      ∀ (k : K c) (a : U c),
        (u (joinCenterAction c (inclusion le_sup_left k) a)).toAdd =
          Representation.specialLinearNatural 3 (linearThreeActor d.model k) (u a).toAdd := by
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hbot,e,he⟩ := hm
  let := hbot
  exact ⟨QuotientGroup.quotientBot.symm.trans e,fun k a => he k a _ rfl⟩

omit [Finite G] in
/-- The center action on K retains the full SL₃ quotient, including its scalar center. -/
theorem MSData.joinCenterAction_restrict_ker (d : MSData c n) :
    ((joinCenterAction c).comp (inclusion le_sup_left : K c →* (K c ⊔ S c : Subgroup G))).ker =
      pCore 2 (K c) := by
  obtain ⟨u,hu⟩ := center_coordinates d
  ext k
  change joinCenterAction c (inclusion le_sup_left k) = 1 ↔ k ∈ pCore 2 (K c)
  have hquot : linearThreeActor d.model k = 1 ↔ k ∈ pCore 2 (K c) := by
    rw [show linearThreeActor d.model k = d.model (QuotientGroup.mk' _ k) from rfl,
      d.model.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff k
  rw [←hquot]
  constructor
  · intro hk
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    have hh := hu k (u.symm (Multiplicative.ofAdd v))
    rw [hk] at hh
    rw [map_one]
    change Representation.specialLinearNatural 3 (linearThreeActor d.model k) v = v
    simpa using hh.symm
  · intro hk
    apply MulEquiv.ext
    intro a
    apply u.injective
    apply Multiplicative.toAdd.injective
    change (u (joinCenterAction c (inclusion le_sup_left k) a)).toAdd = (u a).toAdd
    simpa only [hk,map_one,Module.End.one_apply] using hu k a

/-- The actual KS-action kernel on U is precisely its two-core. -/
theorem MSData.joinCenterAction_ker (d : MSData c n) :
    (joinCenterAction c).ker = pCore 2 (K c ⊔ S c : Subgroup G) := by
  let J := K c ⊔ S c
  let N := (K c).subgroupOf J
  have hn : J ≤ normalizer (K c : Set G) :=
    sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hgen : N ⊔ (S c).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,
      ←MonoidHom.range_eq_map,range_subtype]
  have hquot : IsPGroup 2 (J ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    ((S c).subgroupOf J) (T.isPGroup'.to_le inf_le_left).comap_subtype hgen
  let f := joinCenterAction c
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* K c :=
      (J.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict (K c) (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 (K c) := by
      intro x
      exact d.joinCenterAction_restrict_ker.le x.val.property
    let r' := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 (K c) => (x.val : G)) hab
  have hp : IsPGroup 2 f.ker := by
    have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
    rw [comap_top] at hh
    exact hh.of_equiv topEquiv
  refine le_antisymm ?_ ?_
  · exact le_sSup ⟨inferInstance,hp⟩
  intro x hx
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  have hc := d.joinCore_centralizes_center (mem_map_of_mem J.subtype hx)
  change (x : G) ∈ Subgroup.centralizer (U c : Set G) at hc
  change (x : G)*(a : G)*(x : G)⁻¹ = a
  rw [←mem_centralizer_iff.mp hc a a.property,mul_inv_cancel_right]

/-- The larger core is detected by centralizing the literal original U. -/
theorem MSData.joinCore_eq_centerCentralizer (d : MSData c n) :
    (K c ⊔ S c).pCoreIn 2 = (K c ⊔ S c) ⊓ Subgroup.centralizer (U c : Set G) := by
  rw [pCoreIn,←d.joinCenterAction_ker]
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,mem_centralizer_iff.mpr ?_⟩
    intro a ha
    have hh := congrArg (fun f : MulAut (U c) => ((f ⟨a,ha⟩ : U c) : G)) hx
    change (x : G)*a*(x : G)⁻¹ = a at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · rintro ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change x*(a : G)*x⁻¹ = a
    rw [←mem_centralizer_iff.mp hc a a.property,mul_inv_cancel_right]

/-- Every subgroup of KS outside its two-core fixes at most 2^(2n)
elements of the original natural center. No inner-action assumption is used. -/
theorem MSData.center_fixed_card_le (d : MSData c n) (E : Subgroup G)
    (hE : E ≤ K c ⊔ S c) (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    Nat.card (U c ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) ≤ 2^(2*n) := by
  obtain ⟨x,hx,hxp⟩ : ∃ x ∈ E, x ∉ (K c ⊔ S c).pCoreIn 2 := by
    by_contra! hh
    exact hout hh
  let xJ : (K c ⊔ S c : Subgroup G) := ⟨x,hE hx⟩
  obtain ⟨u,hu⟩ := center_coordinates d
  let β := joinCenterAction c
  let f : (Fin 3 → d.field.Carrier) ≃+ (Fin 3 → d.field.Carrier) :=
    (u.symm.trans ((β xJ).trans u)).toAdditive
  have hfne : f ≠ AddEquiv.refl _ := by
    intro he
    apply hxp
    have hker : xJ ∈ (joinCenterAction c).ker := by
      apply MulEquiv.ext
      intro a
      apply u.injective
      apply Multiplicative.toAdd.injective
      have hh := congrArg (fun e : (Fin 3 → d.field.Carrier) ≃+
        (Fin 3 → d.field.Carrier) => e (u a).toAdd) he
      change (u (β xJ (u.symm (u a)))).toAdd = (u a).toAdd at hh
      change (u (β xJ a)).toAdd = (u a).toAdd
      simpa only [u.symm_apply_apply] using hh
    rw [d.joinCenterAction_ker] at hker
    exact mem_map_of_mem (K c ⊔ S c : Subgroup G).subtype hker
  have hSK : S c ≤ normalizer (K c : Set G) :=
    inf_le_right.trans c.normalizer_component.le
  let α := MulAut.congr d.model (pCoreJoinAction 2 hSK xJ)
  have hi : ∀ g v, f (Representation.specialLinearNatural 3 g v) =
      Representation.specialLinearNatural 3 (α g) (f v) := by
    intro g v
    obtain ⟨k,rfl⟩ := d.model.surjective.comp (QuotientGroup.mk'_surjective _) g
    let k' : K c := (K c).normalizerMonoidHom
      (inclusion (sup_le (K c).le_normalizer hSK) xJ) k
    let a := u.symm (Multiplicative.ofAdd v)
    have hα : α (linearThreeActor d.model k) = linearThreeActor d.model k' := by
      change d.model (pCoreJoinAction 2 hSK xJ
        (d.model.symm (d.model (QuotientGroup.mk' _ k)))) = _
      rw [d.model.symm_apply_apply,pCoreJoinAction_mk]
      rfl
    have hinc : inclusion le_sup_left k' = xJ * inclusion le_sup_left k * xJ⁻¹ :=
      Subtype.ext rfl
    have hβ : β (inclusion le_sup_left k') (β xJ a) =
        β xJ (β (inclusion le_sup_left k) a) := by
      rw [hinc,map_mul,map_mul,map_inv]
      exact congrArg (β xJ) (congrArg (β (inclusion le_sup_left k))
        ((β xJ).symm_apply_apply a))
    have hv : (u a).toAdd = v := congrArg Multiplicative.toAdd (u.apply_symm_apply _)
    change f (Representation.specialLinearNatural 3 (linearThreeActor d.model k) v) = _
    calc
      f (Representation.specialLinearNatural 3 (linearThreeActor d.model k) v) =
          (u (β xJ (β (inclusion le_sup_left k) a))).toAdd := by
        rw [←hv,←hu k a]
        change (u (β xJ (u.symm (u (β (inclusion le_sup_left k) a))))).toAdd = _
        rw [u.symm_apply_apply]
      _ = (u (β (inclusion le_sup_left k') (β xJ a))).toAdd := by rw [hβ]
      _ = Representation.specialLinearNatural 3 (α (linearThreeActor d.model k)) (f v) := by
        rw [hu,hα]
        rfl
  have hb := Representation.SL3NaturalFixed.fixed_card_le_of_intertwines f hfne α hi
  let C := U c ⊓ Subgroup.centralizer (E : Set G)
  let j : C → {v : Fin 3 → d.field.Carrier // f v = v} := fun a =>
    ⟨(u ⟨a,a.property.1⟩).toAdd,by
      change (u (β xJ (u.symm (u ⟨a,a.property.1⟩)))).toAdd = _
      rw [u.symm_apply_apply]
      have hc : β xJ ⟨a,a.property.1⟩ = ⟨a,a.property.1⟩ := by
        apply Subtype.ext
        change x*(a : G)*x⁻¹ = a
        rw [mem_centralizer_iff.mp a.property.2 x hx,mul_inv_cancel_right]
      rw [hc]⟩
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    have hh := u.injective (Multiplicative.toAdd.injective (congrArg Subtype.val hab))
    exact congrArg (fun y : U c => (y : G)) hh
  have hcard := (Nat.card_le_card_of_injective j hj).trans hb
  rw [d.field.card_eq,d.degree_eq,←pow_mul] at hcard
  simpa only [Nat.mul_comm n 2] using hcard

/-- The source natural factor contributes at least n binary dimensions
to the deficit of every subgroup outside the larger two-core. -/
theorem MSData.center_fixed_index_ge (d : MSData c n) (E : Subgroup G)
    (hE : E ≤ K c ⊔ S c) (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    2^n ≤ (Subgroup.centralizer (E : Set G)).relIndex (U c) := by
  have hb := d.center_fixed_card_le E hE hout
  have hu : Nat.card (U c) = 2^(3*n) := by
    rw [card_map_of_injective (Q c).subtype_injective,d.center_card]
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G)
    (Subgroup.centralizer (E : Set G) ⊓ U c) (U c) bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,hu,inf_comm] at hi
  apply Nat.le_of_mul_le_mul_left (c := 2^(2*n)) _ (by positivity)
  calc
    2^(2*n)*2^n = 2^(3*n) := by rw [←pow_add]; congr 1; omega
    _ = Nat.card (U c ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
        (Subgroup.centralizer (E : Set G)).relIndex (U c) := hi.symm
    _ ≤ _ := Nat.mul_le_mul_right _ hb

omit [Finite G] in
private theorem joinAction_kernel_eq {H : Type*} [Group H]
    (f : (K c ⊔ S c : Subgroup G) →* H)
    (hf : (f.comp (inclusion le_sup_left : K c →* (K c ⊔ S c : Subgroup G))).ker = pCore 2 (K c))
    (hP : pCore 2 (K c ⊔ S c : Subgroup G) ≤ f.ker) :
    f.ker = pCore 2 (K c ⊔ S c : Subgroup G) := by
  let J := K c ⊔ S c
  let N := (K c).subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le))
  have hgen : N ⊔ (S c).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,
      ←MonoidHom.range_eq_map,range_subtype]
  have hquot : IsPGroup 2 (J ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    ((S c).subgroupOf J) (T.isPGroup'.to_le inf_le_left).comap_subtype hgen
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* K c :=
      (J.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict (K c) (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 (K c) := fun x => hf.le x.val.property
    let r' := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 (K c) => (x.val : G)) hab
  have hp : IsPGroup 2 f.ker := by
    have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
    rw [comap_top] at hh
    exact hh.of_equiv topEquiv
  exact le_antisymm (le_sSup ⟨inferInstance,hp⟩) hP

/-- The original invariant dual lift has a quotient action of the full KS,
with kernel exactly O₂(KS). Inverse transpose changes only the coordinates
of the same dual action; the quotient map still has kernel U. -/
theorem MSData.exists_join_lift_quotient_action (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G)) :
    ∃ (e : (K c ⧸ pCore 2 (K c)) ≃* Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier)
      (p : A.val →* Multiplicative (Fin 3 → d.field.Carrier))
      (β : (K c ⊔ S c : Subgroup G) →* MulAut (Multiplicative (Fin 3 → d.field.Carrier))),
      (∀ q, e q = Matrix.SpecialLinearGroup.inverseTranspose (d.model q)) ∧
      Function.Surjective p ∧ p.ker = (U c).subgroupOf A.val ∧
      β.ker = pCore 2 (K c ⊔ S c : Subgroup G) ∧
      (∀ (x : (K c ⊔ S c : Subgroup G)) (a : A.val),
        β x (p a) = p (A.val.normalizerMonoidHom (inclusion hA x) a)) ∧
      (∀ (k : K c) (v : Fin 3 → d.field.Carrier),
        (β (inclusion le_sup_left k) (Multiplicative.ofAdd v)).toAdd =
          Representation.specialLinearNatural 3 (linearThreeActor e k) v) := by
  obtain ⟨p,hp,hk,he⟩ := d.invariantCoreLifts_coordinates A
  let F := d.field.Carrier
  let γ : Matrix.SpecialLinearGroup (Fin 3) F →* Matrix.SpecialLinearGroup (Fin 3) F :=
    Matrix.SpecialLinearGroup.inverseTranspose
  have hγ (g : Matrix.SpecialLinearGroup (Fin 3) F) : γ (γ g) = g := by
    change ((γ g)⁻¹).transpose = g
    rw [←map_inv]
    change ((g⁻¹)⁻¹).transpose.transpose = g
    rw [inv_inv]
    apply Subtype.ext
    rfl
  let τ : MulAut (Matrix.SpecialLinearGroup (Fin 3) F) :=
    { γ with
      invFun := γ
      left_inv := hγ
      right_inv := hγ }
  let e := d.model.trans τ
  let v := Representation.SL3ParabolicNatural.dualVectorCoordinates (F := F)
  let v' := v.toAddEquiv.toMultiplicative
  let p' := v'.toMonoidHom.comp p
  have hp' : Function.Surjective p' := v'.surjective.comp hp
  have hk' : p'.ker = (U c).subgroupOf A.val := by
    ext a
    change v' (p a) = 1 ↔ _
    rw [v'.map_eq_one_iff]
    exact SetLike.ext_iff.mp hk a
  let hn : ((U c).subgroupOf A.val).Normal := hk' ▸ p'.normal_ker
  let := hn
  let q := QuotientGroup.mk' ((U c).subgroupOf A.val)
  let u := QuotientGroup.liftEquiv _ hp' hk'.symm
  obtain ⟨β₀,hβ₀⟩ := exists_quotient_conjugation_action
    (K c ⊔ S c) A.val (U c) hA join_normalizes_coreCenter hn
  let β := (MulAut.congr u).toMonoidHom.comp β₀
  have hu (a : A.val) : u (q a) = p' a := rfl
  have hβ (x : (K c ⊔ S c : Subgroup G)) (a : A.val) :
      β x (p' a) = p' (A.val.normalizerMonoidHom (inclusion hA x) a) := by
    rw [←hu]
    change u (β₀ x (u.symm (u (q a)))) = _
    rw [u.symm_apply_apply,hβ₀]
    rfl
  have he' (k : K c) (a : A.val) :
      (p' (A.val.normalizerMonoidHom (inclusion hA (inclusion le_sup_left k)) a)).toAdd =
        Representation.specialLinearNatural 3 (linearThreeActor e k) (p' a).toAdd := by
    have hh := he k a (A.val.normalizerMonoidHom
      (inclusion hA (inclusion le_sup_left k)) a) rfl
    change v (p (A.val.normalizerMonoidHom (inclusion hA (inclusion le_sup_left k)) a)).toAdd = _
    rw [hh,Representation.SL3ParabolicNatural.dualVectorCoordinates_action]
    rfl
  have hnat (k : K c) (w : Fin 3 → F) :
      (β (inclusion le_sup_left k) (Multiplicative.ofAdd w)).toAdd =
        Representation.specialLinearNatural 3 (linearThreeActor e k) w := by
    obtain ⟨a,ha⟩ := hp' (Multiplicative.ofAdd w)
    rw [←ha,hβ]
    have hh := he' k a
    rw [ha] at hh
    exact hh
  have hrestrict : (β.comp (inclusion le_sup_left : K c →* (K c ⊔ S c : Subgroup G))).ker =
      pCore 2 (K c) := by
    ext k
    change β (inclusion le_sup_left k) = 1 ↔ _
    have hquot : linearThreeActor e k = 1 ↔ k ∈ pCore 2 (K c) := by
      rw [show linearThreeActor e k = e (QuotientGroup.mk' _ k) from rfl,e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff k
    rw [←hquot]
    constructor
    · intro h
      apply Matrix.SpecialLinearGroup.toLin'_injective
      apply LinearEquiv.ext
      intro w
      rw [map_one]
      change Representation.specialLinearNatural 3 (linearThreeActor e k) w = w
      have hh := hnat k w
      rw [h] at hh
      exact hh.symm
    · intro h
      apply MulEquiv.ext
      intro w
      apply Multiplicative.toAdd.injective
      change (β (inclusion le_sup_left k) w).toAdd = w.toAdd
      have hh := hnat k w.toAdd
      rw [h,map_one] at hh
      exact hh
  have hcore : pCore 2 (K c ⊔ S c : Subgroup G) ≤ β.ker := by
    intro x hx
    apply MulEquiv.ext
    intro w
    obtain ⟨a,rfl⟩ := hp' w
    rw [hβ]
    change p' (A.val.normalizerMonoidHom (inclusion hA x) a) = p' a
    apply mul_inv_eq_one.mp
    rw [←map_inv,←map_mul]
    apply hk'.ge
    have hs := d.joinCore_liftAction_mem_sectionKernel A hA x
      (mem_map_of_mem (K c ⊔ S c : Subgroup G).subtype hx)
    exact hs.1 a
  exact ⟨e,p',β,fun _ => rfl,hp',hk',joinAction_kernel_eq β hrestrict hcore,hβ,hnat⟩

omit [Finite G] in
private theorem quotient_actor_fixed_bound (d : MSData c n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier)
    (β : (K c ⊔ S c : Subgroup G) →* MulAut (Multiplicative (Fin 3 → d.field.Carrier)))
    (hnat : ∀ (k : K c) (v : Fin 3 → d.field.Carrier),
      (β (inclusion le_sup_left k) (Multiplicative.ofAdd v)).toAdd =
        Representation.specialLinearNatural 3 (linearThreeActor e k) v)
    (x : (K c ⊔ S c : Subgroup G)) (hne : β x ≠ 1) :
    Nat.card {v : Fin 3 → d.field.Carrier // (β x (Multiplicative.ofAdd v)).toAdd = v} ≤ 2^(2*n) := by
  let f : (Fin 3 → d.field.Carrier) ≃+ (Fin 3 → d.field.Carrier) := (β x).toAdditive
  have hfne : f ≠ AddEquiv.refl _ := by
    intro hf
    apply hne
    apply MulEquiv.ext
    intro v
    exact congrArg (fun a : (Fin 3 → d.field.Carrier) ≃+ (Fin 3 → d.field.Carrier) => a v.toAdd) hf
  have hSK : S c ≤ normalizer (K c : Set G) := inf_le_right.trans c.normalizer_component.le
  let α := MulAut.congr e (pCoreJoinAction 2 hSK x)
  have hi : ∀ g v, f (Representation.specialLinearNatural 3 g v) =
      Representation.specialLinearNatural 3 (α g) (f v) := by
    intro g v
    obtain ⟨k,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
    let k' : K c := (K c).normalizerMonoidHom
      (inclusion (sup_le (K c).le_normalizer hSK) x) k
    have hα : α (linearThreeActor e k) = linearThreeActor e k' := by
      change e (pCoreJoinAction 2 hSK x (e.symm (e (QuotientGroup.mk' _ k)))) = _
      rw [e.symm_apply_apply,pCoreJoinAction_mk]
      rfl
    have hinc : inclusion le_sup_left k' = x * inclusion le_sup_left k * x⁻¹ := Subtype.ext rfl
    have hβ : β (inclusion le_sup_left k') (β x (Multiplicative.ofAdd v)) =
        β x (β (inclusion le_sup_left k) (Multiplicative.ofAdd v)) := by
      rw [hinc,map_mul,map_mul,map_inv]
      exact congrArg (β x) (congrArg (β (inclusion le_sup_left k))
        ((β x).symm_apply_apply _))
    change f (Representation.specialLinearNatural 3 (linearThreeActor e k) v) = _
    rw [←hnat k v]
    change (β x (β (inclusion le_sup_left k) (Multiplicative.ofAdd v))).toAdd = _
    rw [←hβ]
    have hh := hnat k' (β x (Multiplicative.ofAdd v)).toAdd
    rw [←hα] at hh
    exact hh
  have hb := Representation.SL3NaturalFixed.fixed_card_le_of_intertwines f hfne α hi
  rw [d.field.card_eq,d.degree_eq,←pow_mul] at hb
  change Nat.card {v : Fin 3 → d.field.Carrier // f v = v} ≤ _
  simpa only [Nat.mul_comm n 2] using hb

/-- Every outside actor moves at least two field dimensions on the original
invariant elementary lift. Both natural and dual factors use their literal
KS-actions, so field twists are included. -/
theorem MSData.invariantLift_fixed_card_le (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ≤ K c ⊔ S c) (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    Nat.card (A.val ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) ≤ 2^(4*n) := by
  obtain ⟨e,p,β,_htwist,hp,hk,hker,hβ,hnat⟩ := d.exists_join_lift_quotient_action A hA
  obtain ⟨x,hx,hxp⟩ : ∃ x ∈ E, x ∉ (K c ⊔ S c).pCoreIn 2 := by
    by_contra! hh
    exact hout hh
  let xJ : (K c ⊔ S c : Subgroup G) := ⟨x,hE hx⟩
  have hne : β xJ ≠ 1 := by
    intro hh
    have hh' : xJ ∈ β.ker := hh
    rw [hker] at hh'
    exact hxp (mem_map_of_mem (K c ⊔ S c : Subgroup G).subtype hh')
  have hb := quotient_actor_fixed_bound d e β hnat xJ hne
  let C := A.val ⊓ Subgroup.centralizer (E : Set G)
  let r := p.comp (inclusion (show C ≤ A.val from inf_le_left))
  have hrange : Nat.card r.range ≤ 2^(2*n) := by
    let j : r.range → {v : Fin 3 → d.field.Carrier // (β xJ (Multiplicative.ofAdd v)).toAdd = v} :=
      fun v => ⟨v.val.toAdd,by
        obtain ⟨a,ha⟩ := v.property
        rw [←ha]
        change (β xJ (p (inclusion inf_le_left a))).toAdd = (p (inclusion inf_le_left a)).toAdd
        rw [hβ]
        have he : A.val.normalizerMonoidHom (inclusion hA xJ) (inclusion inf_le_left a) =
            inclusion inf_le_left a := by
          apply Subtype.ext
          change x*(a : G)*x⁻¹ = a
          rw [mem_centralizer_iff.mp a.property.2 x hx,mul_inv_cancel_right]
        rw [he]⟩
    exact (Nat.card_le_card_of_injective j (fun a b h =>
      Subtype.ext (Multiplicative.toAdd.injective
        (congrArg (fun z : {v : Fin 3 → d.field.Carrier //
          (β xJ (Multiplicative.ofAdd v)).toAdd = v} => z.val) h)))).trans hb
  have hkernel : Nat.card r.ker ≤ 2^(2*n) := by
    let j : r.ker → (U c ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) :=
      fun a => ⟨a.val.val,⟨hk.le a.property,a.val.property.2⟩⟩
    have hj : Function.Injective j := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg
        (fun z : (U c ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) => (z : G)) h))
    exact (Nat.card_le_card_of_injective j hj).trans (d.center_fixed_card_le E hE hout)
  have hc := r.ker.index_mul_card
  rw [index_ker] at hc
  calc
    Nat.card C = Nat.card r.range * Nat.card r.ker := hc.symm
    _ ≤ 2^(2*n)*2^(2*n) := Nat.mul_le_mul hrange hkernel
    _ = 2^(4*n) := by rw [←pow_add]; congr 1; omega

/-- The first combined fixed-codimension estimate (+) of C.1.35, on the
actual invariant lift and the original full Sylow overgroup. -/
theorem MSData.invariantLift_fixed_index_ge (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ≤ K c ⊔ S c) (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    2^(2*n) ≤ (Subgroup.centralizer (E : Set G)).relIndex A.val := by
  have hb := d.invariantLift_fixed_card_le A hA E hE hout
  have ha := (d.invariantCoreLifts_elementary A).2
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G)
    (Subgroup.centralizer (E : Set G) ⊓ A.val) A.val bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,ha,inf_comm] at hi
  apply Nat.le_of_mul_le_mul_left (c := 2^(4*n)) _ (by positivity)
  calc
    2^(4*n)*2^(2*n) = 2^(6*n) := by rw [←pow_add]; congr 1; omega
    _ = Nat.card (A.val ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
        (Subgroup.centralizer (E : Set G)).relIndex A.val := hi.symm
    _ ≤ _ := Nat.mul_le_mul_right _ hb

/-- The original maximum elementary witness satisfies the quantitative
C.1.35 deficit estimate with the proved natural-plus-dual lower bound. -/
theorem MSData.maxElementary_fixed_deficit (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (S c))
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    let P := (K c ⊔ S c).pCoreIn 2
    let C := P ⊓ Subgroup.centralizer (A.val : Set G)
    2^(2*n) ≤ E.relIndex C ∧
      E.relIndex C ≤ C.relIndex (P ⊓ E) * P.relIndex E := by
  dsimp only
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  have hAP : A.val ≤ P := by
    apply A.property.2.1.le.trans
    rw [←sylow_join_commutator_eq c]
    exact le_normalizer_iff_commutator_le_left.mp ((le_sup_left : K c ≤ K c ⊔ S c).trans
      ((K c ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c ⊔ S c)
          (pCore 2 (K c ⊔ S c : Subgroup G)))))
  let := (d.invariantCoreLifts_elementary A).1
  have hAC : A.val ≤ C := le_inf hAP (le_centralizer A.val)
  have he := d.maxElementary_joinCore_deficit A E hE
  refine ⟨?_,he.2⟩
  have hlower := d.invariantLift_fixed_index_ge A hA E (hE.1.trans le_sup_right) hout
  have hle := relIndex_le_of_le_right (H := Subgroup.centralizer (E : Set G))
    hAC ((Subgroup.centralizer (E : Set G)).subgroupOf C).index_ne_zero_of_finite
  have hc : (Subgroup.centralizer (E : Set G)).relIndex C = E.relIndex C := by
    rw [←inf_relIndex_right (Subgroup.centralizer (E : Set G)) C,
      inf_comm (Subgroup.centralizer (E : Set G)) C,he.1,inf_comm C E,inf_relIndex_right]
  exact hlower.trans (hle.trans_eq hc)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
