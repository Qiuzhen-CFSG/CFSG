module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSPairedFixed
public import Theory.GroupTheory.HomSupExtension

/-!
# The complementary dual quotient and exact MS core deficit

For a KS-invariant elementary lift A, put P=O₂(KS) and C=C_P(A).
The factorization P=QC extends the original dual coordinates Q/A to P/C.
Conjugation retains the same full SL₃ marking and field, so the paired
natural/dual fixed-space bound applies simultaneously to U and P/C.

For a maximum elementary subgroup E of S outside P, this excludes
A∩E≤U. The complementary dual image of the centralizer of a noncentral
w∈A lies on the line through w's dual coordinate: it is a proper additive
subgroup invariant under the actual vector stabilizer. Thus the core
deficit |P∩E:C∩E| is at most 2^n. The previous lower bound makes it exactly
2^n, giving |E|=|C| and C=A(C∩E), without an additional equality premise.

The subsequent centralizer argument C=A, the original MSData construction,
secondary geometry, A₅ application and terminal exclusions remain with
qt-d-1222-rankone-uniqueness-nonblock. No equality P=Q is assumed here.
Source: Aschbacher–Smith C.1.35, printed p.139, the argument after (**)
and exclusion (!)–(!!); applied in original 4.3.11, printed p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

omit [Finite G] in
/-- The original KS normalizes its embedded two-core. -/
theorem join_normalizes_joinCore :
    K c ⊔ S c ≤ normalizer ((K c ⊔ S c).pCoreIn 2 : Set G) :=
  (K c ⊔ S c).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K c ⊔ S c)
      (pCore 2 (K c ⊔ S c : Subgroup G)))

private theorem core_le_joinCore : Q c ≤ (K c ⊔ S c).pCoreIn 2 := by
  rw [←sylow_join_commutator_eq c]
  exact le_normalizer_iff_commutator_le_left.mp
    ((le_sup_left : K c ≤ K c ⊔ S c).trans join_normalizes_joinCore)

omit [Finite G] in
private theorem join_normalizes_liftCentralizer
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G)) :
    K c ⊔ S c ≤ normalizer
      ((K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G) : Set G) :=
  (le_inf join_normalizes_joinCore
    (hA.trans (normalizer_le_normalizer_centralizer A.val))).trans
      inf_normalizer_le_normalizer_inf

/-- The larger core modulo the lift centralizer is the original complementary dual. -/
theorem MSData.exists_joinCore_dual_coordinates (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G)) :
    ∃ p : (K c ⊔ S c).pCoreIn 2 →*
        Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
      Function.Surjective p ∧
      p.ker = (Subgroup.centralizer (A.val : Set G)).subgroupOf ((K c ⊔ S c).pCoreIn 2) ∧
      ∀ (k : K c) (q r : (K c ⊔ S c).pCoreIn 2), (r : G) = k*q*(k : G)⁻¹ →
        (p r).toAdd = (Representation.specialLinearNatural 3).dual
          (linearThreeActor d.model k) (p q).toAdd := by
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  have hQ : Q c ≤ P := core_le_joinCore
  have hC : K c ⊔ S c ≤ normalizer (C : Set G) := join_normalizes_liftCentralizer A hA
  obtain ⟨p,hp,hk,he⟩ := d.invariantCoreLifts_complement_coordinates A
  have hker : p.ker = C.subgroupOf (Q c) := by
    rw [hk]
    ext q
    exact ⟨fun ha => (d.joinCore_eq_core_sup_liftCentralizer hn A hA).2.ge ha |>.2,
      fun hc => (d.joinCore_eq_core_sup_liftCentralizer hn A hA).2.le ⟨q.property,hc⟩⟩
  obtain ⟨f,hf,hfk,hfQ⟩ := MonoidHom.exists_sup_extension
    (hQ.trans ((pCoreIn_le 2 _).trans hC)) p hp hker
  have hP : P = Q c ⊔ C := (d.joinCore_eq_core_sup_liftCentralizer hn A hA).1
  let q := f.comp (inclusion hP.le)
  have hqQ (x : Q c) : q (inclusion hQ x) = p x := hfQ x
  have hqk : q.ker = C.subgroupOf P := by
    ext x
    change f (inclusion hP.le x) = 1 ↔ (x : G) ∈ C
    exact show inclusion hP.le x ∈ f.ker ↔ _ from hfk ▸ Iff.rfl
  have hqs : Function.Surjective q := by
    intro v
    obtain ⟨x,rfl⟩ := hp v
    exact ⟨inclusion hQ x,hqQ x⟩
  have hkill (x : P) (hx : (x : G) ∈ C) : q x = 1 := by
    exact show x ∈ q.ker from hqk.symm ▸ hx
  refine ⟨q,hqs,?_,?_⟩
  · rw [hqk]
    ext x
    exact ⟨And.right,fun hx => ⟨x.property,hx⟩⟩
  intro k x y hxy
  have hx : (x : G) ∈ (Q c : Set G) * (C : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right (Q c) C
      (hQ.trans ((pCoreIn_le 2 _).trans hC)),←hP]
    exact x.property
  obtain ⟨a,ha,b,hb,hab⟩ := hx
  let a' : Q c := ⟨(k:G)*a*(k:G)⁻¹,
    (mem_normalizer_iff.mp (d.doubleDual.2.1 k.property) a).mp ha⟩
  let b' : P := ⟨(k:G)*b*(k:G)⁻¹,
    (mem_normalizer_iff.mp (join_normalizes_joinCore (mem_sup_left k.property)) b).mp hb.1⟩
  have hb' : (b' : G) ∈ C :=
    (mem_normalizer_iff.mp (hC (mem_sup_left k.property)) b).mp hb
  have hx' : x = inclusion hQ ⟨a,ha⟩ * (⟨b,hb.1⟩ : P) := Subtype.ext hab.symm
  have hy' : y = inclusion hQ a' * b' := by
    apply Subtype.ext
    change (y:G) = ((k:G)*a*(k:G)⁻¹)*((k:G)*b*(k:G)⁻¹)
    rw [hxy,←hab]
    group
  rw [hy',hx',map_mul q,map_mul q,hkill b' hb',hkill ⟨b,hb.1⟩ hb,mul_one,mul_one,hqQ,hqQ]
  exact he k ⟨a,ha⟩ a' rfl

/-- Conjugation on the literal larger-core quotient has the same full SL₃ marking. -/
theorem MSData.exists_joinCore_dual_action (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G)) :
    ∃ p : (K c ⊔ S c).pCoreIn 2 →*
        Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
    ∃ δ : (K c ⊔ S c : Subgroup G) →*
        MulAut (Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier))),
      Function.Surjective p ∧
      p.ker = (Subgroup.centralizer (A.val : Set G)).subgroupOf ((K c ⊔ S c).pCoreIn 2) ∧
      (∀ x a, δ x (p a) = p (((K c ⊔ S c).pCoreIn 2).normalizerMonoidHom
        (inclusion join_normalizes_joinCore x) a)) ∧
      ∀ x g φ, (δ x (Multiplicative.ofAdd
        ((Representation.specialLinearNatural 3).dual g φ))).toAdd =
          (Representation.specialLinearNatural 3).dual (joinLinearThreeAction d x g)
            (δ x (Multiplicative.ofAdd φ)).toAdd := by
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  obtain ⟨p,hp,hk,he⟩ := d.exists_joinCore_dual_coordinates hn A hA
  have hkC : p.ker = C.subgroupOf P := by
    rw [hk]
    ext x
    exact ⟨fun hx => ⟨x.property,hx⟩,And.right⟩
  let hN : (C.subgroupOf P).Normal := hkC ▸ p.normal_ker
  let := hN
  let u := QuotientGroup.liftEquiv _ hp hkC.symm
  obtain ⟨δ₀,hδ₀⟩ := exists_quotient_conjugation_action (K c ⊔ S c) P C
    join_normalizes_joinCore (join_normalizes_liftCentralizer A hA) hN
  let δ := (MulAut.congr u).toMonoidHom.comp δ₀
  have hδ (x : (K c ⊔ S c : Subgroup G)) (a : P) :
      δ x (p a) = p (P.normalizerMonoidHom (inclusion join_normalizes_joinCore x) a) := by
    change u (δ₀ x (u.symm (u (QuotientGroup.mk' _ a)))) = _
    rw [u.symm_apply_apply,hδ₀]
    rfl
  have hnat (k : K c) (φ : Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)) :
      (δ (inclusion le_sup_left k) (Multiplicative.ofAdd φ)).toAdd =
        (Representation.specialLinearNatural 3).dual (linearThreeActor d.model k) φ := by
    obtain ⟨a,ha⟩ := hp (Multiplicative.ofAdd φ)
    rw [←ha,hδ]
    have hh := he k a (P.normalizerMonoidHom
      (inclusion join_normalizes_joinCore (inclusion le_sup_left k)) a) rfl
    rw [ha] at hh
    exact hh
  refine ⟨p,δ,hp,hk,hδ,?_⟩
  intro x g φ
  obtain ⟨k,rfl⟩ := d.model.surjective.comp (QuotientGroup.mk'_surjective _) g
  have hSK : S c ≤ normalizer (K c : Set G) := inf_le_right.trans c.normalizer_component.le
  let k' : K c := (K c).normalizerMonoidHom
    (inclusion (sup_le (K c).le_normalizer hSK) x) k
  have hα : joinLinearThreeAction d x (linearThreeActor d.model k) =
      linearThreeActor d.model k' := by
    change d.model (pCoreJoinAction 2 hSK x
      (d.model.symm (d.model (QuotientGroup.mk' _ k)))) = _
    rw [d.model.symm_apply_apply,pCoreJoinAction_mk]
    rfl
  have hinc : inclusion le_sup_left k' = x * inclusion le_sup_left k * x⁻¹ := Subtype.ext rfl
  have hcomm : δ (inclusion le_sup_left k') (δ x (Multiplicative.ofAdd φ)) =
      δ x (δ (inclusion le_sup_left k) (Multiplicative.ofAdd φ)) := by
    rw [hinc,map_mul,map_mul,map_inv]
    exact congrArg (δ x) (congrArg (δ (inclusion le_sup_left k))
      ((δ x).symm_apply_apply _))
  change (δ x (Multiplicative.ofAdd ((Representation.specialLinearNatural 3).dual
    (linearThreeActor d.model k) φ))).toAdd = _
  rw [←hnat k φ]
  change (δ x (δ (inclusion le_sup_left k) (Multiplicative.ofAdd φ))).toAdd = _
  rw [←hcomm]
  change (δ (inclusion le_sup_left k') (δ x (Multiplicative.ofAdd φ))).toAdd =
    (Representation.specialLinearNatural 3).dual
      (joinLinearThreeAction d x (linearThreeActor d.model k))
      (δ x (Multiplicative.ofAdd φ)).toAdd
  rw [hα]
  exact hnat k' (δ x (Multiplicative.ofAdd φ)).toAdd

/-- The actual inside-core image is proper in the complementary dual; for a
large outside image it satisfies the paired natural/dual fixed-space bound. -/
theorem MSData.elementary_core_image_bounds (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : E ≤ K c ⊔ S c)
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    let P := (K c ⊔ S c).pCoreIn 2
    let C := P ⊓ Subgroup.centralizer (A.val : Set G)
    C.relIndex (P ⊓ E) < 2^(3*n) ∧
      (2^n < P.relIndex E →
        Nat.card (U c ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
          C.relIndex (P ⊓ E) ≤ 2^(3*n)) := by
  dsimp only
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  let B := P ⊓ E
  obtain ⟨p,δ,hp,hk,hδ,hdual⟩ := d.exists_joinCore_dual_action hn A hA
  let r := p.comp (inclusion (show B ≤ P from inf_le_left))
  have hrker : r.ker = C.subgroupOf B := by
    ext b
    change p (inclusion (show B ≤ P from inf_le_left) b) = 1 ↔ (b:G) ∈ C
    change inclusion (show B ≤ P from inf_le_left) b ∈ p.ker ↔ _
    rw [hk]
    exact ⟨fun hb => ⟨b.property.1,hb⟩,And.right⟩
  have hN : C.relIndex B = Nat.card r.range := by
    rw [←index_ker,hrker]
    rfl
  let γ := δ.comp (inclusion hE)
  have hfix (v : r.range) (x : E) : γ x v.val = v.val := by
    obtain ⟨b,hb⟩ := v.property
    rw [←hb]
    change δ (inclusion hE x) (p (inclusion inf_le_left b)) = _
    rw [hδ]
    have he : P.normalizerMonoidHom
        (inclusion join_normalizes_joinCore (inclusion hE x)) (inclusion inf_le_left b) =
        inclusion inf_le_left b := by
      apply Subtype.ext
      change (x:G)*(b:G)*(x:G)⁻¹ = b
      have hc := congrArg Subtype.val (mul_comm x (⟨b,b.property.2⟩ : E))
      change (x:G)*(b:G) = (b:G)*(x:G) at hc
      rw [hc,mul_inv_cancel_right]
    rw [he]
    rfl
  let F := d.field.Carrier
  let : Finite (Module.Dual F (Fin 3 → F)) :=
    Finite.of_equiv (Fin 3 → F)
      (Representation.SL3ParabolicNatural.dualVectorCoordinates (F := F)).symm.toEquiv
  have hdim : Nat.card (Multiplicative (Module.Dual F (Fin 3 → F))) = 2^(3*n) := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Module.Dual F (Fin 3 → F)) ≃
      Module.Dual F (Fin 3 → F))]
    rw [Nat.card_congr (Representation.SL3ParabolicNatural.dualVectorCoordinates
      (F := F)).toEquiv,Nat.card_fun,Nat.card_fin]
    change Nat.card d.field.Carrier ^ 3 = _
    rw [d.field.card_eq,d.degree_eq,←pow_mul,Nat.mul_comm n 3]
  constructor
  · rw [hN,←hdim]
    apply lt_of_le_of_ne (Nat.card_le_card_of_injective (fun v : r.range => v.val) Subtype.val_injective)
    intro heq
    have htop : r.range = ⊤ := (eq_top_of_card_eq r.range heq)
    apply hout
    intro x hx
    let xE : E := ⟨x,hx⟩
    have hδx : δ (inclusion hE xE) = 1 := by
      apply MulEquiv.ext
      intro v
      exact hfix ⟨v,htop.ge (mem_top v)⟩ xE
    have hαx : joinLinearThreeAction d (inclusion hE xE) = 1 := by
      apply MulEquiv.ext
      intro g
      apply inv_injective
      apply Matrix.SpecialLinearGroup.toLin'_injective
      apply LinearEquiv.ext
      intro v
      funext i
      have hh := hdual (inclusion hE xE) g (LinearMap.proj i)
      rw [hδx] at hh
      exact (congrArg (fun φ : Module.Dual F (Fin 3 → F) => φ v) hh).symm
    have hxk : xE ∈ ((joinLinearThreeAction d).comp (inclusion hE)).ker := hαx
    rw [d.elementary_joinLinearThreeAction_ker E hE] at hxk
    exact hxk
  · intro hlarge
    obtain ⟨u,hker,hi⟩ := d.exists_join_center_coordinates
    let β := ((MulAut.congr u).toMonoidHom.comp (joinCenterAction c)).comp (inclusion hE)
    have hβker : β.ker = P.subgroupOf E := by
      rw [←MonoidHom.comap_ker,hker]
      ext x
      change inclusion hE x ∈ pCore 2 (K c ⊔ S c : Subgroup G) ↔
        (x:G) ∈ (pCore 2 (K c ⊔ S c : Subgroup G)).map (K c ⊔ S c : Subgroup G).subtype
      constructor
      · exact fun hx => mem_map_of_mem _ hx
      · rintro ⟨y,hy,hxy⟩
        have he : y = inclusion hE x := Subtype.ext hxy
        exact he ▸ hy
    have hβlarge : Nat.card F < Nat.card β.range := by
      change Nat.card d.field.Carrier < _
      rw [d.field.card_eq,d.degree_eq,←index_ker,hβker]
      exact hlarge
    have hb := Representation.SL3NaturalFixed.paired_fixed_card_le β γ
      ((joinLinearThreeAction d).comp (inclusion hE))
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E))
      (fun x g v => hi (inclusion hE x) g v)
      (fun x g φ => hdual (inclusion hE x) g φ) hβlarge
    let X := {v : Fin 3 → F // ∀ x : E, (β x (Multiplicative.ofAdd v)).toAdd = v}
    let Y := {φ : Module.Dual F (Fin 3 → F) // ∀ x : E,
      (γ x (Multiplicative.ofAdd φ)).toAdd = φ}
    have hY : Nat.card r.range ≤ Nat.card Y := by
      let j : r.range → Y := fun v => ⟨v.val.toAdd,fun x => congrArg Multiplicative.toAdd (hfix v x)⟩
      exact Nat.card_le_card_of_injective j
        (fun a b h => Subtype.ext (Multiplicative.toAdd.injective (congrArg (fun z : Y => z.val) h)))
    have hX : Nat.card (U c ⊓ Subgroup.centralizer (E:Set G) : Subgroup G) ≤ Nat.card X := by
      let j : (U c ⊓ Subgroup.centralizer (E:Set G) : Subgroup G) → X := fun a =>
        ⟨(u ⟨a,a.property.1⟩).toAdd,by
          intro x
          change (u (joinCenterAction c (inclusion hE x)
            (u.symm (u ⟨a,a.property.1⟩)))).toAdd = _
          rw [u.symm_apply_apply]
          have he : joinCenterAction c (inclusion hE x) ⟨a,a.property.1⟩ =
              ⟨a,a.property.1⟩ := by
            apply Subtype.ext
            change (x:G)*(a:G)*(x:G)⁻¹ = a
            rw [mem_centralizer_iff.mp a.property.2 x x.property,mul_inv_cancel_right]
          rw [he]⟩
      apply Nat.card_le_card_of_injective j
      intro a b hab
      have he := u.injective (Multiplicative.toAdd.injective (congrArg Subtype.val hab))
      exact Subtype.ext (congrArg (fun x : U c => (x:G)) he)
    rw [hN]
    have hh := (Nat.mul_le_mul hX hY).trans hb
    change _ ≤ Nat.card d.field.Carrier ^ 3 at hh
    rw [d.field.card_eq,d.degree_eq,←pow_mul,Nat.mul_comm n 3] at hh
    exact hh

/-- A maximum elementary subgroup outside the core meets the invariant lift
nontrivially modulo U. This excludes the central-intersection branch of C.1.35. -/
theorem MSData.maxElementary_not_centerIntersection (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (S c))
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    ¬ A.val ⊓ E ≤ U c := by
  intro hcentral
  let := hE.2.1
  let := (d.invariantCoreLifts_elementary A).1
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  have hb := d.elementary_core_image_bounds hn A hA E (hE.1.trans le_sup_right) hout
  change C.relIndex (P ⊓ E) < 2^(3*n) ∧ _ at hb
  have hAC : A.val ≤ C := le_inf (A.property.2.1.le.trans core_le_joinCore) (le_centralizer A.val)
  have hi := (d.maxElementary_joinCore_deficit A E hE).2
  have hindex : E.relIndex A.val ≤ C.relIndex (P ⊓ E) * P.relIndex E :=
    (relIndex_le_of_le_right hAC index_ne_zero_of_finite).trans hi
  by_cases hsmall : P.relIndex E ≤ 2^n
  · have hlo := (d.maxElementary_centerIntersection_deficit A E hE hout hcentral).1
    have hh := hlo.trans hindex
    have hu : C.relIndex (P ⊓ E) * P.relIndex E < 2^(4*n) := calc
      _ ≤ C.relIndex (P ⊓ E) * 2^n := Nat.mul_le_mul_left _ hsmall
      _ < 2^(3*n) * 2^n := Nat.mul_lt_mul_of_pos_right hb.1 (by positivity)
      _ = 2^(4*n) := by rw [←pow_add]; congr 1; omega
    exact (not_lt_of_ge hh) hu
  · have hfixed := hb.2 (lt_of_not_ge hsmall)
    have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) (E ⊓ A.val) A.val bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,
      (d.invariantCoreLifts_elementary A).2,inf_comm E A.val] at hcard
    have hsub : A.val ⊓ E ≤ U c ⊓ Subgroup.centralizer (E:Set G) :=
      le_inf hcentral (inf_le_right.trans (le_centralizer E))
    have hbound : 2^(6*n) ≤ 2^(5*n) := calc
      2^(6*n) = Nat.card (A.val ⊓ E : Subgroup G) * E.relIndex A.val := hcard.symm
      _ ≤ Nat.card (U c ⊓ Subgroup.centralizer (E:Set G) : Subgroup G) *
          (C.relIndex (P ⊓ E) * P.relIndex E) := Nat.mul_le_mul (card_le_of_le hsub) hindex
      _ = (Nat.card (U c ⊓ Subgroup.centralizer (E:Set G) : Subgroup G) *
          C.relIndex (P ⊓ E)) * P.relIndex E := (Nat.mul_assoc _ _ _).symm
      _ ≤ 2^(3*n) * 2^(2*n) := Nat.mul_le_mul hfixed
        (d.elementary_joinCore_index_le E (hE.1.trans le_sup_right))
      _ = 2^(5*n) := by rw [←pow_add]; congr 1; omega
    have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound
    omega

/-- A noncentral element of any invariant lift has a centralizer image of
order at most 2^n in the larger core modulo the lift centralizer. -/
theorem MSData.invariantLift_element_core_index_le (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (w : G) (hw : w ∈ A.val) (hwu : w ∉ U c) :
    let P := (K c ⊔ S c).pCoreIn 2
    let C := P ⊓ Subgroup.centralizer (A.val : Set G)
    C.relIndex (P ⊓ Subgroup.centralizer ({w}:Set G)) ≤ 2^n := by
  dsimp only
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  let Z := P ⊓ Subgroup.centralizer ({w}:Set G)
  obtain ⟨p,hp,hk,he⟩ := d.exists_joinCore_dual_coordinates hn A hA
  obtain ⟨f,hf,hfk,hfe⟩ := d.invariantCoreLifts_coordinates A
  let F := d.field.Carrier
  let wA : A.val := ⟨w,hw⟩
  have hwf : (f wA).toAdd ≠ 0 := by
    intro hh
    have hk' : wA ∈ f.ker := Multiplicative.toAdd.injective hh
    rw [hfk] at hk'
    exact hwu hk'
  let W : AddSubgroup (Module.Dual F (Fin 3 → F)) := {
    carrier := {v | ∃ q : P, (p q).toAdd = v ∧ Commute w (q:G)}
    zero_mem' := ⟨1,by rw [map_one]; rfl,Commute.one_right _⟩
    add_mem' := by
      rintro v z ⟨a,ha,hac⟩ ⟨b,hb,hbc⟩
      refine ⟨a*b,?_,hac.mul_right hbc⟩
      rw [map_mul p]
      change (p a).toAdd + (p b).toAdd = _
      rw [ha,hb]
    neg_mem' := by
      rintro v ⟨a,ha,hac⟩
      refine ⟨a⁻¹,?_,hac.inv_right⟩
      rw [map_inv p]
      change -(p a).toAdd = _
      rw [ha] }
  have hproper : W ≠ ⊤ := by
    intro htop
    apply hwu
    refine ⟨⟨w,A.property.2.1.le hw⟩,mem_center_iff.mpr ?_,rfl⟩
    intro q
    let qP : P := inclusion core_le_joinCore q
    obtain ⟨b,hb,hwb⟩ := show (p qP).toAdd ∈ W from htop ▸ AddSubgroup.mem_top _
    have hker : qP/b ∈ p.ker := p.div_mem_ker_iff.mpr (Multiplicative.toAdd.injective hb.symm)
    rw [hk] at hker
    have hc : Commute w ((qP/b:G)) := mem_centralizer_iff.mp hker w hw
    have hh := hc.mul_right hwb
    apply Subtype.ext
    simpa only [coe_div,coe_mul,div_mul_cancel,qP,coe_inclusion] using hh.symm.eq
  have hstable : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
      (Representation.specialLinearNatural 3).dual g (f wA).toAdd = (f wA).toAdd →
      ∀ v ∈ W, (Representation.specialLinearNatural 3).dual g v ∈ W := by
    intro g hg v hv
    obtain ⟨q,hq,hwq⟩ := hv
    obtain ⟨k,rfl⟩ := d.model.surjective.comp (QuotientGroup.mk'_surjective _) g
    let q' : P := ⟨(k:G)*q*(k:G)⁻¹,
      (mem_normalizer_iff.mp (join_normalizes_joinCore (mem_sup_left k.property)) q).mp q.property⟩
    let w' : A.val := ⟨(k:G)*w*(k:G)⁻¹,
      (mem_normalizer_iff.mp (A.property.2.2 k.property) w).mp hw⟩
    refine ⟨q',?_,?_⟩
    · rw [he k q q' rfl,hq]
      rfl
    have hfw : f w' = f wA := Multiplicative.toAdd.injective ((hfe k wA w' rfl).trans hg)
    have hwu' : (w' : G)/w ∈ U c := by
      have hh : w'/wA ∈ f.ker := f.div_mem_ker_iff.mpr hfw
      rw [hfk] at hh
      exact hh
    have hcomm : Commute (q':G) (w':G) := by
      change ((k:G)*(q:G)*(k:G)⁻¹)*((k:G)*w*(k:G)⁻¹) =
        ((k:G)*w*(k:G)⁻¹)*((k:G)*(q:G)*(k:G)⁻¹)
      calc
        _ = (k:G)*((q:G)*w)*(k:G)⁻¹ := by group
        _ = (k:G)*(w*(q:G))*(k:G)⁻¹ := by rw [hwq.eq]
        _ = _ := by group
    have hcU : Commute (q':G) ((w':G)/w) :=
      (mem_centralizer_iff.mp (d.joinCore_centralizes_center q'.property) _ hwu').symm
    have hh := hcU.inv_right.mul_right hcomm
    have hid : ((w':G)/w)⁻¹*(w':G) = w := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one]
    rw [hid] at hh
    exact hh.symm
  have hline : ∀ v ∈ W, ∃ a : F, v = a • (f wA).toAdd :=
    Representation.SL3ParabolicNatural.dual_stabilizer_invariant_le_line
      (f wA).toAdd hwf W hproper hstable
  let B := (Z.subgroupOf P).map p
  have hB : ∀ v : B, ∃ a : F, v.val.toAdd = a • (f wA).toAdd := by
    intro v
    obtain ⟨q,hq,hqv⟩ := v.property
    apply hline
    refine ⟨q,congrArg Multiplicative.toAdd hqv,?_⟩
    exact mem_centralizer_iff.mp hq.2 w (Set.mem_singleton w)
  choose a ha using hB
  have hcard : Nat.card B ≤ Nat.card F := by
    apply Nat.card_le_card_of_injective a
    intro v z hvz
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    rw [ha v,ha z,hvz]
  have hind : C.relIndex Z = Nat.card B := by
    have hh := C.relIndex_comap P.subtype (Z.subgroupOf P)
    rw [map_subgroupOf_eq_of_le (show Z ≤ P from inf_le_left)] at hh
    rw [←hh]
    have hkC : p.ker = C.subgroupOf P := by
      rw [hk]
      ext x
      exact ⟨fun hx => ⟨x.property,hx⟩,And.right⟩
    change (C.subgroupOf P).relIndex (Z.subgroupOf P) = _
    rw [←hkC,relIndex_ker]
  rw [hind]
  exact hcard.trans_eq (d.field.card_eq.trans (congrArg (2^·) d.degree_eq))

/-- The original outside maximum elementary subgroup always attains the
minimal deficit. Hence the cardinality and generation equalities hold
without an extra equality-case assumption. -/
theorem MSData.maxElementary_core_equality (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (S c))
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    let P := (K c ⊔ S c).pCoreIn 2
    let C := P ⊓ Subgroup.centralizer (A.val : Set G)
    C.relIndex (P ⊓ E) = 2^n ∧ Nat.card E = Nat.card C ∧ C = A.val ⊔ (C ⊓ E) := by
  dsimp only
  let := hE.2.1
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  obtain ⟨w,hw,hwu⟩ := SetLike.not_le_iff_exists.mp
    (d.maxElementary_not_centerIntersection hn A hA E hE hout)
  have hle : P ⊓ E ≤ P ⊓ Subgroup.centralizer ({w}:Set G) := by
    intro z hz
    refine ⟨hz.1,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (mem_centralizer_iff.mp (le_centralizer E hz.2) w hw.2).symm
  have hb : C.relIndex (P ⊓ E) ≤ 2^n :=
    (relIndex_le_of_le_right hle index_ne_zero_of_finite).trans
      (d.invariantLift_element_core_index_le hn A hA w hw.1 hwu)
  exact ⟨le_antisymm hb (d.maxElementary_core_deficit A hA E hE hout),
    d.maxElementary_minimal_deficit_equality A hA E hE hout hb⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
