module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSOutsideRank
public import Theory.Representation.SL3.NaturalDualFixed
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The paired fixed-space estimate and equality case in the original MS core

Let A be a KS-invariant elementary lift, P=O₂(KS), and C=C_P(A).
The original action on U and the quotient action on A/U induce the same
automorphism of the original full SL₃. Transport through the literal
quotient map therefore applies the paired natural/dual estimate, including
field actors: if |E:E∩P|>2^n, then |C_A(E)|≤2^(3n).

For every maximum elementary subgroup E of S outside P, this sharper
estimate combines with the small-image bound to give |P∩E:C∩E|≥2^n.
In particular P∩E is not contained in C. If this index is at most 2^n,
all counting inequalities are equalities: |E|=|C| and C=A(C∩E).
These conclusions use the original relative indices and subgroups.

The central-intersection exclusion and the subsequent argument forcing
C=A, hence O₂(KS)=Q, remain necessary. MSData is an explicit input here;
its source construction and final nonblock assembly remain with the
original nonblock owner. Source: Aschbacher–Smith C.1.35, printed p.139,
estimates (+), (**) and their equality case; original 4.3.11, p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

omit [Finite G] in
/-- The literal KS-action on A/U retains the original dual SL₃ marking. -/
theorem MSData.exists_join_dual_coordinates (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G)) :
    ∃ p : A.val →* Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
    ∃ δ : (K c ⊔ S c : Subgroup G) →*
        MulAut (Multiplicative (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier))),
      Function.Surjective p ∧ p.ker = (U c).subgroupOf A.val ∧
      (∀ x a, δ x (p a) = p (A.val.normalizerMonoidHom (inclusion hA x) a)) ∧
      ∀ x g φ, (δ x (Multiplicative.ofAdd
        ((Representation.specialLinearNatural 3).dual g φ))).toAdd =
          (Representation.specialLinearNatural 3).dual (joinLinearThreeAction d x g)
            (δ x (Multiplicative.ofAdd φ)).toAdd := by
  obtain ⟨p,hp,hk,he⟩ := d.invariantCoreLifts_coordinates A
  let hn : ((U c).subgroupOf A.val).Normal := hk ▸ p.normal_ker
  let := hn
  let u := QuotientGroup.liftEquiv _ hp hk.symm
  obtain ⟨δ₀,hδ₀⟩ := exists_quotient_conjugation_action
    (K c ⊔ S c) A.val (U c) hA join_normalizes_coreCenter hn
  let δ := (MulAut.congr u).toMonoidHom.comp δ₀
  have hδ (x : (K c ⊔ S c : Subgroup G)) (a : A.val) :
      δ x (p a) = p (A.val.normalizerMonoidHom (inclusion hA x) a) := by
    change u (δ₀ x (u.symm (u (QuotientGroup.mk' _ a)))) = _
    rw [u.symm_apply_apply,hδ₀]
    rfl
  have hnat (k : K c) (φ : Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)) :
      (δ (inclusion le_sup_left k) (Multiplicative.ofAdd φ)).toAdd =
        (Representation.specialLinearNatural 3).dual (linearThreeActor d.model k) φ := by
    obtain ⟨a,ha⟩ := hp (Multiplicative.ofAdd φ)
    rw [←ha,hδ]
    have hh := he k a (A.val.normalizerMonoidHom
      (inclusion hA (inclusion le_sup_left k)) a) rfl
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

/-- A large outside image fixes at most 2^(3n) elements of the original lift. -/
theorem MSData.invariantLift_largeImage_fixed_card_le (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : E ≤ K c ⊔ S c)
    (hlarge : 2^n < ((K c ⊔ S c).pCoreIn 2).relIndex E) :
    Nat.card (A.val ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) ≤ 2^(3*n) := by
  obtain ⟨u,hker,hi⟩ := d.exists_join_center_coordinates
  obtain ⟨p,δ,hp,hk,hδ,hdual⟩ := d.exists_join_dual_coordinates A hA
  let β := ((MulAut.congr u).toMonoidHom.comp (joinCenterAction c)).comp (inclusion hE)
  let γ := δ.comp (inclusion hE)
  have hβker : β.ker = ((K c ⊔ S c).pCoreIn 2).subgroupOf E := by
    rw [←MonoidHom.comap_ker,hker]
    ext x
    change inclusion hE x ∈ pCore 2 (K c ⊔ S c : Subgroup G) ↔
      (x : G) ∈ (pCore 2 (K c ⊔ S c : Subgroup G)).map (K c ⊔ S c : Subgroup G).subtype
    constructor
    · exact fun hx => mem_map_of_mem _ hx
    · rintro ⟨y,hy,hxy⟩
      have he : y = inclusion hE x := Subtype.ext hxy
      exact he ▸ hy
  have hβlarge : Nat.card d.field.Carrier < Nat.card β.range := by
    rw [d.field.card_eq,d.degree_eq,←index_ker,hβker]
    exact hlarge
  have hb := Representation.SL3NaturalFixed.paired_fixed_card_le β γ
    ((joinLinearThreeAction d).comp (inclusion hE))
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E))
    (fun x g v => hi (inclusion hE x) g v)
    (fun x g φ => hdual (inclusion hE x) g φ) hβlarge
  let X := {v : Fin 3 → d.field.Carrier // ∀ x : E,
    (β x (Multiplicative.ofAdd v)).toAdd = v}
  let Y := {φ : Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) // ∀ x : E,
    (γ x (Multiplicative.ofAdd φ)).toAdd = φ}
  let : Finite (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)) :=
    Finite.of_equiv (Fin 3 → d.field.Carrier)
      (Representation.SL3ParabolicNatural.dualVectorCoordinates (F := d.field.Carrier)).symm.toEquiv
  let C := A.val ⊓ Subgroup.centralizer (E : Set G)
  let r := p.comp (inclusion (show C ≤ A.val from inf_le_left))
  have hrange : Nat.card r.range ≤ Nat.card Y := by
    let j : r.range → Y := fun v => ⟨v.val.toAdd,by
      intro x
      obtain ⟨a,ha⟩ := v.property
      rw [←ha]
      change (δ (inclusion hE x) (p (inclusion inf_le_left a))).toAdd = _
      rw [hδ]
      have he : A.val.normalizerMonoidHom (inclusion hA (inclusion hE x))
          (inclusion inf_le_left a) = inclusion inf_le_left a := by
        apply Subtype.ext
        change (x : G)*(a : G)*(x : G)⁻¹ = a
        rw [mem_centralizer_iff.mp a.property.2 x x.property,mul_inv_cancel_right]
      rw [he]
      rfl⟩
    exact Nat.card_le_card_of_injective j (fun a b h =>
      Subtype.ext (Multiplicative.toAdd.injective (congrArg (fun z : Y => z.val) h)))
  have hkernel : Nat.card r.ker ≤ Nat.card X := by
    let j : r.ker → X := fun a =>
      ⟨(u ⟨a.val.val,hk.le a.property⟩).toAdd,by
        intro x
        change (u (joinCenterAction c (inclusion hE x)
          (u.symm (u ⟨a.val.val,hk.le a.property⟩)))).toAdd = _
        rw [u.symm_apply_apply]
        have he : joinCenterAction c (inclusion hE x) ⟨a.val.val,hk.le a.property⟩ =
            ⟨a.val.val,hk.le a.property⟩ := by
          apply Subtype.ext
          change (x : G)*(a.val.val : G)*(x : G)⁻¹ = a.val.val
          rw [mem_centralizer_iff.mp a.val.property.2 x x.property,mul_inv_cancel_right]
        rw [he]⟩
    apply Nat.card_le_card_of_injective j
    intro a b h
    have hh := u.injective (Multiplicative.toAdd.injective (congrArg (fun z : X => z.val) h))
    exact Subtype.ext (Subtype.ext (congrArg (fun z : U c => (z : G)) hh))
  have hc := r.ker.card_mul_index
  rw [index_ker] at hc
  calc
    Nat.card C = Nat.card r.ker * Nat.card r.range := hc.symm
    _ ≤ Nat.card X * Nat.card Y := Nat.mul_le_mul hkernel hrange
    _ ≤ Nat.card d.field.Carrier ^ 3 := hb
    _ = 2^(3*n) := by rw [d.field.card_eq,d.degree_eq,←pow_mul,Nat.mul_comm n 3]

/-- The large-image part of source (+), on the original invariant lift. -/
theorem MSData.invariantLift_largeImage_fixed_index_ge (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : E ≤ K c ⊔ S c)
    (hlarge : 2^n < ((K c ⊔ S c).pCoreIn 2).relIndex E) :
    2^(3*n) ≤ (Subgroup.centralizer (E : Set G)).relIndex A.val := by
  have hb := d.invariantLift_largeImage_fixed_card_le A hA E hE hlarge
  have ha := (d.invariantCoreLifts_elementary A).2
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G)
    (Subgroup.centralizer (E : Set G) ⊓ A.val) A.val bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,ha,inf_comm] at hi
  apply Nat.le_of_mul_le_mul_left (c := 2^(3*n)) _ (by positivity)
  calc
    2^(3*n)*2^(3*n) = 2^(6*n) := by rw [←pow_add]; congr 1; omega
    _ = Nat.card (A.val ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
        (Subgroup.centralizer (E : Set G)).relIndex A.val := hi.symm
    _ ≤ _ := Nat.mul_le_mul_right _ hb

/-- The full source (**) deficit bound, for the original maximum elementary subgroup. -/
theorem MSData.maxElementary_core_deficit (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (S c))
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    let P := (K c ⊔ S c).pCoreIn 2
    let C := P ⊓ Subgroup.centralizer (A.val : Set G)
    2^n ≤ C.relIndex (P ⊓ E) := by
  dsimp only
  by_cases hsmall : ((K c ⊔ S c).pCoreIn 2).relIndex E ≤ 2^n
  · exact d.maxElementary_smallImage_core_deficit A hA E hE hout hsmall
  let := hE.2.1
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  have hlarge := d.invariantLift_largeImage_fixed_index_ge A hA E
    (hE.1.trans le_sup_right) (lt_of_not_ge hsmall)
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
  have hle := relIndex_le_of_le_right (H := Subgroup.centralizer (E : Set G))
    hAC ((Subgroup.centralizer (E : Set G)).subgroupOf C).index_ne_zero_of_finite
  have hc : (Subgroup.centralizer (E : Set G)).relIndex C = E.relIndex C := by
    rw [←inf_relIndex_right (Subgroup.centralizer (E : Set G)) C,
      inf_comm (Subgroup.centralizer (E : Set G)) C,he.1,inf_comm C E,inf_relIndex_right]
  have hbound : 2^(3*n) ≤ C.relIndex (P ⊓ E) * 2^(2*n) :=
    ((hlarge.trans (hle.trans_eq hc)).trans he.2).trans
      (Nat.mul_le_mul_left _ (d.elementary_joinCore_index_le E (hE.1.trans le_sup_right)))
  rw [show 3*n=n+2*n from by omega,pow_add] at hbound
  exact Nat.le_of_mul_le_mul_right hbound (by positivity)

/-- The original inside-core intersection contains an element outside the lift centralizer. -/
theorem MSData.maxElementary_not_le_liftCentralizer (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (S c))
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2) :
    ¬ (K c ⊔ S c).pCoreIn 2 ⊓ E ≤
      (K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G) := by
  intro hle
  have hb := d.maxElementary_core_deficit A hA E hE hout
  dsimp only at hb
  rw [relIndex_eq_one.mpr hle] at hb
  exact (not_le_of_gt (one_lt_pow₀ (by decide : 1 < (2:ℕ))
    (show n ≠ 0 from by have := d.pair.positive; omega))) hb


/-- At the minimal core deficit, all counting inequalities are equalities:
the original centralizer factor is generated by the lift and its fixed points. -/
theorem MSData.maxElementary_minimal_deficit_equality (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (S c))
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2)
    (hN : ((K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G)).relIndex
      ((K c ⊔ S c).pCoreIn 2 ⊓ E) ≤ 2^n) :
    let C := (K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G)
    Nat.card E = Nat.card C ∧ C = A.val ⊔ (C ⊓ E) := by
  dsimp only
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  let := hE.2.1
  let := (d.invariantCoreLifts_elementary A).1
  have hAP : A.val ≤ P := by
    apply A.property.2.1.le.trans
    rw [←sylow_join_commutator_eq c]
    exact le_normalizer_iff_commutator_le_left.mp ((le_sup_left : K c ≤ K c ⊔ S c).trans
      ((K c ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c ⊔ S c)
          (pCore 2 (K c ⊔ S c : Subgroup G)))))
  have hAC : A.val ≤ C := le_inf hAP (le_centralizer A.val)
  have he := d.maxElementary_joinCore_deficit A E hE
  have hfixed : (Subgroup.centralizer (E : Set G)).relIndex A.val = E.relIndex A.val := by
    have hi : A.val ⊓ Subgroup.centralizer (E : Set G) = A.val ⊓ E := by
      calc
        A.val ⊓ Subgroup.centralizer (E : Set G) =
            A.val ⊓ (C ⊓ Subgroup.centralizer (E : Set G)) := by
          rw [←inf_assoc,inf_eq_left.mpr hAC]
        _ = A.val ⊓ (C ⊓ E) := by rw [he.1]
        _ = A.val ⊓ E := by rw [←inf_assoc,inf_eq_left.mpr hAC]
    rw [←inf_relIndex_left A.val (Subgroup.centralizer (E : Set G)),hi,inf_relIndex_left]
  have hmono : E.relIndex A.val ≤ E.relIndex C :=
    relIndex_le_of_le_right hAC index_ne_zero_of_finite
  have hcount : C.relIndex E = C.relIndex (P ⊓ E) * P.relIndex E := by
    rw [relIndex_inf_mul_relIndex,inf_eq_left.mpr (show C ≤ P from inf_le_left)]
  have hupper : C.relIndex E ≤ E.relIndex A.val := by
    rw [hcount]
    by_cases hsmall : P.relIndex E ≤ 2^n
    · have hl := d.invariantLift_fixed_index_ge A hA E (hE.1.trans le_sup_right) hout
      rw [hfixed] at hl
      calc
        C.relIndex (P ⊓ E) * P.relIndex E ≤ 2^n * 2^n := Nat.mul_le_mul hN hsmall
        _ = 2^(2*n) := by rw [←pow_add]; congr 1; omega
        _ ≤ E.relIndex A.val := hl
    · have hl := d.invariantLift_largeImage_fixed_index_ge A hA E
        (hE.1.trans le_sup_right) (lt_of_not_ge hsmall)
      rw [hfixed] at hl
      calc
        C.relIndex (P ⊓ E) * P.relIndex E ≤ 2^n * 2^(2*n) :=
          Nat.mul_le_mul hN (d.elementary_joinCore_index_le E (hE.1.trans le_sup_right))
        _ = 2^(3*n) := by rw [←pow_add]; congr 1; omega
        _ ≤ E.relIndex A.val := hl
  have hEC : E.relIndex C = C.relIndex E := le_antisymm
    (by rw [hcount]; exact he.2) (hupper.trans hmono)
  have hAE : E.relIndex A.val = E.relIndex C := le_antisymm hmono (hEC ▸ hupper)
  have card_index (X Y : Subgroup G) :
      Nat.card (X ⊓ Y : Subgroup G) * X.relIndex Y = Nat.card Y := by
    simpa only [relIndex_bot_left,inf_relIndex_right] using
      relIndex_mul_relIndex (⊥ : Subgroup G) (X ⊓ Y) Y bot_le inf_le_right
  have hCcard := card_index E C
  have hEcard := card_index C E
  rw [inf_comm E C,hEC] at hCcard
  refine ⟨hEcard.symm.trans hCcard,?_⟩
  have hgenle : A.val ⊔ (C ⊓ E) ≤ C := sup_le hAC inf_le_left
  apply (eq_of_le_of_card_ge hgenle ?_).symm
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A.val (C ⊓ E)
    ((inf_le_left.trans (show C ≤ Subgroup.centralizer (A.val : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [←inf_assoc,inf_eq_left.mpr hAC] at hprod
  have hAcard := card_index E A.val
  rw [inf_comm E A.val,hAE] at hAcard
  have hCcard' := card_index E C
  rw [inf_comm E C] at hCcard'
  have hpos : 0 < Nat.card (A.val ⊓ E : Subgroup G) := Nat.card_pos
  apply Nat.le_of_mul_le_mul_left (c := Nat.card (A.val ⊓ E : Subgroup G)) _ hpos
  calc
    Nat.card (A.val ⊓ E : Subgroup G) * Nat.card C =
        Nat.card (A.val ⊓ E : Subgroup G) *
          (Nat.card (C ⊓ E : Subgroup G) * E.relIndex C) := by rw [hCcard']
    _ = (Nat.card (A.val ⊓ E : Subgroup G) * E.relIndex C) *
        Nat.card (C ⊓ E : Subgroup G) := by ring
    _ = Nat.card A.val * Nat.card (C ⊓ E : Subgroup G) := by rw [hAcard]
    _ = Nat.card (A.val ⊓ E : Subgroup G) *
        Nat.card (A.val ⊔ (C ⊓ E) : Subgroup G) := hprod
    _ ≤ _ := le_rfl

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
