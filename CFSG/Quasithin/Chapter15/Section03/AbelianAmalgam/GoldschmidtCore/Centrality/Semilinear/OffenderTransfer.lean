module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ActualAction
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.Stability

/-!
# The actual Thompson image consists of best offenders

Let A have maximum order among elementary subgroups of S, and let W≤S
be an elementary module. For the literal centralizer quotient q, compare
A with L C_W(L), where C_A(W)≤L≤A. Maximum order and the subgroup product
formula give |q(L)| |C_W(L)| ≤ |q(A)| |C_W(A)|. Consequently every
nontrivial q(A) is a best offender, not just a group containing an offender.

Taking all maximum elementary subgroups places the entire Thompson image
inside the best-offender-generated subgroup. Its normality then places
the image of X=[X,J(S)] there. The internal transport preserves both the
actual ambient vector carrier and the quotient map used by recognition.

This supplies the offender premise for the repaired semilinear branch of
Aschbacher–Smith 15.3.68 and the argument on printed p.1155 (combined
manuscript, 1 March 2004); compare B.1.3 and B.2.4. It asserts neither
equality of ordinary Thompson and offender groups nor a classification.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G J : Type*} [Group G] [Group J] [Finite G] [Finite J]

private theorem maximum_fixed_eq (S V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    V ⊓ centralizer (A : Set G) = A ⊓ V := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let C := V ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have he := IsElementaryAbelian.sup_of_le_centralizer (p := 2) (E := A) (C := C) inf_le_right
  have hmax := hA.2.2 (A ⊔ C) (sup_le hA.1 (inf_le_left.trans hVS)) he
  have hAC : A = A ⊔ C := Subgroup.eq_of_le_of_card_ge le_sup_left hmax
  apply le_antisymm
  · exact le_inf (le_sup_right.trans hAC.ge) inf_le_left
  · exact le_inf inf_le_right (inf_le_left.trans
      (le_centralizer_iff_isMulCommutative.mpr inferInstance))

omit [Finite G] [Finite J] in
private theorem card_kernel_image (q : G →* J) (A : Subgroup G) :
    Nat.card (A ⊓ q.ker : Subgroup G) * Nat.card (A.map q) = Nat.card A := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) (q.ker ⊓ A) A bot_le inf_le_right
  rw [relIndex_bot_left,inf_relIndex_right,relIndex_ker] at h
  simpa only [inf_comm,relIndex_bot_left] using h

omit [Finite J] in
private theorem maximum_card_weight (S V A L : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (q : G →* J) (hker : q.ker = centralizer (V : Set G))
    (hLA : L ≤ A) (hCL : A ⊓ q.ker ≤ L) :
    Nat.card (L.map q) * Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) ≤
      Nat.card (A.map q) * Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 L := IsElementaryAbelian.of_le hLA
  let D := V ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le inf_le_left
  have hD := IsElementaryAbelian.sup_of_le_centralizer (p := 2) (E := L) (C := D) inf_le_right
  have hmax : Nat.card (L ⊔ D : Subgroup G) ≤ Nat.card A :=
    hA.2.2 _ (sup_le (hLA.trans hA.1) (inf_le_left.trans hVS)) hD
  have hAV : A ⊓ V ≤ A ⊓ q.ker := by
    rw [hker]
    exact inf_le_inf_left A (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hLD : L ⊓ D = A ⊓ V := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans hLA) (inf_le_right.trans inf_le_left)
    · exact le_inf (hAV.trans hCL) (le_inf inf_le_right
        (inf_le_left.trans ((le_centralizer_iff_isMulCommutative.mpr
          (inferInstance : IsMulCommutative A)).trans (centralizer_le hLA))))
  have hLK : L ⊓ q.ker = A ⊓ q.ker := le_antisymm (inf_le_inf_right _ hLA)
    (le_inf hCL inf_le_right)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes L D
    (inf_le_right.trans (centralizer_le_normalizer (L : Set G)))
  rw [hLD] at hprod
  have hLc := card_kernel_image q L
  rw [hLK] at hLc
  have hAc := card_kernel_image q A
  have hpos : 0 < Nat.card (A ⊓ q.ker : Subgroup G) := Nat.card_pos
  rw [maximum_fixed_eq S V A hVS hA]
  have hb : Nat.card L * Nat.card D ≤ Nat.card (A ⊓ V : Subgroup G) * Nat.card A := by
    rw [hprod]
    exact Nat.mul_le_mul_left _ hmax
  rw [← hLc,← hAc] at hb
  nlinarith

private noncomputable def actual_fixed_equiv (V : Subgroup G) [IsElementaryAbelian 2 V]
    (q : G →* J) (ρ : Representation (ZMod 2) J (Additive V))
    (hact : ∀ (g : G) (v : Additive V),
      ((ρ (q g) v).toMul : G) = g * (v.toMul : G) * g⁻¹)
    (A : Subgroup G) : fixedSpace ρ (A.map q) ≃ (V ⊓ centralizer (A : Set G) : Subgroup G) := by
  have hi (v : Additive V) : v ∈ fixedSpace ρ (A.map q) ↔
      (v.toMul : G) ∈ centralizer (A : Set G) := by
    constructor
    · intro hv a ha
      have he := congrArg (fun v : Additive V => (v.toMul : G)) (hv ⟨q a,mem_map_of_mem q ha⟩)
      change ((ρ (q a) v).toMul : G) = v.toMul at he
      rw [hact] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hv a
      obtain ⟨g,hg,he⟩ := a.property
      change ρ (a : J) v = v
      rw [← he]
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hact,hv g hg,mul_inv_cancel_right]
  exact {
    toFun v := ⟨v.val.toMul,v.val.toMul.property,(hi v.val).mp v.property⟩
    invFun v := ⟨Additive.ofMul ⟨v,v.property.1⟩,(hi _).mpr v.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }

private theorem actual_weight_card (V A : Subgroup G) [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 A]
    (q : G →* J) (ρ : Representation (ZMod 2) J (Additive V))
    (hact : ∀ (g : G) (v : Additive V),
      ((ρ (q g) v).toMul : G) = g * (v.toMul : G) * g⁻¹) :
    2 ^ weight ρ (A.map q) =
      Nat.card (A.map q) * Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) := by
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hi : 2 ^ rank (A.map q) = Nat.card (A.map q) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (A.map q)).exists_card_eq
    simp only [rank,hn,Nat.log_pow Nat.one_lt_two]
  have hf : 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (A.map q)) =
      Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) := by
    rw [← Nat.card_congr (actual_fixed_equiv V q ρ hact A)]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (A.map q))).symm
  rw [weight,pow_add,hi,hf]

/-- A maximum elementary subgroup has a best-offender image on an actual
faithful centralizer quotient, not merely an offender somewhere inside that image. -/
theorem maximum_image_bestOffender (S V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (q : G →* J) (hker : q.ker = centralizer (V : Set G))
    (ρ : Representation (ZMod 2) J (Additive V))
    (hact : ∀ (g : G) (v : Additive V),
      ((ρ (q g) v).toMul : G) = g * (v.toMul : G) * g⁻¹)
    (hne : A.map q ≠ ⊥) : IsBestOffender ρ (A.map q) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  refine ⟨⟨hne,inferInstance⟩,?_⟩
  intro B hB
  let L := A ⊓ B.comap q
  have hLA : L ≤ A := inf_le_left
  let : IsElementaryAbelian 2 L := IsElementaryAbelian.of_le hLA
  have hL : L.map q = B := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩; exact hx.2
    · intro b hb
      obtain ⟨a,ha,he⟩ := hB hb
      exact ⟨a,⟨ha,by change q a ∈ B; rw [he]; exact hb⟩,he⟩
  have hCL : A ⊓ q.ker ≤ L := by
    rintro a ⟨ha,hk⟩
    exact ⟨ha,by change q a ∈ B; rw [show q a = 1 from hk]; exact B.one_mem⟩
  have hb := maximum_card_weight S V A L hVS hA q hker hLA hCL
  rw [← actual_weight_card V L q ρ hact,← actual_weight_card V A q ρ hact,hL] at hb
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hb


/-- The full Thompson image lies in the actual best-offender-generated subgroup. -/
theorem thompson_image_le_offender (S V : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (q : G →* J) (hker : q.ker = centralizer (V : Set G))
    (ρ : Representation (ZMod 2) J (Additive V))
    (hact : ∀ (g : G) (v : Additive V),
      ((ρ (q g) v).toMul : G) = g * (v.toMul : G) * g⁻¹) :
    (elementaryAbelianMaxJ S).map q ≤ offenderSubgroup ρ := by
  apply (map_le_iff_le_comap).mpr
  apply sSup_le
  intro A hA
  apply (map_le_iff_le_comap).mp
  by_cases hz : A.map q = ⊥
  · rw [hz]; exact bot_le
  · have hb := maximum_image_bestOffender S V A hVS hA q hker ρ hact hz
    exact le_iSup_of_le (A.map q) (le_iSup_of_le ⟨hb,le_top⟩ le_rfl)

/-- The genuine residual/Thompson source identity transfers X into the
best-offender subgroup. No equality of ordinary Thompson and offender groups is used. -/
theorem thompson_commutator_image_le_offender
    (S V X : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (q : G →* J) (hker : q.ker = centralizer (V : Set G))
    (ρ : Representation (ZMod 2) J (Additive V))
    (hact : ∀ (g : G) (v : Additive V),
      ((ρ (q g) v).toMul : G) = g * (v.toMul : G) * g⁻¹)
    (hX : X = ⁅X,elementaryAbelianMaxJ S⁆) : X.map q ≤ offenderSubgroup ρ := by
  let := offenderSubgroup_normal ρ
  rw [hX,map_commutator]
  exact (commutator_mono le_top (thompson_image_le_offender S V hVS q hker ρ hact)).trans
    (commutator_le_right ⊤ (offenderSubgroup ρ))


omit [Finite J] in
private theorem offender_subgroup_le_of_equiv
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) J V) (ρ : Representation (ZMod 2) J W)
    (e : V ≃ₗ[ZMod 2] W) (he : ∀ j v, e (σ j v) = ρ j (e v)) :
    offenderSubgroup σ ≤ offenderSubgroup ρ := by
  have hweight (A : Subgroup J) : weight σ A = weight ρ A := by
    let f : fixedSpace σ A ≃ₗ[ZMod 2] fixedSpace ρ A := {
      toFun v := ⟨e v,fun a => (he a v).symm.trans (congrArg e (v.property a))⟩
      invFun w := ⟨e.symm w,by
        intro a
        apply e.injective
        change e (σ (a : J) (e.symm (w : W))) = e (e.symm (w : W))
        rw [he,e.apply_symm_apply]
        exact w.property a⟩
      left_inv v := Subtype.ext (e.symm_apply_apply v)
      right_inv w := Subtype.ext (e.apply_symm_apply w)
      map_add' v w := Subtype.ext (e.map_add v w)
      map_smul' c v := Subtype.ext (e.map_smul c v) }
    exact congrArg (rank A + ·) f.finrank_eq
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA,_⟩
  have hB : IsBestOffender ρ A := ⟨hA.1,fun B hBA => by
    rw [← hweight B,← hweight A]; exact hA.2 B hBA⟩
  exact le_iSup_of_le A (le_iSup_of_le ⟨hB,le_top⟩ le_rfl)

/-- Transport the Thompson/offender comparison to literal ambient subgroups,
without changing the vector carrier or quotient map used by recognition. -/
theorem internal_thompson_commutator_image_le_offender
    (H S W X : Subgroup G) [IsElementaryAbelian 2 W]
    (hSH : S ≤ H) (hWS : W ≤ S) (hXH : X ≤ H)
    (hHW : H ≤ normalizer (W : Set G))
    (q : H →* J) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (W.subgroupOf H : Set H))
    (ρ : Representation (ZMod 2) J (Additive W))
    (hact : ∀ (h : H) (w : Additive W),
      ((ρ (q h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹)
    (hX : X = ⁅X,elementaryAbelianMaxJ S⁆) :
    (X.subgroupOf H).map q ≤ offenderSubgroup ρ := by
  have hWH := hWS.trans hSH
  let Wi := W.subgroupOf H
  let : Wi.Normal := normal_subgroupOf_of_le_normalizer hHW
  let : IsElementaryAbelian 2 Wi := IsElementaryAbelian.subgroupOf hWH
  let σ := NormalElementaryQuotient.representation Wi q hq hker
  let ea := (subgroupOfEquivOfLe hWH).toAdditive
  let e : Additive Wi ≃ₗ[ZMod 2] Additive W :=
    ea.toLinearEquiv (fun c v => ZMod.map_smul ea.toAddMonoidHom c v)
  have he (j : J) (v : Additive Wi) : e (σ j v) = ρ j (e v) := by
    obtain ⟨h,rfl⟩ := hq j
    apply Additive.toMul.injective
    apply Subtype.ext
    have hv := congrArg (fun a : H => (a : G))
      (NormalElementaryQuotient.representation_apply Wi q hq hker h v)
    change (((σ (q h) v).toMul : H) : G) = ((ρ (q h) (e v)).toMul : G)
    rw [hact]
    exact hv
  have hXi : X.subgroupOf H = ⁅X.subgroupOf H,elementaryAbelianMaxJ (S.subgroupOf H)⁆ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hXH,
      ← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hSH]
    exact hX
  have hi := thompson_commutator_image_le_offender (S.subgroupOf H) Wi (X.subgroupOf H)
    (subgroupOf_mono H hWS) q hker σ
    (NormalElementaryQuotient.representation_apply Wi q hq hker) hXi
  exact hi.trans (offender_subgroup_le_of_equiv σ ρ e he)


omit [Finite G] [Finite J] in
/-- Faithfulness and the literal conjugation formula identify the intrinsic
quotient kernel with the centralizer, including all subgroup coercions. -/
theorem faithful_conjugation_kernel (H W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWH : W ≤ H) (q : H →* J)
    (ρ : Representation (ZMod 2) J (Additive W)) (hfaith : Function.Injective ρ)
    (hact : ∀ (h : H) (w : Additive W),
      ((ρ (q h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹) :
    q.ker = centralizer (W.subgroupOf H : Set H) := by
  ext h
  constructor
  · intro hh v hv
    apply Subtype.ext
    have he := hact h (Additive.ofMul ⟨v,hv⟩)
    rw [show q h = 1 from hh,map_one] at he
    change (v : G) = (h : G) * (v : G) * (h : G)⁻¹ at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · intro hh
    apply hfaith
    rw [map_one]
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hact]
    change (h : G) * (w.toMul : G) * (h : G)⁻¹ = w.toMul
    have he := congrArg Subtype.val (hh (⟨w.toMul,hWH w.toMul.property⟩ : H) w.toMul.property)
    change (w.toMul : G) * (h : G) = (h : G) * (w.toMul : G) at he
    rw [← he,mul_inv_cancel_right]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
