module
public import Theory.Representation.SL3.NaturalDualElementaryLift
public import Theory.GroupTheory.FixedSupplementCentralizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup

/-!
# Elementary dual lifts in the original nonblock core

The actual MS quotient map identifies Q/Z(Q) with two copies of the dual
of its natural center. The nonzero covector stabilizer has no natural
fixed vector, so squaring vanishes on every diagonal dual lift. Transport
through the original quotient and subtype maps gives elementary abelian
subgroups of order 2^(6n), normalized by K.

The two coordinate lifts intersect in Z(Q) and generate Q. Since they are
abelian, their centralizers in Q are exactly themselves. These are the
elementary-lift and self-centralizer conclusions used in C.1.35's core
argument. Construction of MSData, the remaining C.1.35 core argument and
the final nonblock contradiction remain with this module's assembly owner,
qt-d-1222-rankone-uniqueness-nonblock. No identity Q=O₂(KS) is assumed here.

Source: Aschbacher--Smith, C.1.35(2), printed pp.137--138, applied to
original 4.3.10--11, printed p.617.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Representation.SL3ParabolicNatural
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private theorem MSData.exists_elementary_coordinates (d : MSData c n) :
    ∃ p : Q c →* Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
      Function.Surjective p ∧ p.ker = (U c).subgroupOf (Q c) ∧
      (∀ (k : K c) (q r : Q c), (r : G) = k * q * (k : G)⁻¹ →
        (p r).toAdd =
          ((Representation.specialLinearNatural 3).dual.prod
            (Representation.specialLinearNatural 3).dual)
              (linearThreeActor d.model k) (p q).toAdd) ∧
      ∀ a b : d.field.Carrier,
        IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p) := by
  obtain ⟨hUQ,hKnQ,_,hn,e,he⟩ := d.doubleDual
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' ((U c).subgroupOf (Q c)))
  have hk : p.ker = (U c).subgroupOf (Q c) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hpi : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hpe (k : K c) (q r : Q c) (hr : (r : G) = k*q*(k : G)⁻¹) :
      (p r).toAdd =
        ((Representation.specialLinearNatural 3).dual.prod
          (Representation.specialLinearNatural 3).dual)
            (linearThreeActor d.model k) (p q).toAdd := he k q r hr
  refine ⟨p,hpi,hk,hpe,?_⟩
  have hnatural := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hnatural
  obtain ⟨_,_,_,hn₀,e₀,he₀⟩ := hnatural
  let := hn₀
  let u₀ : U c ≃* Multiplicative (Fin 3 → d.field.Carrier) :=
    QuotientGroup.quotientBot.symm.trans e₀
  let uk : p.ker ≃* U c :=
    (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe hUQ)
  let u := uk.trans u₀
  have hc : p.ker ≤ center (Q c) := by
    intro q hq
    have hqU : (q : G) ∈ U c := by rwa [hk] at hq
    obtain ⟨z,hz,heq⟩ := hqU
    exact (show z = q from Subtype.ext heq) ▸ hz
  let := conjMulDistribMulActionOfLeNormalizer (K c) (Q c) hKnQ
  have hp (k : K c) (q : Q c) : (p (k • q)).toAdd =
      ((Representation.specialLinearNatural 3).dual.prod
        (Representation.specialLinearNatural 3).dual)
          (linearThreeActor d.model k) (p q).toAdd := hpe k q (k • q) rfl
  have hu (k : K c) (x y : p.ker) (hy : (y : Q c) = k • (x : Q c)) :
      (u y).toAdd = Representation.specialLinearNatural 3
        (linearThreeActor d.model k) (u x).toAdd := by
    apply he₀ k (uk x) (uk y)
    exact congrArg Subtype.val hy
  exact fun a b => dualDiagonal_preimage_elementary (linearThreeActor d.model)
    (d.model.surjective.comp (QuotientGroup.mk'_surjective _)) p hc u hp hu a b

/-- The full preimage in the original Q of a diagonal dual summand. -/
def dualLift (d : MSData c n)
    (p : Q c →* Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))
    (a b : d.field.Carrier) : Subgroup G :=
  ((dualDiagonal a b).range.comap p).map (Q c).subtype

private theorem dualLift_normalized (d : MSData c n)
    (p : Q c →* Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))
    (hp : ∀ (k : K c) (q r : Q c), (r : G) = k * q * (k : G)⁻¹ →
        (p r).toAdd =
          ((Representation.specialLinearNatural 3).dual.prod
            (Representation.specialLinearNatural 3).dual)
              (linearThreeActor d.model k) (p q).toAdd)
    (a b : d.field.Carrier) : K c ≤ normalizer (dualLift d p a b : Set G) := by
  have hf (k : K c) (q : G) (hq : q ∈ dualLift d p a b) :
      (k : G)*q*(k : G)⁻¹ ∈ dualLift d p a b := by
    obtain ⟨q,⟨f,hf⟩,rfl⟩ := hq
    let r : Q c := ⟨(k : G)*q*(k : G)⁻¹,
      (mem_normalizer_iff.mp (d.doubleDual.2.1 k.property) q).mp q.property⟩
    refine ⟨r,⟨Multiplicative.ofAdd
      ((Representation.specialLinearNatural 3).dual (linearThreeActor d.model k) f.toAdd),?_⟩,rfl⟩
    apply Multiplicative.toAdd.injective
    rw [hp k q r rfl,←hf]
    change (a • _,b • _) =
      (((Representation.specialLinearNatural 3).dual (linearThreeActor d.model k)) (a • f.toAdd),
        ((Representation.specialLinearNatural 3).dual (linearThreeActor d.model k)) (b • f.toAdd))
    rw [map_smul,map_smul]
    rfl
  intro k hk
  apply mem_normalizer_iff.mpr
  intro q
  constructor
  · exact hf ⟨k,hk⟩ q
  · intro hq
    have hh := hf ⟨k⁻¹,(K c).inv_mem hk⟩ _ hq
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh

private theorem card_preimage {J H : Type*} [Group J] [Group H]
    (p : J →* H) (hp : Function.Surjective p) (B : Subgroup H) :
    Nat.card (B.comap p) = Nat.card B * Nat.card p.ker := by
  let W := B.comap p
  let f := p.comp W.subtype
  have hr : f.range = B := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact x.property
    · intro hy
      obtain ⟨x,hx⟩ := hp y
      exact ⟨⟨x,show p x ∈ B from hx.symm ▸ hy⟩,hx⟩
  have hk : f.ker = p.ker.subgroupOf W := rfl
  have hle : p.ker ≤ W := by
    intro x hx
    change p x ∈ B
    rw [show p x = 1 from hx]
    exact B.one_mem
  have hc := f.ker.index_mul_card
  rw [index_ker,hr,hk,Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hc
  exact hc.symm

private theorem dualLift_card (d : MSData c n)
    (p : Q c →* Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))
    (hp : Function.Surjective p) (hk : p.ker = (U c).subgroupOf (Q c))
    (a b : d.field.Carrier) (hab : a ≠ 0 ∨ b ≠ 0) :
    Nat.card (dualLift d p a b) = 2 ^ (6*n) := by
  have hUQ : U c ≤ Q c := d.doubleDual.1
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,e,_⟩ := hm
  let := hn
  have hU : Nat.card (U c) = (Nat.card d.field.Carrier)^3 := by
    rw [Nat.card_congr (QuotientGroup.quotientBot.symm.trans e).toEquiv]
    change Nat.card (Fin 3 → d.field.Carrier) = _
    rw [Nat.card_fun,Nat.card_fin]
  have hker : Nat.card p.ker = (Nat.card d.field.Carrier)^3 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hUQ).toEquiv,hU]
  have hline : Nat.card (dualDiagonal a b).range = (Nat.card d.field.Carrier)^3 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective (dualDiagonal_injective hab)).toEquiv]
    change Nat.card (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)) = _
    rw [Module.natCard_eq_pow_finrank (K := d.field.Carrier),Subspace.dual_finrank_eq,
      Module.finrank_fin_fun]
  let W := (dualDiagonal a b).range.comap p
  rw [show Nat.card (dualLift d p a b) = Nat.card W from
    (Nat.card_congr (W.equivMapOfInjective (Q c).subtype (Q c).subtype_injective).toEquiv).symm]
  rw [card_preimage p hp,hline,hker,d.field.card_eq,d.degree_eq,←pow_add,←pow_mul]
  congr 1
  omega

private theorem dualLift_center_le (d : MSData c n)
    (p : Q c →* Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))
    (hk : p.ker = (U c).subgroupOf (Q c)) (a b : d.field.Carrier) :
    U c ≤ dualLift d p a b := by
  intro z hz
  let zQ : Q c := ⟨z,d.doubleDual.1 hz⟩
  have hzk : zQ ∈ p.ker := by rw [hk]; exact hz
  refine ⟨zQ,?_,rfl⟩
  change p zQ ∈ (dualDiagonal a b).range
  rw [show p zQ = 1 from hzk]
  exact (dualDiagonal a b).range.one_mem

/-- The original quotient marking supplies all elementary dual-line lifts,
with their exact order and normalization in K. No core identity for KS is used. -/
theorem MSData.exists_elementary_dual_lifts (d : MSData c n) :
    ∃ p : Q c →* Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
      Function.Surjective p ∧ p.ker = (U c).subgroupOf (Q c) ∧
      (∀ (k : K c) (q r : Q c), (r : G) = k * q * (k : G)⁻¹ →
        (p r).toAdd =
          ((Representation.specialLinearNatural 3).dual.prod
            (Representation.specialLinearNatural 3).dual)
              (linearThreeActor d.model k) (p q).toAdd) ∧
      ∀ a b : d.field.Carrier,
        IsElementaryAbelian 2 (dualLift d p a b) ∧
        U c ≤ dualLift d p a b ∧ dualLift d p a b ≤ Q c ∧
        K c ≤ normalizer (dualLift d p a b : Set G) ∧
        (a ≠ 0 ∨ b ≠ 0 → Nat.card (dualLift d p a b) = 2^(6*n)) := by
  obtain ⟨p,hp,hk,he,hel⟩ := d.exists_elementary_coordinates
  refine ⟨p,hp,hk,he,?_⟩
  intro a b
  let := hel a b
  exact ⟨IsElementaryAbelian.map_subtype,dualLift_center_le d p hk a b,
    map_subtype_le _,dualLift_normalized d p he a b,dualLift_card d p hp hk a b⟩

private theorem diagonal_axes_inf (F : Type*) [Field F] :
    (dualDiagonal (1:F) 0).range ⊓ (dualDiagonal (0:F) 1).range = ⊥ := by
  apply bot_unique
  rintro v ⟨⟨f,hf⟩,⟨g,hg⟩⟩
  apply mem_bot.mpr
  apply Multiplicative.toAdd.injective
  have hfst := congrArg (fun z => z.toAdd.1) hg
  have hsnd := congrArg (fun z => z.toAdd.2) hf
  change (v.toAdd.1,v.toAdd.2) = (0,0)
  change (0 : F) • g.toAdd = v.toAdd.1 at hfst
  change (0 : F) • f.toAdd = v.toAdd.2 at hsnd
  exact Prod.ext (by simpa only [zero_smul] using hfst.symm)
    (by simpa only [zero_smul] using hsnd.symm)

private theorem diagonal_axes_sup (F : Type*) [Field F] :
    (dualDiagonal (1:F) 0).range ⊔ (dualDiagonal (0:F) 1).range = ⊤ := by
  apply top_unique
  intro v _
  have he : v = dualDiagonal (1:F) 0 (Multiplicative.ofAdd v.toAdd.1) *
      dualDiagonal (0:F) 1 (Multiplicative.ofAdd v.toAdd.2) := by
    apply Multiplicative.toAdd.injective
    change v.toAdd = (1 • v.toAdd.1,0 • v.toAdd.1) + (0 • v.toAdd.2,1 • v.toAdd.2)
    simp only [one_smul,zero_smul,Prod.mk_add_mk,add_zero,zero_add]
  rw [he]
  exact mul_mem_sup ⟨_,rfl⟩ ⟨_,rfl⟩

/-- Apply the diagonal-lift construction to the two actual quotient summands.
They generate Q, intersect precisely in Z(Q), and each has order 2^(6n), as
required at the start of C.1.35's core argument. -/
theorem MSData.exists_elementary_core_decomposition (d : MSData c n) :
    ∃ A B : Subgroup G,
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 2^(6*n) ∧ Nat.card B = 2^(6*n) ∧
      K c ≤ normalizer (A : Set G) ∧ K c ≤ normalizer (B : Set G) ∧
      A ⊓ B = U c ∧ A ⊔ B = Q c := by
  obtain ⟨p,hp,hk,_,hl⟩ := d.exists_elementary_dual_lifts
  have ha := hl 1 0
  have hb := hl 0 1
  refine ⟨dualLift d p 1 0,dualLift d p 0 1,ha.1,hb.1,
    ha.2.2.2.2 (Or.inl one_ne_zero),hb.2.2.2.2 (Or.inr one_ne_zero),
    ha.2.2.2.1,hb.2.2.2.1,?_,?_⟩
  · rw [dualLift,dualLift,←map_inf _ _ _ (Q c).subtype_injective,
      ←comap_inf,diagonal_axes_inf,MonoidHom.comap_bot,hk,
      map_subgroupOf_eq_of_le d.doubleDual.1]
  · rw [dualLift,dualLift,←Subgroup.map_sup,comap_sup_eq _ _ _ hp,
      diagonal_axes_sup,comap_top,←MonoidHom.range_eq_map,range_subtype]


private theorem centralizer_eq_of_abelian_pair (Q A B : Subgroup G)
    [IsMulCommutative A] [IsMulCommutative B]
    (hAB : A ≤ normalizer (B : Set G)) (hQ : A ⊔ B = Q)
    (hZA : (center Q).map Q.subtype ≤ A) :
    Q ⊓ Subgroup.centralizer (A : Set G) = A := by
  have hAQ : A ≤ Q := hQ ▸ le_sup_left
  have hBQ : B ≤ Q := hQ ▸ le_sup_right
  let C := B ⊓ Subgroup.centralizer (A : Set G)
  have hQC : Q ≤ centralizer (C : Set G) := by
    rw [←hQ]
    apply sup_le
    · exact le_centralizer_iff.mpr (show C ≤ Subgroup.centralizer (A : Set G) from inf_le_right)
    · exact (le_centralizer B).trans (centralizer_le inf_le_left)
  have hCA : C ≤ A := by
    intro x hx
    apply hZA
    refine ⟨⟨x,hBQ hx.1⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (hQC y.property x hx).symm
  rw [←hQ, inf_centralizer_sup_of_centralizing A B A hAB (le_centralizer A)]
  exact sup_eq_left.mpr hCA

/-- The two original dual summands lift to self-centralizing elementary
subgroups in Q. This supplies the centralizer input to C.1.35's core proof
without a separate pairing or nondegeneracy assumption. -/
theorem MSData.exists_selfCentralizing_elementary_core_decomposition (d : MSData c n) :
    ∃ A B : Subgroup G,
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 2^(6*n) ∧ Nat.card B = 2^(6*n) ∧
      K c ≤ normalizer (A : Set G) ∧ K c ≤ normalizer (B : Set G) ∧
      A ⊓ B = U c ∧ A ⊔ B = Q c ∧
      Q c ⊓ Subgroup.centralizer (A : Set G) = A ∧
      Q c ⊓ Subgroup.centralizer (B : Set G) = B := by
  obtain ⟨A,B,hA,hB,hAc,hBc,hAn,hBn,hi,hs⟩ := d.exists_elementary_core_decomposition
  let := hA
  let := hB
  have hAQ : A ≤ Q c := hs ▸ le_sup_left
  have hBQ : B ≤ Q c := hs ▸ le_sup_right
  have hQK : Q c ≤ K c := (Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 _) le_rfl)
  have hUA : U c ≤ A := hi ▸ inf_le_left
  have hUB : U c ≤ B := hi ▸ inf_le_right
  exact ⟨A,B,hA,hB,hAc,hBc,hAn,hBn,hi,hs,
    centralizer_eq_of_abelian_pair (Q c) A B (hAQ.trans (hQK.trans hBn)) hs hUA,
    centralizer_eq_of_abelian_pair (Q c) B A (hBQ.trans (hQK.trans hAn))
      ((sup_comm B A).trans hs) hUB⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
