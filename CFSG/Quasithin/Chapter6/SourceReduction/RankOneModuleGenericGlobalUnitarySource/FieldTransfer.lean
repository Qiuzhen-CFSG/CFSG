module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Orbits
public import Theory.Representation.OrthogonalFourMinusBinaryIrreducibility
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.CyclicQuotientInvolutionTransfer
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# Ambient involution transfer through the original unitary-four field action

The literal Hermitian module is irreducible under L and self-centralizing
in G. Hence O₂(LT) is exactly O₂(L). The full original Sylow's action on
L/O₂(L), followed by the binary PSL₂ field projection, has kernel T ∩ L;
its index divides the actual matrix-field degree 2m. Generalized Thompson
transfer in the original nonabelian simple group puts every ambient
involution into that kernel. The established inner coverage and nonfusion
then give exactly two ambient classes and the actual Thompson order formula.

Both orientations, ordinary and degree-two rows, q=4 and the full quotient
kernel are retained. In particular the degree-two graph involution is fused
into T ∩ L by ambient conjugation; it is not erased from sourceS or from
the constructed extension. This is the fusion part of F.4.38. Ambient
outer-centralizer Sylow placement, odd outer degree and comparison of the
formula with the same marked extension remain separate obligations.

Source: Aschbacher--Smith A.1.37(2), F.4.35,38,43 and 5.3.3, printed
pp.31,292,294,296,659 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

/-- Every original L-invariant subgroup of its Hermitian two-core is trivial or the whole core. -/
theorem Preparation.unitaryFour_core_irreducible
    (E : Subgroup G) (hEQ : E ≤ L.pCoreIn 2)
    (hLE : L ≤ normalizer (E : Set G)) : E = ⊥ ∨ E = L.pCoreIn 2 := by
  let : NeZero m := ⟨by omega⟩
  let Q := L.pCoreIn 2
  obtain ⟨e,f,hf⟩ := d.unitary_core_hermitian_model h hH hp m hm hc
  let B := (E.subgroupOf Q).map f.toMonoidHom
  have hb : ∀ g x, x ∈ B → multiplicativeAction m g x ∈ B := by
    rintro g _ ⟨v,hv,rfl⟩
    obtain ⟨l,hl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    let w := f.symm (multiplicativeAction m g (f v))
    have hw : w.val = (l : G)*v.val*(l : G)⁻¹ := by
      have hh := hf l v
      change e (QuotientGroup.mk' (pCore 2 L) l) = g at hl
      rw [hl] at hh
      exact hh
    refine ⟨w,?_,f.apply_symm_apply _⟩
    change w.val ∈ E
    rw [hw]
    exact (mem_normalizer_iff.mp (hLE l.property) v.val).mp hv
  rcases multiplicativeAction_irreducible m B hb with he | he
  · left
    apply E.eq_bot_iff_forall.mpr
    intro x hx
    have hm : f ⟨x,hEQ hx⟩ ∈ B := mem_map_of_mem f.toMonoidHom hx
    rw [he,mem_bot] at hm
    exact congrArg Subtype.val (f.injective (hm.trans f.map_one.symm))
  · right
    apply le_antisymm hEQ
    intro x hx
    have hm : f ⟨x,hx⟩ ∈ B := he ▸ mem_top _
    obtain ⟨v,hv,hvx⟩ := hm
    have heq : v.val = x := congrArg Subtype.val (f.injective hvx)
    exact heq ▸ (show v.val ∈ E from hv)

/-- The full original Sylow does not enlarge the two-core of L, including in the degree-two row. -/
theorem Preparation.unitaryFour_sylow_join_core_eq :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = L.pCoreIn 2 := by
  have hYN : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer h.sylow_normalizes
  have hz := pCoreIn_le_centralizer_of_irreducible (L.pCoreIn 2) L
    (L ⊔ (T : Subgroup G)) (isPGroup_pCoreIn 2 L)
    ((pCoreIn_le 2 L).trans le_sup_left)
    (hYN.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) le_sup_left
    (d.unitaryFour_core_irreducible h hH hp m hm hc)
  rw [d.unitary_core_centralizer h hH hp m hm hc] at hz
  exact le_antisymm hz (pCoreIn_mono_of_normalizes le_sup_left hYN)

omit d h hH hp hm hc in
/-- The field coefficient of the full original Sylow action on L/O₂(L). -/
@[expose] def unitaryFourSylowFieldAction
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) : T →* (F ≃+* F) :=
  (Theory.PSL2.fieldProjection F).comp ((MulAut.congr e).toMonoidHom.comp
    ((pCoreJoinAction 2 hTL).comp (inclusion le_sup_right)))

omit d h hH hp hm hc [Finite G] in
private theorem quotient_inner_iff
    {K V : Subgroup G} (hVK : V ≤ normalizer (K : Set G))
    (hV : IsPGroup 2 V) (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hcore : (K ⊔ V : Subgroup G).pCoreIn 2 ≤ K)
    (x : (K ⊔ V : Subgroup G)) :
    pCoreJoinAction 2 hVK x ∈ MulAut.innerSubgroup (K ⧸ pCore 2 K) ↔ x.val ∈ K := by
  let f := pCoreJoinAction 2 hVK
  constructor
  · rintro ⟨z,hzinner⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
    have he : f (inclusion le_sup_left k) = f x :=
      (pCoreJoinAction_on_component 2 hVK k).trans hzinner
    have hx : x * (inclusion le_sup_left k)⁻¹ ∈ f.ker := by
      change f (x * (inclusion le_sup_left k)⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [pCoreJoinAction_kernel 2 hVK hV hz] at hx
    have hk := hcore (mem_map_of_mem (K ⊔ V).subtype hx)
    have hh := K.mul_mem hk k.property
    change (x.val * k.val⁻¹) * k.val ∈ K at hh
    simpa only [inv_mul_cancel_right] using hh
  · intro hx
    let k : K := ⟨x.val,hx⟩
    have he : inclusion (show K ≤ K ⊔ V from le_sup_left) k = x := Subtype.ext rfl
    rw [←he,pCoreJoinAction_on_component]
    exact ⟨_,rfl⟩

/-- The actual left quotient field action has exactly T ∩ L as kernel; sourceS is not substituted for it. -/
theorem Preparation.unitaryFour_sylow_field_kernel
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) :
    (unitaryFourSylowFieldAction h.sylow_normalizes e).ker =
      L.subgroupOf (T : Subgroup G) := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [center_map_equiv,Subgroup.map_bot]
    apply bot_unique
    intro x hx
    apply Theory.PSL2.psl2_conj_eq_one_implies x
    ext y
    change x*y*x⁻¹=y
    rw [←mem_center_iff.mp hx y,mul_inv_cancel_right]
  ext t
  change Theory.PSL2.fieldProjection F
    ((MulAut.congr e) (pCoreJoinAction 2 h.sylow_normalizes
      (inclusion le_sup_right t))) = 1 ↔ t.val ∈ L
  rw [←MonoidHom.mem_ker,Theory.PSL2.fieldProjection_ker]
  have hi (a : MulAut (L ⧸ pCore 2 L)) :
      MulAut.congr e a ∈ Theory.PSL2.inner F ↔
        a ∈ MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
    change MulAut.congr e a ∈ MulAut.innerSubgroup (Theory.PSL2.Group F) ↔ _
    rw [←MulAut.map_innerSubgroup_congr e]
    exact mem_map_iff_mem (MulAut.congr e).injective
  rw [hi,quotient_inner_iff _ T.isPGroup' hz
    ((d.unitaryFour_sylow_join_core_eq h hH hp m hm hc).le.trans (pCoreIn_le 2 L))]
  rfl

/-- The reduced Sylow index divides the matrix-field degree 2m, with its possible even factor retained. -/
theorem Preparation.unitaryFour_reduced_sylow_index_dvd :
    L.relIndex (T : Subgroup G) ∣ 2*m := by
  have hn : n = 2*m := (d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc).2.1
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  change (L.subgroupOf (T : Subgroup G)).index ∣ 2*m
  rw [←d.unitaryFour_sylow_field_kernel h hH hp m hm hc e,index_ker]
  exact (unitaryFourSylowFieldAction h.sylow_normalizes e).range.card_subgroup_dvd_card.trans
    (dvd_of_eq ((FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF).trans hn))

/-- Cyclic field-action transfer puts every ambient involution into the reduced Sylow, without an outer-parity premise. -/
theorem Preparation.unitaryFour_involution_fused_into_reduced_sylow
    (x : G) (hx : orderOf x=2) : ∃ y ∈ (T : Subgroup G) ⊓ L, IsConj x y := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : CommGroup (F ≃+* F) := IsCyclic.commGroup
  let : IsSimpleGroup G := h.qtke.simple
  obtain ⟨a,hxa⟩ := T.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have ha : orderOf a=2 := by
    rw [←Subgroup.orderOf_coe]
    obtain ⟨g,hg⟩ := isConj_iff.mp hxa
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  obtain ⟨b,hab,hb⟩ := T.exists_isConj_ker_of_cyclic_of_simple h.qtke.nonabelian
    (unitaryFourSylowFieldAction h.sylow_normalizes e) a ha
  have hbL : b.val ∈ L := by
    change b ∈ L.subgroupOf (T : Subgroup G)
    rw [←d.unitaryFour_sylow_field_kernel h hH hp m hm hc e]
    exact hb
  exact ⟨b.val,⟨b.property,hbL⟩,hxa.trans hab⟩

/-- Exactly two involution classes cover the entire original group, with representatives in O₂(L). -/
theorem Preparation.unitaryFour_ambient_two_classes :
    ∃ z ∈ L.pCoreIn 2, ∃ t ∈ L.pCoreIn 2,
      orderOf z = 2 ∧ orderOf t = 2 ∧ ¬ IsConj z t ∧
        ∀ x : G, orderOf x = 2 → IsConj x z ∨ IsConj x t := by
  obtain ⟨z,hz,t,ht,hz2,ht2,hzt,hcover⟩ := d.unitary_inner_two_classes h hH hp m hm hc
  refine ⟨z,hz,t,ht,hz2,ht2,hzt,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := d.unitaryFour_involution_fused_into_reduced_sylow h hH hp m hm hc x hx
  have hy2 : orderOf y=2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hxy
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  exact (hcover y hy hy2).elim (fun hz => Or.inl (hxy.trans hz))
    (fun ht => Or.inr (hxy.trans ht))

/-- The actual ambient Thompson formula, with coverage and nonfusion supplied by the prepared row. -/
theorem Preparation.unitaryFour_ambient_thompson_order :
    ∃ z ∈ L.pCoreIn 2, ∃ t ∈ L.pCoreIn 2,
      orderOf z = 2 ∧ orderOf t = 2 ∧ ¬ IsConj z t ∧
      (∀ x : G, orderOf x = 2 → IsConj x z ∨ IsConj x t) ∧
      Nat.card G = TwoInvolutionClassOrder.kappa z t z * Nat.card (centralizer ({t} : Set G)) +
        TwoInvolutionClassOrder.kappa z t t * Nat.card (centralizer ({z} : Set G)) := by
  obtain ⟨z,hz,t,ht,hz2,ht2,hzt,hcover⟩ := d.unitaryFour_ambient_two_classes h hH hp m hm hc
  exact ⟨z,hz,t,ht,hz2,ht2,hzt,hcover,TwoInvolutionClassOrder.card_eq z t hz2 ht2 hzt
    (fun x hx => (hcover x hx).elim (fun hz => Or.inl hz.symm) (fun ht => Or.inr ht.symm))⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
