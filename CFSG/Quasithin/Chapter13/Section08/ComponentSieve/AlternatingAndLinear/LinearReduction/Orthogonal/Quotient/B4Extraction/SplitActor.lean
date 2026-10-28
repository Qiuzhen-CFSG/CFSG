module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.IndexTwo
public import Theory.Representation.BinaryOffender.SectionLinear
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.FieldTheory.Finiteness

/-!
# The original quadratic actor on an exchanged A₈ constituent

For a faithful S₈ representation with a split restriction to the marked A₈,
simplicity makes each constituent faithful. Indeed, if the left constituent
were trivial, its exchanged partner would also be trivial, contradicting
faithfulness of the whole representation.

An actor outside A₈ exchanges the two summands. Quadraticity then forces the
intersection of the actor with A₈ to fix the left constituent, hence to be
trivial. The actor embeds in the quotient of order two, while the left
constituent injects into the quotient by the actor's fixed space. The bound
on fixed codimension would make this faithful constituent at most two
dimensional. Its at most four vectors cannot support a faithful action of
A₈, whose order is 20160. Therefore the original actor lies in A₈, and its
quadraticity and codimension bound pass to the literal constituent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.25, printed pp.959–960 (PDF pp.976–977), the prerequisites for applying
B.4.2 and B.4.5 to the reducible A₈ restriction. This proves the actor and
faithfulness step; representation classification is a separate input.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U) (K : Subgroup H)
  (d : RestrictionSplit ρ K)

private theorem split_disjoint : Disjoint d.left.toSubmodule d.right.toSubmodule := by
  rw [disjoint_iff]
  change (d.left ⊓ d.right).toSubmodule = ⊥
  rw [d.complementary.inf_eq_bot]
  rfl

private theorem split_sup : d.left.toSubmodule ⊔ d.right.toSubmodule = ⊤ := by
  change (d.left ⊔ d.right).toSubmodule = ⊤
  rw [d.complementary.sup_eq_top]
  rfl

private theorem split_index (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) : K.index = 2 := by
  rw [← K.index_map_equiv eH]
  change (K.map eH.toMonoidHom).index = 2
  rw [hK]
  exact alternatingGroup.index_eq_two

private theorem split_left_faithful [K.Normal] [IsSimpleGroup K]
    (hf : Function.Injective ρ) : Function.Injective d.left.toRepresentation := by
  have hker : d.left.toRepresentation.asGroupHom.ker = ⊥ := by
    rcases (inferInstance : d.left.toRepresentation.asGroupHom.ker.Normal).eq_bot_or_eq_top
      with h | h
    · exact h
    exfalso
    have hl (k : K) (v : d.left.toSubmodule) : ρ k v = v := by
      have hk : d.left.toRepresentation.asGroupHom k = 1 := by
        change k ∈ d.left.toRepresentation.asGroupHom.ker
        rw [h]
        trivial
      have hk' : d.left.toRepresentation k = 1 := congrArg Units.val hk
      exact congrArg (fun f : Module.End (ZMod 2) d.left.toSubmodule => (f v : U)) hk'
    have hr (k : K) (v : U) (hv : v ∈ d.right.toSubmodule) : ρ k v = v := by
      rw [← d.map_left] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hc : d.swapper⁻¹ * k * d.swapper ∈ K :=
        by simpa only [inv_inv] using
          (inferInstance : K.Normal).conj_mem k k.property d.swapper⁻¹
      have he := congrArg (ρ d.swapper) (hl ⟨_, hc⟩ ⟨w, hw⟩)
      simpa only [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul] using he
    have hall (k : K) : ρ k = 1 := by
      ext v
      have hv : v ∈ d.left.toSubmodule ⊔ d.right.toSubmodule := by
        rw [split_sup ρ K d]
        trivial
      obtain ⟨l, hl', r, hr', rfl⟩ := Submodule.mem_sup.mp hv
      simpa only [map_add, Module.End.one_apply] using congrArg₂ (· + ·)
        (hl k ⟨l, hl'⟩) (hr k r hr')
    have hsub : Subsingleton K := ⟨fun k l => Subtype.ext (hf ((hall k).trans (hall l).symm))⟩
    exact not_nontrivial_iff_subsingleton.mpr hsub inferInstance
  intro k l hkl
  exact (d.left.toRepresentation.asGroupHom.ker_eq_bot_iff.mp hker) (Units.ext hkl)

private theorem outside_maps_left (hindex : K.index = 2)
    {a : H} (ha : a ∉ K) {v : U} (hv : v ∈ d.left.toSubmodule) :
    ρ a v ∈ d.right.toSubmodule := by
  have hm : d.swapper⁻¹ * a ∈ K :=
    (K.mul_mem_iff_of_index_two hindex).mpr
      (iff_of_false (by simpa using d.outside) ha)
  have hi := d.left.apply_mem_toSubmodule ⟨_, hm⟩ hv
  have he : ρ d.swapper (ρ (d.swapper⁻¹ * a) v) ∈ d.right.toSubmodule := by
    rw [← d.map_left]
    exact ⟨_, hi, rfl⟩
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using he

private theorem outside_fixed_left_zero (hindex : K.index = 2)
    {a : H} (ha : a ∉ K) {v : U} (hv : v ∈ d.left.toSubmodule)
    (hfix : ρ a v = v) : v = 0 := by
  exact (Submodule.disjoint_def.mp (split_disjoint ρ K d)) v hv
    (hfix ▸ outside_maps_left ρ K d hindex ha hv)

private theorem quadratic_intersection_trivial (hindex : K.index = 2)
    (hl : Function.Injective d.left.toRepresentation)
    (A : Subgroup H) (hq : IsQuadratic ρ A) {a : H} (ha : a ∈ A) (hak : a ∉ K)
    {b : H} (hb : b ∈ A) (hbk : b ∈ K) : b = 1 := by
  have he : d.left.toRepresentation ⟨b, hbk⟩ = 1 := by
    ext v
    apply sub_eq_zero.mp
    exact outside_fixed_left_zero ρ K d hindex hak
      (d.left.toSubmodule.sub_mem (d.left.apply_mem_toSubmodule ⟨b, hbk⟩ v.property)
        v.property) (hq a ha b hb v)
  have := hl (he.trans d.left.toRepresentation.map_one.symm)
  exact congrArg Subtype.val this

private theorem actor_rank_le_one [Finite H] (hindex : K.index = 2)
    (A : Subgroup H) (htriv : ∀ b ∈ A, b ∈ K → b = 1) : rank A ≤ 1 := by
  let : K.Normal := K.normal_of_index_eq_two hindex
  let f : A →* H ⧸ K := (QuotientGroup.mk' K).comp A.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro b hb
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact htriv b b.property ((QuotientGroup.eq_one_iff (b : H)).mp hb)
  have hc := Nat.card_le_card_of_injective f hf
  change Nat.card A ≤ K.index at hc
  have hlog := Nat.log_mono_right (b := 2) (hc.trans_eq hindex)
  exact hlog

private theorem outside_dim_le_codim [FiniteDimensional (ZMod 2) U]
    (hindex : K.index = 2) (A : Subgroup H) {a : H} (ha : a ∈ A) (hak : a ∉ K) :
    Module.finrank (ZMod 2) d.left.toSubmodule ≤ fixedCodim ρ A := by
  let f := (fixedSpace ρ A).mkQ.comp d.left.toSubmodule.subtype
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    have hm : (v : U) ∈ fixedSpace ρ A := (Submodule.Quotient.mk_eq_zero _).mp hv
    exact outside_fixed_left_zero ρ K d hindex hak v.property (hm ⟨a, ha⟩)
  exact LinearMap.finrank_le_finrank_of_injective hf

private theorem marked_card (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) : Nat.card K = 20160 := by
  let e := (eH.subgroupMap K).trans (MulEquiv.subgroupCongr hK)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem faithful_dim_gt_two [FiniteDimensional (ZMod 2) U]
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hl : Function.Injective d.left.toRepresentation) :
    2 < Module.finrank (ZMod 2) d.left.toSubmodule := by
  classical
  let : Finite d.left.toSubmodule := Module.finite_of_finite (ZMod 2)
  by_contra! hn
  have hc : Nat.card d.left.toSubmodule ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hf : Function.Injective (fun k : K =>
      (d.left.toRepresentation k : d.left.toSubmodule → d.left.toSubmodule)) := by
    intro k l hkl
    exact hl (LinearMap.ext (congrFun hkl))
  have hcard := Nat.card_le_card_of_injective _ hf
  rw [Nat.card_fun, marked_card K eH hK] at hcard
  have hp : Nat.card d.left.toSubmodule ^ Nat.card d.left.toSubmodule ≤ 4 ^ 4 :=
    (Nat.pow_le_pow_left hc _).trans (Nat.pow_le_pow_right (by decide) hc)
  omega

/-- The actual left constituent is faithful: the simple component cannot act
trivially on one summand without acting trivially on both. -/
theorem RestrictionSplit.left_faithful
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hf : Function.Injective ρ) : Function.Injective d.left.toRepresentation := by
  let : K.Normal := K.normal_of_index_eq_two (split_index K eH hK)
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K :=
    ((eH.subgroupMap K).trans (MulEquiv.subgroupCongr hK)).isSimpleGroup
  exact split_left_faithful ρ K d hf

include d in
/-- A quadratic actor satisfying the bound of two preserves the two
constituents; in particular, the original actor lies in the marked A₈. -/
theorem RestrictionSplit.actor_le [Finite H] [FiniteDimensional (ZMod 2) U]
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hf : Function.Injective ρ) (A : Subgroup H) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A) : A ≤ K := by
  have hi := split_index K eH hK
  have hl := d.left_faithful ρ K eH hK hf
  intro a ha
  by_contra hak
  have hr := actor_rank_le_one K hi A (fun b hb hk =>
    quadratic_intersection_trivial ρ K d hi hl A hq ha hak hb hk)
  have hd := outside_dim_le_codim ρ K d hi A ha hak
  have hlarge := faithful_dim_gt_two ρ K d eH hK hl
  omega

/-- All actor hypotheses for B.4 on the actual left constituent. The actor
is transported only by the inclusion in K, and its rank is unchanged. -/
theorem RestrictionSplit.actor_prerequisites [Finite H] [FiniteDimensional (ZMod 2) U]
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hf : Function.Injective ρ) (A : Subgroup H) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hb : fixedCodim ρ A ≤ 2 * rank A) :
    A ≤ K ∧ rank (A.subgroupOf K) = rank A ∧
      Function.Injective d.left.toRepresentation ∧
      IsElementaryTwo (A.subgroupOf K) ∧
      IsQuadratic d.left.toRepresentation (A.subgroupOf K) ∧
      fixedCodim d.left.toRepresentation (A.subgroupOf K) ≤ 2 * rank (A.subgroupOf K) := by
  have hAK := d.actor_le ρ K eH hK hf A hq hb
  have hr : rank (A.subgroupOf K) = rank A :=
    congrArg (Nat.log 2) (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv)
  have hm : (A.subgroupOf K).map K.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAK
  have he : IsElementaryTwo (A.subgroupOf K) := by
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAK⟩
    intro hz
    exact hA.1 (by rw [← hm, hz, Subgroup.map_bot])
  have hq' : IsQuadratic d.left.toRepresentation (A.subgroupOf K) := by
    intro a ha b hb v
    exact Subtype.ext (hq a ha b hb v)
  have hfix : fixedSpace (ρ.comp K.subtype) (A.subgroupOf K) = fixedSpace ρ A := by
    ext v
    constructor
    · intro hv a
      exact hv ⟨⟨a, hAK a.property⟩, a.property⟩
    · intro hv a
      exact hv ⟨a, a.property⟩
  have hc := fixedCodim_subrepresentation_le (ρ.comp K.subtype) d.left (A.subgroupOf K)
  have hc' : fixedCodim (ρ.comp K.subtype) (A.subgroupOf K) = fixedCodim ρ A := by
    unfold fixedCodim
    rw [hfix]
  exact ⟨hAK, hr, d.left_faithful ρ K eH hK hf, he, hq', by omega⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
