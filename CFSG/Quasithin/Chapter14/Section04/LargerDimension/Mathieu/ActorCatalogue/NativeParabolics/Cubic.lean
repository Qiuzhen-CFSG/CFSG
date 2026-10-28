module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Transport
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# The cubic residual actor in the native Mathieu extension

The normal triple-cover component has index two. Consequently every normal
three-subgroup lies in that component, and quasisimplicity puts it in the
component's center. The published scalar has order three, so it generates
exactly the ambient three-core. Its two-residual is itself and its two-core
is trivial, proving all four conditions of the source X-family.

The explicit outer involution inverts the scalar. This identifies the scalar
centralizer with the component and the component centralizer with the cubic
subgroup. The scalar acts without nonzero fixed vectors, so the cubic subgroup
meets every nonzero binary point centralizer trivially. In particular the
literal Borel residual is distinct from the first actor.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012, with
14.4.2(6), printed p.1006, and H.12.1, printed pp.393--394. The remaining
parabolic actors and their catalogue are separate calculations. All matrices
and source attribution are inherited from ActorCatalogue.Native.
-/

@[expose] public section
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
noncomputable def componentEquiv : component ≃* M22TripleCover :=
  subgroupOfEquivOfLe derivedGroup_le_actionGroup

def cubicScalar : Model := componentInclusion M22TripleCover.scalar

def cubic : Subgroup Model := (center component).map component.subtype

instance cubic_normal : cubic.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  exact (show (⊤ : Subgroup Model) ≤ normalizer (component : Set Model) by
    rw [normalizer_eq_top]).trans
      (normalizer_le_normalizer_characteristic_image component (center component))

theorem cubic_eq_map_center : cubic = (center M22TripleCover).map componentInclusion := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x.val.val, x.property⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact congrArg (fun a : component => a.val.val)
      (mem_center_iff.mp hx ⟨componentInclusion y, y.property⟩)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨componentInclusion x, x.property⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : M22TripleCover => (z : Matrix12ˣ))
      (mem_center_iff.mp hx (⟨y.val.val, y.property⟩ : M22TripleCover))

theorem cubic_eq_zpowers : cubic = zpowers cubicScalar := by
  rw [cubic_eq_map_center, M22TripleCover.center_eq_zpowers, MonoidHom.map_zpowers]
  rfl

theorem cubic_card : Nat.card cubic = 3 := by
  rw [cubic_eq_map_center, card_map_of_injective
    (show Function.Injective componentInclusion from
      inclusion_injective derivedGroup_le_actionGroup), M22TripleCover.center_card]

theorem cubic_isPGroup : IsPGroup 3 cubic := IsPGroup.of_card (n := 1) (by simpa using cubic_card)

theorem cubic_le_component : cubic ≤ component := by
  exact (map_le_range component.subtype (center component)).trans_eq (range_subtype _)

theorem threeCore_le_component : pCore 3 Model ≤ component := by
  let q := QuotientGroup.mk' component
  have hp : IsPGroup 2 (Model ⧸ component) := IsPGroup.of_card (n := 1)
    (by simpa only [pow_one, ← index_eq_card] using component_index)
  have hd := IsPGroup.disjoint_of_ne 3 2 (by decide)
    ((pCore 3 Model).map q) ⊤ (pCore_isPGroup.map q) (hp.to_subgroup ⊤)
  have hb : (pCore 3 Model).map q = ⊥ := by simpa using hd.eq_bot
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb

theorem threeCore_eq_cubic : pCore 3 Model = cubic := by
  apply le_antisymm
  · let : Theory.GroupTheory.IsQuasisimple component :=
      Theory.GroupTheory.IsQuasisimple.of_mulEquiv componentEquiv.symm
    have hcore : (pCore 3 Model).subgroupOf component ≤ pCore 3 component :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    intro x hx
    exact mem_map.mpr ⟨⟨x, threeCore_le_component hx⟩,
      Theory.GroupTheory.IsQuasisimple.pCore_le_center 3 (hcore hx), rfl⟩
  · exact le_sSup ⟨inferInstance, cubic_isPGroup⟩

theorem cubic_twoCore : twoCore cubic = ⊥ := by
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 cubic) ⊤
    pCore_isPGroup (cubic_isPGroup.to_subgroup ⊤)
  have he : pCore 2 cubic = ⊥ := by simpa using hd.eq_bot
  simp only [twoCore, he, Subgroup.map_bot]

theorem cubic_twoResidual : twoResidual cubic = cubic := by
  have he : pResidual 2 cubic = ⊤ := by
    apply (pResidual_eq_top_iff 2 cubic).mpr
    intro N hN hp
    let := hN
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide)
      (⊤ : Subgroup (cubic ⧸ N)) ⊤ (hp.to_subgroup ⊤)
        ((cubic_isPGroup.to_quotient N).to_subgroup ⊤)
    have hq : Subsingleton (cubic ⧸ N) := by
      apply subsingleton_of_forall_eq 1
      intro x
      have he : (⊤ : Subgroup (cubic ⧸ N)) = ⊥ := by simpa using hd.eq_bot
      exact (show x ∈ (⊥ : Subgroup (cubic ⧸ N)) from he ▸ mem_top x)
    exact index_eq_one.mp (by rw [index_eq_card]; exact Nat.card_eq_one_iff_unique.mpr ⟨hq, inferInstance⟩)
  simp only [twoResidual, he, ← MonoidHom.range_eq_map, range_subtype]

theorem firstActor_eq_cubic : twoResidual (pCore 3 Model) = cubic := by
  rw [threeCore_eq_cubic, cubic_twoResidual]

theorem firstActor_threeExtension (S : Sylow 2 Model) :
    ThreeExtension ⊤ (S : Subgroup Model) (twoResidual (pCore 3 Model)) := by
  rw [firstActor_eq_cubic]
  refine ⟨le_top, ?_, cubic_twoResidual, ?_⟩
  · rw [normalizer_eq_top]
    exact le_top
  · rw [cubic_twoCore, relIndex_bot_left, cubic_card]

theorem cubicScalar_not_mem_pointCentralizer {v : Space} (hv : v ≠ 0) :
    cubicScalar ∉ pointCentralizer v := by
  intro h
  apply hv
  exact (M22TripleCover.scalar_fixed_iff v).mp h

theorem firstActor_not_le_pointCentralizer {v : Space} (hv : v ≠ 0) :
    ¬ twoResidual (pCore 3 Model) ≤ pointCentralizer v := by
  rw [firstActor_eq_cubic, cubic_eq_zpowers]
  intro h
  exact cubicScalar_not_mem_pointCentralizer hv (h (mem_zpowers _))


theorem cubicScalar_mem_cubic : cubicScalar ∈ cubic := by
  rw [cubic_eq_zpowers]
  exact mem_zpowers _

theorem cubic_le_centralizer_component : cubic ≤ centralizer (component : Set Model) := by
  rintro g ⟨x, hx, rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)

theorem component_le_centralizer_scalar : component ≤ centralizer ({cubicScalar} : Set Model) := by
  intro g hg z hz
  have he : z = cubicScalar := hz
  subst z
  exact (cubic_le_centralizer_component cubicScalar_mem_cubic g hg).symm

theorem outer_conj_scalar : outerInvolution * cubicScalar * outerInvolution⁻¹ = cubicScalar ^ 2 :=
  Subtype.ext unitC_conj_scalarUnit

theorem scalar_sq_ne_self : cubicScalar ^ 2 ≠ cubicScalar := by
  intro h
  have he : cubicScalar = 1 := by
    apply mul_left_cancel (a := cubicScalar)
    simpa only [pow_two, mul_one] using h
  apply coreScalar_ne_one
  exact (inclusion_injective derivedGroup_le_actionGroup)
    (show componentInclusion M22TripleCover.scalar = componentInclusion 1 from he)

theorem outer_not_mem_centralizer_scalar : outerInvolution ∉ centralizer ({cubicScalar} : Set Model) := by
  intro h
  have hc := h cubicScalar (Set.mem_singleton _)
  have he : outerInvolution * cubicScalar * outerInvolution⁻¹ = cubicScalar := by
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  exact scalar_sq_ne_self (outer_conj_scalar.symm.trans he)

theorem centralizer_scalar_eq_component : centralizer ({cubicScalar} : Set Model) = component := by
  apply le_antisymm ?_ component_le_centralizer_scalar
  by_contra h
  have ht := eq_top_of_component_lt _
    (lt_of_le_of_ne component_le_centralizer_scalar (by
      intro he
      exact h (le_of_eq he.symm)))
  exact outer_not_mem_centralizer_scalar (ht ▸ mem_top _)

theorem centralizer_component_eq_cubic : centralizer (component : Set Model) = cubic := by
  apply le_antisymm ?_ cubic_le_centralizer_component
  intro g hg
  have hgc : g ∈ component := by
    rw [← centralizer_scalar_eq_component]
    exact centralizer_le (Set.singleton_subset_iff.mpr
      (cubic_le_component cubicScalar_mem_cubic)) hg
  exact mem_map.mpr ⟨⟨g, hgc⟩, mem_center_iff.mpr (fun x =>
    Subtype.ext (hg x.val x.property)), rfl⟩

theorem cubic_disjoint_pointCentralizer {v : Space} (hv : v ≠ 0) :
    Disjoint cubic (pointCentralizer v) := by
  let : Fact (Nat.card cubic).Prime := ⟨cubic_card ▸ Nat.prime_three⟩
  rcases ((pointCentralizer v).subgroupOf cubic).eq_bot_or_eq_top_of_prime_card with hb | ht
  · rw [disjoint_iff, inf_comm, ← subgroupOf_map_subtype, hb, Subgroup.map_bot]
  · have hle : cubic ≤ pointCentralizer v := subgroupOf_eq_top.mp ht
    exact (cubicScalar_not_mem_pointCentralizer hv (hle cubicScalar_mem_cubic)).elim

theorem borelResidual_le_pointCentralizer (B : Subgroup Model) {v : Space}
    (hB : B ≤ pointCentralizer v) : twoResidual B ≤ pointCentralizer v :=
  (map_le_range B.subtype (pResidual 2 B)).trans ((range_subtype B).le.trans hB)

theorem firstActor_ne_borelResidual (B : Subgroup Model) {v : Space}
    (hv : v ≠ 0) (hB : B ≤ pointCentralizer v) :
    twoResidual (pCore 3 Model) ≠ twoResidual B := by
  intro h
  exact firstActor_not_le_pointCentralizer hv (h ▸ borelResidual_le_pointCentralizer B hB)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
