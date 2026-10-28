module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneFullProfiles
public import Theory.GroupTheory.SmallElementaryCoreOvergroupBound
public import Theory.GroupTheory.ElementaryEightSymmetricThreeSplit

/-!
# Full binary endpoints from the intrinsic b=1 action

The original characteristic-two parabolic is solvable at field order two.
Its small elementary core and the actual local Sylow bound force the intrinsic
actor to equal the whole reduced endpoint. The natural quotient then identifies
an order-four core endpoint with S₄. For an order-eight core, the opposite
omega-center supplies an involution outside the kernel, excluding the nonsplit
extension and yielding C₂ × S₄. No ambient-completion Sylow is used.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.156–157;
the binary cases of (14.13) and (14.15), pp.218–220.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne
open Reduction OriginalExtension NoncommutingProfile
variable {G k W : Type*} [Group G] [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

/-- The binary actor is the entire reduced endpoint. The small-core bound
uses the actual endpoint Sylow, never a Sylow subgroup of the completion. -/
theorem binary_actor_eq_stabilizer
    (h : HypothesisF11 L S) (i : Bool)
    (d : BOneActionData F (base F i) (base F (!i)) k W)
    (ha : d.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    (hcore : Q F (base F i) = Z F (base F i))
    (hneighbor : Q F (base F (!i)) = Z F (base F (!i)))
    (E : letI : Algebra (ZMod 2) k := ZMod.algebra k 2
      W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hk : Nat.card k = 2)
    (hsmall : Nat.card (Q F (base F i)) = 4 ∨ Nat.card (Q F (base F i)) = 8)
    (hcards : Nat.card (Q F (base F (!i))) = Nat.card (Q F (base F i))) :
    d.actor = stabilizer F (base F i) := by
  classical
  let V := stabilizer F (base F i)
  let N := pCore 2 V
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite V := by
    change Finite (MulAction.stabilizer (G₀ L S) (base F i))
    rw [Subgroup.CosetGeometry.stabilizer_base]
    infer_instance
  let : Finite d.actor := Finite.of_injective (inclusion d.actor_le) (inclusion_injective _)
  let : IsElementaryAbelian 2 (Q F (base F i)) := by
    rw [hcore]
    exact Noncommuting.graph_Z_elementary (reduced_triple h) _
  let eN : N ≃* Q F (base F i) := N.equivMapOfInjective V.subtype V.subtype_injective
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.of_injective eN.toMonoidHom eN.injective
  have hNcard : Nat.card N = Nat.card (Q F (base F i)) := Nat.card_congr eN.toEquiv
  have hsol : Group.IsSolvable (parabolic L S (if i then 1 else 0)) := by
    by_contra hn
    have hh := BOneSource.field_gt_two_of_nonsolvable h i d ha hn
    omega
  let := hsol
  have hVle : F i ≤ (parabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S) := by
    cases i
    · exact comap_mono (P₀_le h 0)
    · exact comap_mono (P₀_le h 1)
  have hVle' : V ≤ (parabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S) := by
    simpa only [V,stabilizer,Subgroup.CosetGeometry.stabilizer_base] using hVle
  let f : V →* parabolic L S (if i then 1 else 0) := {
    toFun x := ⟨x.val.val,hVle' x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let : Group.IsSolvable V := Group.isSolvable_of_isSolvable_injective
    (f := f) (by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : parabolic L S (if i then 1 else 0) => (z : G)) he)
  obtain ⟨T,hT⟩ : ∃ T : Sylow 2 V, (T : Subgroup V).map V.subtype =
      Q F (base F (!i)) ⊔ Q F (base F i) :=
    core_product_sylow d (reduced_triple h) hneighbor
  have hcT : Nat.card T = 2 * Nat.card N := by
    have hm : Nat.card T = Nat.card (Q F (base F (!i)) ⊔ Q F (base F i) : Subgroup (G₀ L S)) := by
      have hh : Nat.card ((T : Subgroup V).map V.subtype) = Nat.card T :=
        card_map_of_injective V.subtype_injective
      exact hh.symm.trans (congrArg (fun K : Subgroup (G₀ L S) => Nat.card K) hT)
    have hp : Nat.card (Q F (base F (!i)) ⊔ Q F (base F i) : Subgroup (G₀ L S)) =
        Nat.card (Q F (base F (!i))) * Nat.card k :=
      core_product_card d (reduced_triple h) hcore E
    rw [hm,hp,hk,hcards,←hNcard]
    omega
  have hbound := card_le_six_mul_of_small_elementary_core N
    (hNcard.symm ▸ hsmall) (source_vertex_core_selfCentralizing (reduced_triple h) _) ⟨T,hcT⟩
  have hdcard : Nat.card d.actor = 6 * Nat.card N := by
    have hker : Nat.card d.quotient.ker = Nat.card (Q F (base F i)) := by
      rw [d.kernel]
      exact Nat.card_congr (subgroupOfEquivOfLe d.core_le).toEquiv
    have hquot : Nat.card (d.actor ⧸ d.quotient.ker) = Nat.card SL(2,k) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective d.quotient d.onto).toEquiv
    rw [card_eq_card_quotient_mul_card_subgroup d.quotient.ker,hquot,hker,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hk,←hNcard]
    norm_num
  exact eq_of_le_of_card_ge d.actor_le (by rw [hdcard]; exact hbound)

private def binarySL2Equiv (hk : Nat.card k = 2) : SL(2,k) ≃* Equiv.Perm (Fin 3) := by
  let : Fintype k := Fintype.ofFinite k
  let e := ZMod.ringEquivOfPrime k Nat.prime_two (by simpa only [Nat.card_eq_fintype_card] using hk)
  let f := Matrix.SpecialLinearGroup.map (n := Fin 2) e.symm.toRingHom
  have hf : Function.Injective f := by
    intro a b hab
    ext j l
    exact e.symm.injective (congrArg (fun z : SL(2,ZMod 2) => z.val j l) hab)
  have hc : Nat.card SL(2,k) = Nat.card SL(2,ZMod 2) := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hk]
    simp
  exact (MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hc⟩)).trans
    SLTwoPermThree.sl2Two_equiv_perm_three.some

/-- The opposite elementary core supplies the involution required to exclude
nonsplit elementary-eight extensions of the symmetric group on three letters. -/
theorem actor_involution_outside_core
    (h : HypothesisF11 L S) (i : Bool)
    (d : BOneActionData F (base F i) (base F (!i)) k W) :
    ∃ x : d.actor, (x : G₀ L S) ∉ Q F (base F i) ∧ x^2=1 := by
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 d.imageSylow
  let s : d.imageSylow := e (Multiplicative.ofAdd (1 : k))
  have hs : (s : SL(2,k)) ≠ 1 := by
    intro he
    have hh := congrArg e.symm (show s=1 from Subtype.ext he)
    simp [s] at hh
  have hm : (s : SL(2,k)) ∈ ((Z F (base F (!i))).subgroupOf d.actor).map d.quotient := by
    rw [d.neighbor_image]
    exact s.property
  obtain ⟨x,hx,hxs⟩ := hm
  refine ⟨x,?_,?_⟩
  · intro hxQ
    have hker : x ∈ d.quotient.ker := d.kernel.symm ▸ hxQ
    exact hs (hxs.symm.trans hker)
  · apply Subtype.ext
    exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U (reduced_triple h) _).1 hx)).2.2

/-- Once the actor is the full endpoint, its marked natural quotient and
opposite involution identify both possible binary endpoint groups. -/
theorem binary_endpoint_models
    (h : HypothesisF11 L S) (i : Bool)
    (d : BOneActionData F (base F i) (base F (!i)) k W)
    (he : d.actor = stabilizer F (base F i))
    (hcore : Q F (base F i) = Z F (base F i)) (hk : Nat.card k=2) :
    (Nat.card (Q F (base F i))=4 →
      Nonempty (stabilizer F (base F i) ≃* Equiv.Perm (Fin 4))) ∧
    (Nat.card (Q F (base F i))=8 →
      Nonempty (stabilizer F (base F i) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) := by
  let V := stabilizer F (base F i)
  let N := pCore 2 V
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite V := by
    change Finite (MulAction.stabilizer (G₀ L S) (base F i))
    rw [Subgroup.CosetGeometry.stabilizer_base]
    infer_instance
  let : IsElementaryAbelian 2 (Q F (base F i)) := by
    rw [hcore]
    exact Noncommuting.graph_Z_elementary (reduced_triple h) _
  let eN : N ≃* Q F (base F i) := N.equivMapOfInjective V.subtype V.subtype_injective
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.of_injective eN.toMonoidHom eN.injective
  have hNcard : Nat.card N = Nat.card (Q F (base F i)) := Nat.card_congr eN.toEquiv
  let a : V ≃* d.actor := (MulEquiv.subgroupCongr he).symm
  let e := binarySL2Equiv hk
  let f : V →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (d.quotient.comp a.toMonoidHom)
  have hf : Function.Surjective f := e.surjective.comp (d.onto.comp a.surjective)
  have hker : f.ker = N := by
    ext x
    change e (d.quotient (a x))=1 ↔ x∈N
    rw [e.map_eq_one_iff,←MonoidHom.mem_ker,d.kernel]
    change (x : G₀ L S)∈N.map V.subtype ↔ x∈N
    exact mem_map_iff_mem V.subtype_injective
  have hself : centralizer (N : Set V) ≤ N := source_vertex_core_selfCentralizing (reduced_triple h) _
  constructor
  · intro hc
    apply mulEquiv_perm_four_of_selfCentralizing_four_card_twentyfour N (hNcard.trans hc) hself
    have hquot : Nat.card (V ⧸ f.ker)=6 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,hquot,hker,hNcard,hc]
  · intro hc
    obtain ⟨x,hx,hx2⟩ := actor_involution_outside_core h i d
    let y : V := a.symm x
    have hy : y^2=1 := by rw [←map_pow,hx2,map_one]
    have hyn : f y ≠ 1 := by
      intro hy
      have hyN : y∈N := hker ▸ (show y∈f.ker from hy)
      have hyQ : (y : G₀ L S)∈Q F (base F i) := mem_map_of_mem V.subtype hyN
      exact hx hyQ
    apply c2_symmetric_four_of_elementary_eight_s3_involution f hf
      (hker.symm ▸ inferInstance) (hker.symm ▸ hNcard.trans hc)
      (hker.symm ▸ hself) y hy hyn

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne
