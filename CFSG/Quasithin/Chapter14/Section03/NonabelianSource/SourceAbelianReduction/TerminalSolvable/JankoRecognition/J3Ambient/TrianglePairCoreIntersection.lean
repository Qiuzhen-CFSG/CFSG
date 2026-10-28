module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.OverlapPair
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.BaumeisterParabolics
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# The actual pair-centralizer intersection with the involution core

Involution fusion transports the full generalized Fitting core and its A₅
quotient to the literal field involution. The actual pair centralizer is
S₃ × C₂, so its normal two-subgroup in that core is the central involution
line. Both the subgroup and the involution retain the original field embedding.
No local complement or triangle recognition is assumed.

Source: Baumeister, A geometry for groups of J₃-type (2007), Lemma 2.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

variable {G : Type*} [Group G] [Finite G]

/-- The actual full intrinsic and ambient cores, and the full core quotient,
at any involution in the original single-class source. -/
theorem literal_involution_core_and_quotient
    {D : Seed G} (hc : Janko23.OneInvolutionClass G) (f : G) (hf : orderOf f = 2) :
    Nonempty (Janko23.localCore f ≃* MinusExtraspecial.Model) ∧
    Nonempty (Janko23.ambientCore f ≃* MinusExtraspecial.Model) ∧
    Nonempty ((Janko23.involutionCentralizer f ⧸ Janko23.localCore f) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hc.isConj D.localType.involution hf)
  let a := MulAut.conj g
  have haf : a f = D.z := hg
  let c : Janko23.involutionCentralizer f ≃* Janko23.involutionCentralizer D.z :=
    (CentralizerSmallKernelTransport.centralizerEquiv a f).trans
      (MulEquiv.subgroupCongr (by rw [haf]))
  have he : (Janko23.localCore f).map c.toMonoidHom = Janko23.localCore D.z :=
    map_generalizedFitting_equiv c
  let e0 : Janko23.localCore f ≃* MinusExtraspecial.Model :=
    (((Janko23.localCore f).equivMapOfInjective c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr he)).trans D.localType.core_equiv.some
  let e1 : Janko23.localCore f ≃* Janko23.ambientCore f :=
    (Janko23.localCore f).equivMapOfInjective _
      (Janko23.involutionCentralizer f).subtype_injective
  exact ⟨⟨e0⟩, ⟨e1.symm.trans e0⟩,
    ⟨(QuotientGroup.congr _ _ c he).trans D.localType.quotient_equiv.some⟩⟩

private theorem normal_two_product {H : Type*} [Group H] [Finite H]
    (e : H ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))
    (I : Subgroup H) [I.Normal] (hI : IsPGroup 2 I)
    (z : H) (hzI : z ∈ I) (hz : orderOf z = 2) : I = zpowers z := by
  let f : H →* Equiv.Perm (Fin 3) := (MonoidHom.fst _ _).comp e.toMonoidHom
  have hf : Function.Surjective f := Prod.fst_surjective.comp e.surjective
  have hcore : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three
      (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id (by
        simp only [MonoidHom.ker_id]
        exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using hh.symm
  have hmap : I.map f = ⊥ := by
    have hn : (I.map f).Normal := Normal.map inferInstance f hf
    have hh : I.map f ≤ pCore 2 (Equiv.Perm (Fin 3)) := le_sSup ⟨hn, hI.map f⟩
    rw [hcore] at hh
    exact eq_bot_iff.mpr hh
  have hfst (x : I) : (e (x : H)).1 = 1 := by
    have hh : f (x : H) ∈ I.map f := mem_map_of_mem f x.property
    rwa [hmap, mem_bot] at hh
  let t : I → Multiplicative (ZMod 2) := fun x => (e (x : H)).2
  have ht : Function.Injective t := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact Prod.ext ((hfst x).trans (hfst y).symm) hxy
  have hIc : Nat.card I ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      using Nat.card_le_card_of_injective t ht
  apply (eq_of_le_of_card_ge (zpowers_le.mpr hzI) ?_).symm
  rw [Nat.card_zpowers, hz]
  exact hIc

/-- The pair centralizer meets the full involution core in the same literal
involution line used by the point centralizer. -/
theorem literal_triangle_pair_core_intersection
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    (normalizer (overlap j : Set G) ⊓
      centralizer ({j SingerField.fieldElement} : Set G)) ⊓
      Janko23.ambientCore (j SingerField.fieldElement) =
        zpowers (j SingerField.fieldElement) := by
  let f := j SingerField.fieldElement
  let H := Janko23.involutionCentralizer f
  let Y := normalizer (overlap j : Set G) ⊓ H
  let Q := Janko23.ambientCore f
  have hf : orderOf f = 2 := image_involution_order j hj.1
  obtain ⟨_, ⟨eQ⟩, _⟩ := literal_involution_core_and_quotient (D := D) hc f hf
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 5)
    ((Nat.card_congr eQ.toEquiv).trans MinusExtraspecial.card_model)
  obtain ⟨eP⟩ := literal_overlap_pair_equiv P hc A C a j hj
  let eY : Y ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) :=
    Janko23.J3Recognition.Ambient.BaumeisterParabolics.pair_centralizer_equiv j hj.1 eP
  let I := Q.subgroupOf Y
  have hQH : Q ≤ H := Janko23.ambientCore_le f
  have hYH : Y ≤ H := inf_le_right
  have hQN : (Q.subgroupOf H).Normal := by
    rw [Janko23.ambientCore_subgroupOf]
    infer_instance
  let : I.Normal := normal_subgroupOf_of_le_normalizer
    (hYH.trans ((normal_subgroupOf_iff_le_normalizer hQH).mp hQN))
  have hI : IsPGroup 2 I := hQ.comap_of_injective Y.subtype Y.subtype_injective
  have hfY : f ∈ Y :=
    ⟨(overlap j).le_normalizer (image_involution_mem j),
      mem_centralizer_singleton_iff.mpr rfl⟩
  let fY : Y := ⟨f, hfY⟩
  have hfI : fY ∈ I := Janko23.HTypeAt.involution_mem_core
  have hfYo : orderOf fY = 2 := (orderOf_coe fY).symm.trans hf
  have hIeq := normal_two_product eY I hI fY hfI hfYo
  have hm := congrArg (Subgroup.map Y.subtype) hIeq
  rw [subgroupOf_map_subtype, MonoidHom.map_zpowers] at hm
  change Y ⊓ Q = zpowers f
  exact (inf_comm Y Q).trans hm

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
