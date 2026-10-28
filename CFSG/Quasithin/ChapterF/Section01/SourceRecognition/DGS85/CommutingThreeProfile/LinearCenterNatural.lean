module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CenterCommutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Neighborhood
public import Theory.Representation.SL2.NaturalConjugateQuotient
public import Theory.GroupTheory.Commutator.RelativeGeneration

public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Natural coordinates on the linear center with its prescribed marking

The neighboring center Z_y is a fixed Sylow seed in Z_m. The actual
common-Sylow product and [V_y,Q_y] ≤ Z_y bound all Sylow displacements
by that seed. Minimality of Z_m makes its conjugates generate the whole
center. The orders q and q² make the seed proper, so small-seed recognition
constructs natural coordinates for the given original SL₂(k) marking.

The second theorem constructs the existing HasNaturalCenter input, including
its exact two-core kernel. A finite field transport handles its universe
convention; it imposes no relation between the ambient and field universes.
The marked coordinate theorem itself retains the original field and marking.
SuzukiMarkedLayers consumes both results at the literal source quotient.
The earlier minimality, common-Sylow, order and commutator inputs remain.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), printed p.178; (12.9)(c4), printed p.186, and its proof on p.188.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
local instance linearCenterNaturalBinaryAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem source_linear_center_seed
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    let F := reducedFamily L S
    let A := star L S i
    let Zm := Z F (base F i)
    let Zy := Z F (base F (!i))
    Zm ≤ A ∧ A ≤ normalizer (Zm : Set (G₀ L S)) ∧
      Zm = conjugateSpanBy Zy A ∧ Zm ≠ Zy ∧
      ⁅Zm,A.pCoreIn 2⁆ ≤ ⊥ ∧
      ⁅Zm,(T : Subgroup A).map A.subtype⁆ ≤ Zy ∧
      ⁅Zy,(T : Subgroup A).map A.subtype⁆ ≤ ⊥ := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let Zm := Z F m
  let Zy := Z F y
  let J := conjugateSpanBy Zy A
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  let : Finite Zm := Finite.of_injective (inclusion (Z_le_stabilizer F m)) (inclusion_injective _)
  let : IsElementaryAbelian 2 Zm := Z_elementary F (fun v => (source_Z_Q_U (reduced_triple h) v).1) m
  have hQA : Q F m ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hZA : Zm ≤ A := ((source_Z_Q_U (reduced_triple h) m).1.trans (map_subtype_le _)).trans hQA
  have hAZ : A ≤ normalizer (Zm : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F m)).mp (Z_normal F m))
  have hJZ : J ≤ Zm := conjugateSpanBy_le hzy hAZ
  have hJA : A ≤ normalizer (J : Set (G₀ L S)) := le_normalizer_conjugateSpanBy Zy A
  have hspan : Zm = J := by
    let : (J.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hJA
    rcases hmin (J.subgroupOf A) inferInstance (subgroupOf_mono A hJZ) with hz | ht
    · have hJzero : J = ⊥ := by
        have hh := congrArg (Subgroup.map A.subtype) hz
        simpa only [map_subgroupOf_eq_of_le (hJZ.trans hZA),Subgroup.map_bot] using hh
      have hYzero : Zy = ⊥ := bot_unique (hJzero ▸ le_conjugateSpanBy Zy A)
      have hh : Nat.card Zy = Nat.card k := hcardy
      rw [hYzero,Nat.card_unique] at hh
      have : 1 < Nat.card k := Finite.one_lt_card
      omega
    · have hh := congrArg (Subgroup.map A.subtype) ht
      change (J.subgroupOf A).map A.subtype = (Zm.subgroupOf A).map A.subtype at hh
      rw [map_subgroupOf_eq_of_le (hJZ.trans hZA),map_subgroupOf_eq_of_le hZA] at hh
      exact hh.symm
  have hneq : Zm ≠ Zy := by
    intro he
    have hh : Nat.card Zm = Nat.card Zy := congrArg (fun P : Subgroup (G₀ L S) => Nat.card P) he
    rw [hcard,hcardy] at hh
    have : 1 < Nat.card k := Finite.one_lt_card
    nlinarith
  have hZQ : Zm ≤ centralizer (Q F m : Set (G₀ L S)) :=
    Z_centralizes_Q F m (source_Z_Q_U (reduced_triple h) m).1
  have hcore : ⁅Zm,A.pCoreIn 2⁆ ≤ ⊥ := by
    rw [star_core h i]
    exact (commutator_eq_bot_iff_le_centralizer.mpr hZQ).le
  have hcentral : (Q F y ⊔ Q F m) ≤ centralizer (Zy : Set (G₀ L S)) :=
    sup_le (le_centralizer_iff.mp (Z_centralizes_Q F y (source_Z_Q_U (reduced_triple h) y).1))
      (le_centralizer_iff.mp (hzy.trans hZQ))
  have hfix : ⁅Zy,(T : Subgroup A).map A.subtype⁆ ≤ ⊥ := by
    rw [hT,commutator_comm]
    exact (commutator_eq_bot_iff_le_centralizer.mpr hcentral).le
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hmove : ⁅Zm,(T : Subgroup A).map A.subtype⁆ ≤ Zy := by
    rw [hT,commutator_comm]
    apply commutator_sup_le_of_relative_normal (Q F y ⊔ Q F m) (Q F y) (Q F m) Zm Zy
    · exact hcentral.trans (Subgroup.centralizer_le_normalizer _)
    · exact le_sup_left
    · exact le_sup_right
    · rw [commutator_comm]
      exact (commutator_mono (Z_neighbor_le_V F hadj.symm) le_rfl).trans hcommy
    · rw [commutator_comm]
      exact (commutator_eq_bot_iff_le_centralizer.mpr hZQ).le.trans bot_le
  exact ⟨hZA,hAZ,hspan,hneq,hcore,hmove,hfix⟩

/-- The original quotient marking gives actual natural coordinates on the center. -/
theorem source_linear_center_marked_natural
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    let F := reducedFamily L S
    let A := star L S i
    let π := e.toMonoidHom.comp ((originalQuotient h i).symm.toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 A)))
    Nonempty (BinaryConjugationSection A (Z F (base F i)) ⊥
      ((SL2NaturalOffenders.NoStrong.natural (F := k)).comp π)) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let Zm := Z F m
  let Zy := Z F y
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  let : Finite Zm := Finite.of_injective (inclusion (Z_le_stabilizer F m)) (inclusion_injective _)
  let : IsElementaryAbelian 2 Zm := Z_elementary F (fun v => (source_Z_Q_U (reduced_triple h) v).1) m
  obtain ⟨hZA,hAZ,hspan,hneq,hcore,hmove,hfix⟩ :=
    source_linear_center_seed h i T hT e hcard hcardy hzy hcommy hmin
  let eA := (originalQuotient h i).symm.trans e
  obtain ⟨_,E,hE⟩ := SL2.natural_conjugate_quotient A Zm ⊥ Zy hAZ
    (le_normalizer_of_normal) bot_le hzy hspan hneq hcore T eA hmove hfix
    (by rw [relIndex_bot_left]; exact hcardy.le)
  let H : Subgroup (G₀ L S) := ⊥
  let f : Zm →* Multiplicative (Fin 2 → k) := {
    toFun z := Multiplicative.ofAdd (E (Additive.ofMul (QuotientGroup.mk z)))
    map_one' := by exact E.map_zero
    map_mul' z w := by
      change E (Additive.ofMul (QuotientGroup.mk (z*w))) = _
      rw [QuotientGroup.mk_mul]
      exact E.map_add _ _ }
  refine ⟨{
    section_le := hZA
    kernel_le := bot_le
    normalized := hAZ
    coordinates := f
    onto := ?_
    kernel_eq := ?_
    equivariant := ?_ }⟩
  · intro v
    obtain ⟨w,hw⟩ := E.surjective v.toAdd
    obtain ⟨z,hz⟩ := QuotientGroup.mk'_surjective (H.subgroupOf Zm) w.toMul
    refine ⟨z,?_⟩
    change E (Additive.ofMul (QuotientGroup.mk z)) = v.toAdd
    change (QuotientGroup.mk z : Zm ⧸ (⊥ : Subgroup (G₀ L S)).subgroupOf Zm) = w.toMul at hz
    rw [hz]
    exact hw
  · ext z
    change E (Additive.ofMul (QuotientGroup.mk z)) = 0 ↔ z ∈ H.subgroupOf Zm
    rw [E.map_eq_zero_iff]
    exact QuotientGroup.eq_one_iff z
  · intro a z
    exact hE a z
/-- Construct the retained natural-center input from the preceding source geometry. -/
theorem source_linear_hasNaturalCenter
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hz : center (star L S i) = ⊥) :
    Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)) := by
  let F := reducedFamily L S
  let m := base F i
  let A := star L S i
  let : Fintype k := Fintype.ofFinite k
  let : Small.{u} k := small_of_injective (Fintype.equivFin k).injective
  let κ := Shrink.{u} k
  let eκ : κ ≃+* k := Shrink.ringEquiv.{u} k
  let : Finite κ := Finite.of_injective eκ eκ.injective
  let : CharP κ 2 := eκ.toRingHom.charP eκ.injective 2
  let : Algebra (ZMod 2) κ := ZMod.algebra κ 2
  have hκ : Nat.card κ = Nat.card k := Nat.card_congr eκ.toEquiv
  let e' := e.trans (Atlas.fieldEquivSL 2 eκ.symm)
  obtain ⟨d⟩ := source_linear_center_marked_natural h i T hT e'
    (hcard.trans (by rw [hκ])) (hcardy.trans hκ.symm) hzy hcommy hmin
  let π := e'.toMonoidHom.comp ((originalQuotient h i).symm.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A)))
  have hπ : Function.Surjective π := e'.surjective.comp
    ((originalQuotient h i).symm.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : π.ker = (Q F m).subgroupOf A := by
    have hh : π.ker = pCore 2 A := by
      ext a
      change e' ((originalQuotient h i).symm (QuotientGroup.mk a)) = 1 ↔ _
      rw [e'.map_eq_one_iff,(originalQuotient h i).symm.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff a
    rw [hh]
    change pCore 2 A = (Q (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf A
    rw [←star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hω : Stellmacher.omegaOneCenterAmbient A = ⊥ := by
    apply bot_unique
    intro z hz'
    obtain ⟨hzA,_,hzc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz'
    have hm : (⟨z,hzA⟩ : A) ∈ center A := mem_center_iff.mpr (fun a => Subtype.ext (hzc a a.property))
    rw [hz,mem_bot] at hm
    exact congrArg Subtype.val hm
  exact ⟨κ,inferInstance,inferInstance,inferInstance,π,hπ,hker,hω.symm ▸ ⟨d⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
