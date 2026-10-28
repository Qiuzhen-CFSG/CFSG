module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Normalization of binary components in E.6.8

Both binary linear groups contain an actual copy of A₆: use A₆ ≤ A₈,
PSL₄(2) ≃ A₈, and the block-diagonal inclusion GL₄(2) ≤ GL₅(2).
If a component were moved by an element of its containing group, its
conjugate would commute with it. The two embedded A₆ subgroups contradict
quasithinness via the elementary-nine times alternating-four local witness.
Thus the whole centralizer of U normalizes L, in particular Q does.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), the invocation of 1.2.1(3).
The exceptional equivalence is the attributed ATLAS port imported above.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
open CFSG.Quasithin CFSG.Quasithin.ChapterE.Section06
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry

/-- An actual comparison with the linear automorphisms of the binary natural space. -/
noncomputable def binaryEquiv {X : Type*} [Group X] {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL X n 2) : X ≃* LinearGroup n := Classical.choice <| by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hm
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨e₀.trans ((Atlas.fieldEquivPSL n f.symm).trans (projectiveEquivLinear hn))⟩

private def a6Sum : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6 ⊕ Fin 2) :=
  ((Equiv.Perm.sumCongrHom (Fin 6) (Fin 2)).comp
    ((alternatingGroup (Fin 6)).subtype.prod (1 : alternatingGroup (Fin 6) →* Equiv.Perm (Fin 2)))).codRestrict _
      (by
        intro a
        change Equiv.Perm.sign (Equiv.sumCongr (a : Equiv.Perm (Fin 6)) 1) = 1
        rw [Equiv.Perm.sign_sumCongr, Equiv.Perm.mem_alternatingGroup.mp a.property,
          map_one, mul_one])

private def a6To8 : alternatingGroup (Fin 6) →* alternatingGroup (Fin 8) :=
  (Equiv.altCongrHom finSumFinEquiv).toMonoidHom.comp a6Sum

private theorem a6To8_injective : Function.Injective a6To8 := by
  intro a b h
  have he := (Equiv.altCongrHom finSumFinEquiv).injective h
  have hp := Equiv.Perm.sumCongrHom_injective (congrArg Subtype.val he)
  exact Subtype.ext (congrArg Prod.fst hp)

private noncomputable def splitFive : Space 5 ≃ₗ[ZMod 2] ZMod 2 × Space 4 :=
  (LinearEquiv.piCongrLeft (ZMod 2) (fun _ => ZMod 2) (finSuccEquiv 4)).trans
    (LinearEquiv.piOptionEquivProd (ZMod 2))

private noncomputable def fourToFive : LinearGroup 4 →* LinearGroup 5 where
  toFun g := splitFive.trans ((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr g) |>.trans splitFive.symm
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

private theorem fourToFive_injective : Function.Injective fourToFive := by
  intro a b h
  apply LinearEquiv.ext
  intro v
  have he := congrArg (fun g : LinearGroup 5 => (splitFive (g (splitFive.symm (0, v)))).2) h
  simpa [fourToFive] using he

private theorem exists_a6_embedding {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ∃ f : alternatingGroup (Fin 6) →* LinearGroup n, Function.Injective f := by
  let e := Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans (projectiveEquivLinear (by decide : 0 < 4))
  let f := e.toMonoidHom.comp a6To8
  have hf : Function.Injective f := e.injective.comp a6To8_injective
  rcases hn with rfl | rfl
  · exact ⟨f, hf⟩
  · exact ⟨fourToFive.comp f, fourToFive_injective.comp hf⟩

variable {G : Type*} [Group G] [Finite G]

private theorem normal_of_component_contains_a6 (hG : IsQuasithin G)
    {L : Subgroup G} (hL : IsComponent G L)
    (f : alternatingGroup (Fin 6) →* L) (hf : Function.Injective f) : L.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra he
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (hL.commutator_eq_bot_of_ne (hL.map_conj g) (Ne.symm he))
  let j := L.subtype.comp f
  have hj : Function.Injective j := L.subtype_injective.comp hf
  let A := j.range
  have hAL : A ≤ L := by rintro _ ⟨x, rfl⟩; exact (f x).property
  have hAC : A ≤ centralizer ((A.map (MulAut.conj g).toMonoidHom) : Set G) :=
    hAL.trans (hc.trans (centralizer_le (map_mono hAL)))
  exact alternatingGroup.not_commuting_a6_of_quasithin hG A
    (A.map (MulAut.conj g).toMonoidHom) (MonoidHom.ofInjective hj).symm
    (((MulAut.conj g).subgroupMap A).symm.trans (MonoidHom.ofInjective hj).symm) hAC

/-- Binary four- and five-dimensional components are normalized by the source Q. -/
theorem binary_component_normalizer {K : GroupClass} {T : Sylow 2 G}
    {M V U Q L : Subgroup G} (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL L n 2) :
    Q ≤ normalizer (L : Set G) := by
  let H := centralizer (U : Set G)
  let e := (subgroupOfEquivOfLe hL.1).trans (binaryEquiv (by omega) hm)
  obtain ⟨f, hf⟩ := exists_a6_embedding hn
  have hnormal := normal_of_component_contains_a6 (h.simpleQTKE.quasithin.subgroup H)
    hL.2 (e.symm.toMonoidHom.comp f) (e.symm.injective.comp hf)
  have hnH : H ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hL.1).mp hnormal
  apply le_trans _ hnH
  rw [hQ]
  exact inf_le_right.trans (centralizer_le hU.1)

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
