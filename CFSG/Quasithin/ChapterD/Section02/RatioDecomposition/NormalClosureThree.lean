module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SeededThreeCore
public import Theory.Representation.BinaryOffender.NormalClosure

/-!
# Normal-closure reduction for a non-quintic original actor

A rank-one starred actor that centralizes the ambient five-core retains
its exact starred family on its normal closure. The closure has no intrinsic
five-core commutator, even if other ambient stars do. The original
Sylow-fixed generating seed then gives a globally fixed three-core
complement, so its literal moved action is faithful, fully Fitting-moved,
and admits the D.2.16 factor decomposition.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed p.1084,
and D.2.25--29, printed pp.190--192.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD
open CyclicSource RatioDecomposition
variable {G V : Type*} [Group G] [Finite G] [Group.IsSolvable G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] [Group.IsSolvable G] in
theorem normalClosure_starred_generated {A : Subgroup G} (hA : A ∈ QhatStar ρ) :
    Jhat (ρ.comp (normalClosure (A : Set G)).subtype) = ⊤ := by
  let N := normalClosure (A : Set G)
  have hAN : A ≤ N := le_normalClosure
  have ht := subgroup_starred_transport ρ N ⟨A,hA,hAN⟩
  apply Subgroup.map_injective N.subtype_injective
  rw [←MonoidHom.range_eq_map,range_subtype]
  apply le_antisymm (map_subtype_le _)
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g,rfl⟩ := isConj_iff.mp hax
  let B := A.map (MulAut.conj g).toMonoidHom
  have hBN : B ≤ N := (map_mono hAN).trans_eq (Normal.map_conj_eq N g)
  have hB : B.subgroupOf N ∈ QhatStar (ρ.comp N.subtype) := by
    apply (ht.2 _).mpr
    rw [map_subgroupOf_eq_of_le hBN]
    exact QhatStar.map_conj ρ hA g
  have hh := map_mono (le_sSup hB) (f := N.subtype)
  rw [map_subgroupOf_eq_of_le hBN] at hh
  exact hh (mem_map.mpr ⟨a,ha,rfl⟩)

omit [Finite G] in
/-- The normal closure of a cyclic original starred actor retains the exact
unmoved cyclic source hypotheses. -/
theorem normalClosure_cyclic_core (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ ≤ 2)
    (hrank : ∀ A ∈ QhatStar ρ, rank A = 1)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) :
    CoreHypotheses (ρ.comp (normalClosure (A : Set G)).subtype) := by
  let N := normalClosure (A : Set G)
  have ht := subgroup_starred_transport ρ N ⟨A,hA,le_normalClosure⟩
  refine ⟨hf.comp N.subtype_injective,ht.1 ▸ hq,
    normalClosure_starred_generated ρ hA,generalizedFitting_eq_fitting_of_solvable N,
    normal_subgroup_twoCore_eq_bot N hcore,?_⟩
  intro B hB
  rw [←rank_map_injective N.subtype N.subtype_injective]
  exact hrank _ ((ht.2 B).mp hB)

omit [Finite G] [Group.IsSolvable G] [FiniteDimensional (ZMod 2) V] in
/-- Centralizing the original five-core rules out quintic movement throughout
the actor's normal closure, using the intrinsic core's literal inclusion. -/
theorem normalClosure_no_five {A : Subgroup G} (hfive : ⁅pCore 5 G,A⁆ = ⊥) :
    ∀ B : Subgroup (normalClosure (A : Set G)),
      ⁅pCore 5 (normalClosure (A : Set G)),B⁆ = ⊥ := by
  let N := normalClosure (A : Set G)
  have hNC : N ≤ centralizer (pCore 5 G : Set G) := normalClosure_le_normal
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hfive))
  have hp : (pCore 5 N).map N.subtype ≤ pCore 5 G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map N.subtype⟩
  intro B
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro p hpN b hb
  apply Subtype.ext
  exact (hNC b.property p (hp (mem_map_of_mem N.subtype hpN))).symm

/-- A normal starred-generated actor with its original ambient seed admits
the three-core reduction; it need not equal the entire ambient Jhat. -/
theorem normal_seededThreeCore_factors (hf : Function.Injective ρ)
    (H : Subgroup G) [H.Normal] (h : CoreHypotheses (ρ.comp H.subtype))
    (hwit : ∃ A ∈ QhatStar ρ, A ≤ H)
    (hq : cubicRatio (ρ.comp H.subtype) = 2)
    (hfive : ∀ A∈QhatStar (ρ.comp H.subtype),⁅pCore 5 H,A⁆=⊥)
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hseed : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w}=⊤) :
    let P := (pCore 3 H).map H.subtype
    ∃ d : FactorData ρ H (subspaceCommutator ρ ⊤ P),
      subspaceCommutator d.representation ⊤ (fittingSubgroup H) = ⊤ ∧
        ∃ c : Decomposition d.representation, c.FittingFull := by
  let P := (pCore 3 H).map H.subtype
  let : P.Normal := inferInstanceAs ((pCore 3 H).map H.subtype).Normal
  have hPH : P ≤ H := map_subtype_le _
  have hPS : P.subgroupOf H = pCore 3 H := by
    exact (Subgroup.map_injective H.subtype_injective) (map_subgroupOf_eq_of_le hPH)
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := H)).map H.subtype |>.exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  let U := subspaceCommutator ρ ⊤ P
  have hsup : U ⊔ fixedSpace ρ H = ⊤ := by
    have hs := h.threeCore_fixed_supplement_of_ambient_seed ρ H S Z hseed hspan hq hfive
    simpa only [subspaceCommutator_comp_map,fixedSpace_comp_map,
      ←MonoidHom.range_eq_map,Subgroup.range_subtype] using hs
  have hs := oddMoved_stable ρ H P
  have ht := side_transport ρ hs hsup le_rfl hwit
  have hfull := oddMovedAction_full_of_le ρ H P hPH hodd (fittingSubgroup H)
    (hPS.symm ▸ pCore_le_fitting H 3)
  have hgen : Jhat (oddMovedAction ρ H P) = ⊤ := by
    apply top_unique
    rw [←h.generated]
    apply sSup_le
    intro B hB
    exact le_sSup ((ht.2 B).mpr ((subgroup_starred_transport ρ H hwit).2 B |>.mp hB))
  have hsupport : subspaceCommutator ρ ⊤ H = U := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,_,rfl⟩
      obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
        (show v ∈ U ⊔ fixedSpace ρ H from hsup ▸ Submodule.mem_top)
      have hwg : ρ g w = w := hw ⟨g,hg⟩
      have he : ρ g (u+w) - (u+w) = ρ g u-u := by rw [map_add,hwg]; abel
      rw [he]
      exact U.sub_mem ((hs hg u).mpr hu) hu
    · apply Submodule.span_mono
      rintro _ ⟨p,hp,v,hv,rfl⟩
      exact ⟨p,hPH hp,v,hv,rfl⟩
  let d : FactorData ρ H U :=
    ⟨oddMovedAction ρ H P,fun _ _ => rfl,side_faithful ρ hf hs hsup le_rfl,hgen,
      by
        apply top_unique
        apply hfull.ge.trans
        apply Submodule.span_mono
        rintro _ ⟨g,hg,v,hv,rfl⟩
        exact ⟨g,Subgroup.mem_top g,v,hv,rfl⟩,
      hsupport,hsup,ht.1,ht.2⟩
  exact ⟨d,hfull,source_fitting_decomposition d.representation d.faithful d.generated hfull
    (ht.1 ▸ (subgroup_starred_transport ρ H hwit).1 ▸ h.ratio_le)⟩

/-- The original non-quintic actor's normal closure supplies a literal fully
moved factor datum even when other starred actors do move the five-core. -/
theorem source_three_normalClosure_seed_factors (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ = 2)
    (hrank : ∀ A ∈ QhatStar ρ, rank A = 1)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hfive : ⁅pCore 5 G,A⁆ = ⊥)
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hseed : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w}=⊤) :
    let N := normalClosure (A : Set G)
    let P := (pCore 3 N).map N.subtype
    ∃ d : FactorData ρ N (subspaceCommutator ρ ⊤ P),
      subspaceCommutator d.representation ⊤ (fittingSubgroup N) = ⊤ ∧
        ∃ c : Decomposition d.representation, c.FittingFull := by
  let N := normalClosure (A : Set G)
  have hbound : cubicRatio ρ ≤ 2 := hq.le
  have h := normalClosure_cyclic_core ρ hf hcore hbound hrank hA
  exact normal_seededThreeCore_factors ρ hf N h ⟨A,hA,le_normalClosure⟩
    ((subgroup_starred_transport ρ N ⟨A,hA,le_normalClosure⟩).1.trans hq)
    (fun B _ => normalClosure_no_five hfive B) S Z hseed hspan
end CFSG.Quasithin.ChapterD
