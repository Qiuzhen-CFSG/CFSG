module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.Setup
public import Theory.GroupTheory.ReducedNormal.CoprimeSupplement

/-!
# Reducedness of the original Xi commutator module

For X in Xi(G,T), the odd p-group quotient X/O₂(X) makes an original
Sylow p-subgroup a supplement to O₂(X). Its image in J=XT has order
coprime to W=R₂(J), while O₂(X) maps into O₂(J) and centralizes W.
The literal quotient J/X is a two-group. The coprime supplement theorem
therefore proves [W,X] reduced and identifies its centralizer with C_J(W).

This uses the actual subgroup inclusions and needs neither V nontrivial
nor the irreducible Frattini action. Those premises remain relevant to the
separate assertion C_T(V)=O₂(J), which is not claimed here.
Source: Aschbacher--Smith, Lemma 3.2.13, printed pp.584--585.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem sourceModule_reduced_and_centralizer (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G)) :
    IsPReduced 2 (sourceModule (T : Subgroup G) X) ∧
    centralizer (sourceModule (T : Subgroup G) X : Set (sourceGroup (T : Subgroup G) X)) =
      centralizer (reducedTwoSubgroup (sourceGroup (T : Subgroup G) X) :
        Set (sourceGroup (T : Subgroup G) X)) := by
  let J := sourceGroup (T : Subgroup G) X
  let Y := X.subgroupOf J
  let S := (T : Subgroup G).subgroupOf J
  let W := reducedTwoSubgroup J
  let C := centralizer (W : Set J)
  let i : X →* J := inclusion (show X ≤ J from le_sup_left)
  let := hX.normal_in_join
  have hYtop : (⊤ : Subgroup X).map i = Y := by
    ext j
    constructor
    · rintro ⟨x, _, rfl⟩
      exact x.property
    · intro hj
      exact ⟨⟨j.val, hj⟩, mem_top _, Subtype.ext rfl⟩
  have hYS : Y ⊔ S = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show X ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup 2 (J ⧸ Y) :=
    isPGroup_quotient_of_sup_eq_top Y S T.isPGroup'.comap_subtype hYS
  obtain ⟨q, hq, ho, hodd⟩ := hX.odd_quotient
  let : Fact q.Prime := ⟨hq⟩
  let P : Sylow q X := Classical.choice inferInstance
  let Q := (P : Subgroup X).map i
  have hQY : Q ≤ Y := hYtop ▸ map_mono (f := i) le_top
  have hQp : IsPGroup q Q := P.isPGroup'.map i
  have hW := isPReduced_reducedPSubgroup (p := 2) (G := J)
  let := hW.elementary
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card W) :=
    IsPGroup.coprime_card_of_ne q 2 (by intro he; subst q; norm_num at ho)
      Q W hQp (IsElementaryAbelian.isPGroup 2 W)
  have hs : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, pCoreIn] using
      hX.sylow_sup hodd P
  have hsJ : (pCore 2 X).map i ⊔ Q = Y := by
    rw [← Subgroup.map_sup, hs, hYtop]
  have hcore : (pCore 2 X).map i ≤ pCore 2 J := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := hj
    have hh := pCoreIn_mono_of_normalizes (show X ≤ J from le_sup_left)
      (sup_le X.le_normalizer hX.invariant) (mem_map_of_mem X.subtype hx)
    obtain ⟨y, hy, he⟩ := hh
    have hey : y = i x := Subtype.ext he
    exact hey ▸ hy
  have hgen : Y ≤ C ⊔ Q := by
    rw [← hsJ]
    exact sup_le_sup (hcore.trans
      (le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 J))) le_rfl
  exact ⟨hW.commutator_of_coprime_supplement Y Q hquot hQY hcop hgen,
    hW.centralizer_commutator_eq_of_coprime_supplement Y Q hquot hQY hcop hgen⟩

/-- The literal module [R₂(XT),X] is reduced for every Xi member. -/
theorem sourceModule_reduced (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G)) :
    IsPReduced 2 (sourceModule (T : Subgroup G) X) :=
  (sourceModule_reduced_and_centralizer T hX).1

/-- Restricting the original action to [R₂(XT),X] preserves its kernel. -/
theorem sourceModule_centralizer_eq_reduced (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G)) :
    centralizer (sourceModule (T : Subgroup G) X : Set (sourceGroup (T : Subgroup G) X)) =
      centralizer (reducedTwoSubgroup (sourceGroup (T : Subgroup G) X) :
        Set (sourceGroup (T : Subgroup G) X)) :=
  (sourceModule_reduced_and_centralizer T hX).2

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
