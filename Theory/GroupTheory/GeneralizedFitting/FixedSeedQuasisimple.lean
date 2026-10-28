module
public import Theory.GroupTheory.Commutator.ThompsonAB
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.OddKernelInvolutionCentralizer
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# Quasisimplicity detected in a prime-subgroup centralizer

An ordinary component of C_G(B), for a p-subgroup B, centralizes every
normal p-subgroup P of G. It centralizes C_P(B) by component calculus;
Thompson's residual A × B lemma then makes it centralize P. If that seed
lies in a normal C-component Q with quasisimple p-core quotient, the
centralizer of O_p(Q) in Q cannot be a proper solvable normal subgroup.
Thus O_p(Q) is central and Q itself is quasisimple.

For a central cover, a perfect simultaneous-centralizer residual centralizes
the full inverse image of a cyclic p-subgroup. Restricting its normality
places it as an ordinary component of that inverse image's centralizer.
All maps retain the full central kernel, which is allowed to be a p-group.
This supplies the seed for the preceding criterion, without an ambient
normality inference from local normality.

Source: Thompson's A × B lemma, Aschbacher--Smith A.1.18, p.24;
application to the full cubic residual in 4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- An ordinary fixed-subgroup component centralizes every normal p-subgroup. -/
theorem IsComponentIn.centralizes_normal_pGroup
    {S B : Subgroup G} (hS : IsComponentIn S (centralizer (B : Set G)))
    (hB : IsPGroup p B) (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) :
    S ≤ centralizer (P : Set G) := by
  let C := centralizer (B : Set G)
  let : Group.IsNilpotent (P.subgroupOf C) := (hP.comap_of_injective C.subtype C.subtype_injective).isNilpotent
  have hc := hS.2.le_centralizer_of_solvable_normal (P.subgroupOf C)
  have hfix : P ⊓ centralizer (B : Set G) ≤ centralizer (S : Set G) := by
    intro x hx s hs
    exact (congrArg C.subtype (hc
      (show (⟨s,hS.1 hs⟩ : C) ∈ S.subgroupOf C from hs) ⟨x,hx.2⟩ hx.1)).symm
  let := hS.quasisimple
  have hres : pResidual p S = ⊤ := by
    rw [pResidual_eq_top_iff]
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (S ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (S ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (S ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (S ⧸ N) inferInstance
  have hh := thompson_a_times_b_centralizer S B P hB hP hres
    le_normalizer_of_normal le_normalizer_of_normal
    (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hS.1) hfix
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)

end Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A nonsolvable fixed component forces the containing C-component’s
p-core to be central, so its quasisimple p-core quotient lifts. -/
theorem IsCComponent.quasisimple_of_fixed_component
    {Q S B : Subgroup G} (hQ : Q.IsCComponent) [Q.Normal]
    [IsQuasisimple (Q ⧸ pCore p Q)]
    (hS : IsComponentIn S (centralizer (B : Set G)))
    (hB : IsPGroup p B) (hSQ : S ≤ Q) : IsQuasisimple Q := by
  let P := Q.pCoreIn p
  let : P.Normal := inferInstanceAs ((pCore p Q).map Q.subtype).Normal
  have hSP := hS.centralizes_normal_pGroup hB P (isPGroup_pCoreIn p Q)
  let C := (centralizer (P : Set G)).subgroupOf Q
  have hQC : Q ≤ centralizer (P : Set G) := by
    by_contra hn
    have hne : C ≠ ⊤ := fun he => hn (subgroupOf_eq_top.mp he)
    let : Group.IsSolvable C := hQ.isSolvable_of_subnormal_lt_top
      (inferInstance : C.Normal).isSubnormal hne
    let f : S →* C := {
      toFun s := ⟨⟨s,hSQ s.property⟩,hSP s.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hi : Function.Injective f := fun a b he =>
      Subtype.ext (congrArg (fun c : C => ((c : Q) : G)) he)
    let := hS.quasisimple
    let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
    let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
    exact Group.IsPerfect.not_isSolvable S (Group.isSolvable_of_isSolvable_injective hi)
  have hcentral : pCore p Q ≤ center Q := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (hQC y.property x (mem_map_of_mem Q.subtype hx)).symm
  exact (show PerfectCentralCovering.Cover Q (Q ⧸ pCore p Q) from
    { toMonoidHom := QuotientGroup.mk' (pCore p Q)
      surjective := QuotientGroup.mk'_surjective _
      isPerfect := hQ.perfect
      ker_le_center := (QuotientGroup.ker_mk' _).trans_le hcentral }).isQuasisimple
end Subgroup
namespace Theory.GroupTheory
variable {U Y : Type*} [Group U] [Finite U] [Group Y]

/-- The perfect residual in the preimage of an element centralizer remains
an ordinary component in the centralizer of the full cyclic preimage. -/
theorem central_cover_residual_fixed_seed
    {p : ℕ} [Fact p.Prime] (f : U →* Y) (hf : Function.Surjective f)
    (hker : f.ker ≤ center U) (hkerp : IsPGroup p f.ker)
    (y : Y) (hyp : IsPGroup p (zpowers y))
    (x : (centralizer ({y} : Set Y)).comap f)
    (hxS : (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ :
      centralizer ({x} : Set ((centralizer ({y} : Set Y)).comap f))) ∈
        solvableResidual (centralizer ({x} : Set ((centralizer ({y} : Set Y)).comap f))))
    (hS : IsQuasisimple (solvableResidual
      (centralizer ({x} : Set ((centralizer ({y} : Set Y)).comap f))))) :
    let R := (centralizer ({y} : Set Y)).comap f
    let C := centralizer ({(x : U)} : Set U)
    let S := (solvableResidual (centralizer ({x} : Set R))).map
      (R.subtype.elementCentralizerMap x)
    ∃ B : Subgroup C, IsPGroup p B ∧ IsComponentIn S (centralizer (B : Set C)) := by
  let R := (centralizer ({y} : Set Y)).comap f
  let D := centralizer ({x} : Set R)
  let C := centralizer ({(x : U)} : Set U)
  let E := solvableResidual D
  let i : E →* U := R.subtype.comp (D.subtype.comp E.subtype)
  let j : D →* C := R.subtype.elementCentralizerMap x
  have hj : Function.Injective j := by
    intro c d he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : U)) he))
  let S := E.map j
  let B := (zpowers y).comap f
  let := hS
  have hSB : ∀ s : E, i s ∈ centralizer (B : Set U) := by
    intro s b hb
    have he : (MulAut.conj b).toMonoidHom.comp i = i := by
      apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq f hker
      ext a
      change f (b * i a * b⁻¹) = f (i a)
      rw [map_mul,map_mul,map_inv]
      have hc : f (i a) ∈ centralizer (zpowers y : Set Y) := by
        rw [zpowers_eq_closure,centralizer_closure]
        exact a.val.val.property
      rw [hc (f b) hb,mul_inv_cancel_right]
    have ha := DFunLike.congr_fun he s
    exact mul_inv_eq_iff_eq_mul.mp ha
  have hBC : B ≤ C := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (hSB ⟨⟨x,mem_centralizer_singleton_iff.mpr rfl⟩,hxS⟩ b hb)
  let BC := B.subgroupOf C
  let Z := centralizer (BC : Set C)
  have hSZ : S ≤ Z := by
    rintro z ⟨a,ha,rfl⟩ b hb
    exact Subtype.ext (hSB ⟨a,ha⟩ b hb)
  have hZR : ∀ z : Z, (z.val : U) ∈ R := by
    intro z
    change f (z.val : U) ∈ centralizer ({y} : Set Y)
    obtain ⟨b,hb⟩ := hf y
    have hbB : b ∈ B := by change f b ∈ zpowers y; rw [hb]; exact mem_zpowers y
    have hh := congrArg (fun c : C => f (c : U))
      (z.property ⟨b,hBC hbB⟩ hbB)
    change f (b * (z.val : U)) = f ((z.val : U) * b) at hh
    simp only [map_mul] at hh
    rw [hb] at hh
    exact mem_centralizer_singleton_iff.mpr hh.symm
  let g : Z →* D := {
    toFun z := ⟨⟨z.val.val,hZR z⟩,mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp z.val.property))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have he : S.subgroupOf Z = E.comap g := by
    ext z
    constructor
    · rintro ⟨a,ha,he⟩
      have hg : g z = a := hj (by exact he.symm)
      change g z ∈ E
      rw [hg]
      exact ha
    · intro hz
      exact ⟨g z,hz,rfl⟩
  have hn : (S.subgroupOf Z).Normal := by rw [he]; infer_instance
  let e : E ≃* S := E.equivMapOfInjective j hj
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv e
  refine ⟨BC,(hyp.comap_of_ker_isPGroup f hkerp).comap_of_injective C.subtype C.subtype_injective,
    hSZ,hn.isSubnormal,?_⟩
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hSZ).symm
end Theory.GroupTheory
