module
public import Theory.GroupTheory.PerfectCentralCoverOddRankRigidity
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.GroupTheory.QuasithinBasic

/-!
# Perfect parabolic residuals in central covers

A finite perfect local subgroup in a central cover with trivial two-core
embeds in its image whenever that image has odd-prime ranks at most one.
The central kernel has odd order, and cyclic-Sylow transfer removes each
possible odd prime. Applying this to a parabolic preimage identifies its
actual solvable residual with the model residual. A preceding quotient
with two-group kernel preserves the resulting intrinsic two-core quotient.

Source: Aschbacher--Smith, 14.2.8(3), printed p.983; the covering argument
uses I.1.2, printed p.407. The Chapter 14 diagram construction applies this
to the actual point and plane parabolics, retaining both quotient maps.
-/

public section
open Subgroup Theory.GroupTheory
namespace PerfectCentralCovering
variable {X D : Type*} [Group X] [Finite X] [Group D] [Finite D]

/-- Odd-rank-one perfect subgroups lose no elements in the central quotient. -/
theorem Cover.injective_on_perfect_subgroup
    (c : Cover X D) (hc : pCore 2 X = ⊥) (L : Subgroup X)
    [Group.IsPerfect L]
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (L.map c.toMonoidHom) ≤ 1) :
    Function.Injective (c.toMonoidHom.subgroupMap L) := by
  let f := c.toMonoidHom.subgroupMap L
  have hcentral : f.ker ≤ center L := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (c.ker_le_center
      (show c.toMonoidHom x = 1 from congrArg Subtype.val hx)) y
  let d : Cover L (L.map c.toMonoidHom) :=
    ⟨f, c.toMonoidHom.subgroupMap_surjective L, inferInstance, hcentral⟩
  have hodd : Odd (Nat.card f.ker) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    intro hd
    have hk : f.ker.map L.subtype ≤ c.toMonoidHom.ker := by
      rintro _ ⟨x,hx,rfl⟩
      exact congrArg Subtype.val hx
    have hd' : 2 ∣ Nat.card c.toMonoidHom.ker :=
      hd.trans ((Subgroup.card_map_of_injective L.subtype_injective).symm ▸
        card_dvd_of_le hk)
    exact not_dvd_card_central_of_pCore_eq_bot hc _ c.ker_le_center hd'
  exact f.ker_eq_bot_iff.mp (d.ker_eq_bot_of_odd_of_odd_primeRank_le_one hodd hr)

/-- The original central projection identifies the two actual residuals. -/
@[expose] noncomputable def Cover.residualPreimageEquiv
    (c : Cover X D) (hc : pCore 2 X = ⊥) (P : Subgroup D)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (solvableResidual P) ≤ 1) :
    solvableResidual (P.comap c.toMonoidHom) ≃* solvableResidual P := by
  let R := P.comap c.toMonoidHom
  let L := (solvableResidual R).map R.subtype
  let : Group.IsPerfect L := Group.IsPerfect.map R.subtype
  have hm : L.map c.toMonoidHom = (solvableResidual P).map P.subtype :=
    map_solvableResidual_comap c.toMonoidHom c.surjective P
  have hL := c.injective_on_perfect_subgroup hc L (fun p hp ho => by
    rw [hm, ← primeRank_equiv p
      ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective)]
    exact hr p hp ho)
  let f := (c.toMonoidHom.subgroupComap P).solvableResidualMap
  apply MulEquiv.ofBijective f
  refine ⟨?_, (c.toMonoidHom.subgroupComap P).solvableResidualMap_surjective
    (c.toMonoidHom.subgroupComap_surjective_of_surjective P c.surjective)⟩
  intro x y hxy
  have hh : c.toMonoidHom.subgroupMap L
      ⟨x.val.val,mem_map_of_mem R.subtype x.property⟩ =
      c.toMonoidHom.subgroupMap L
      ⟨y.val.val,mem_map_of_mem R.subtype y.property⟩ := by
    apply Subtype.ext
    exact congrArg (fun z : solvableResidual P => z.val.val) hxy
  have hval : x.val.val = y.val.val := congrArg (fun z : L => z.val) (hL hh)
  exact Subtype.ext (Subtype.ext hval)

@[simp] theorem Cover.residualPreimageEquiv_apply
    (c : Cover X D) (hc : pCore 2 X = ⊥) (P : Subgroup D)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (solvableResidual P) ≤ 1)
    (x : solvableResidual (P.comap c.toMonoidHom)) :
    (c.residualPreimageEquiv hc P hr x).val.val = c.toMonoidHom x.val.val := rfl

/-- A preceding two-group kernel preserves the residual core quotient. -/
@[expose] noncomputable def Cover.residualPreimagePCoreEquiv
    {A : Type*} [Group A] [Finite A]
    (c : Cover X D) (hc : pCore 2 X = ⊥) (P : Subgroup D)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (solvableResidual P) ≤ 1)
    (q : A →* X) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) :
    (solvableResidual ((P.comap c.toMonoidHom).comap q) ⧸
      pCore 2 (solvableResidual ((P.comap c.toMonoidHom).comap q))) ≃*
    (solvableResidual P ⧸ pCore 2 (solvableResidual P)) := by
  let R := P.comap c.toMonoidHom
  let f := q.subgroupComap R
  have hf : Function.Surjective f := q.subgroupComap_surjective_of_surjective R hq
  have hfker : IsPGroup 2 f.ker := by
    let j : f.ker →* q.ker :=
      ((R.comap q).subtype.comp f.ker.subtype).codRestrict q.ker
        (fun x => congrArg Subtype.val x.property)
    exact hk.of_injective j (by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : q.ker => z.val) hxy)))
  let d := c.residualPreimageEquiv hc P hr
  exact (f.solvableResidualMap.pCoreQuotientEquiv
    (f.solvableResidualMap_surjective hf)
    (f.solvableResidualMap_ker_isPGroup hfker)).trans
      (QuotientGroup.congr _ _ d (pCore_map_iso 2 d))

end PerfectCentralCovering
