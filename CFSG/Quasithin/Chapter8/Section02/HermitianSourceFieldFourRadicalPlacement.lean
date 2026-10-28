module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourRadical
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Commutator
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.GroupTheory.PPerfectHom

/-!
# Radical placement at the Hermitian field-four normalizer

The actual local residual is nonsolvable, is normalized by the original Sylow,
and has simple two-core quotient. The radical commutator theorem gives
[Ξ_p(K),R] = Ξ_p(K). If the radical lay in the original component normalizer,
relative normality of R would put the radical inside R. A solvable normal
subgroup of R lies in O₂(R), contradicting two-perfectness and nontriviality.

For an elementary odd quotient, Ξ-irreducibility also proves that adjoining
the original Sylow gives a minimal outside overgroup. The companion Chapter 12
module applies both deductions at the selected and zero-closure fixed subgroups
and removes radical placement from the natural A.3.6 exclusion. The nilpotent
alternative and the remaining 8.2.8--13 argument are separate obligations.

Source: Aschbacher--Smith, 8.2.7, printed pp.717--718, using 1.3.3 and
A.3.3(1); refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem solvable_twoPerfect_normal_eq_bot
    (X R : Subgroup G) [Group.IsPerfect R] [IsSimpleGroup (R ⧸ pCore 2 R)]
    [Group.IsSolvable X] (hXR : X ≤ R) (hn : R ≤ normalizer (X : Set G))
    (hp : IsPPerfect 2 X) : X = ⊥ := by
  let A := X.subgroupOf R
  let e : A ≃* X := subgroupOfEquivOfLe hXR
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hA : A ≤ pCore 2 R := by
    rw [←PerfectCoreTwoExtension.radical_eq_core]
    exact le_solvableRadical A inferInstance inferInstance
  let f : X →* pCore 2 R := (inclusion hA).comp e.symm.toMonoidHom
  have hf := hp.hom_eq_one_of_isPGroup pCore_isPGroup f
  apply bot_unique
  intro x hx
  have he := DFunLike.congr_fun hf (⟨x,hx⟩ : X)
  exact congrArg (fun z : pCore 2 R => ((z : R) : G)) he

/-- The actual radical lies outside M when its nonsolvable source residual
is relatively normal in M intersect N_G(U). -/
theorem radical_not_le_relative_normalizer
    {κ : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK κ E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
        C.IsCComponent → A36Conclusion C)
    {T K R M N : Subgroup G}
    [Group.IsPerfect R] [IsSimpleGroup (R ⧸ pCore 2 R)]
    (hK : K ∈ Chapter1.L G T)
    (hQ : IsSQTK κ ((K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)))
    (hTK : T ≤ normalizer (K : Set G)) (hTR : T ≤ normalizer (R : Set G))
    (hRK : R ≤ K) (hKN : K ≤ N)
    (hMR : M ⊓ N ≤ normalizer (R : Set G))
    (hn : ¬ IsQuasisimple (XiQuotient K))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K)))
    (hX : XiMember T (XiP p K)) : ¬ XiP p K ≤ M := by
  have hR : ¬ Group.IsSolvable R := by
    intro hs
    let := hs
    exact Group.IsPerfect.not_isSolvable (R ⧸ pCore 2 R) inferInstance
  have hcomm := RadicalActions.XiP_commutator_eq_of_nonsolvable_subgroup_of_A36
    hA36 hK hQ hn hTK hTR hRK hR ho hd
  intro hXM
  have hXRn : XiP p K ≤ normalizer (R : Set G) :=
    (le_inf hXM ((XiP_le p K).trans hKN)).trans hMR
  have hXR : XiP p K ≤ R := by
    rw [←hcomm,commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hXRn
  let : Group.IsSolvable (XiP p K) := hX.isSolvable
  exact hX.ne_bot (solvable_twoPerfect_normal_eq_bot (XiP p K) R hXR
    (hRK.trans (XiP_invariant p K.le_normalizer)) hX.perfect)

private theorem elementary_Xi_intermediate
    {T X Y : Subgroup G} (hX : XiMember T X)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p (XiQuotient X)]
    (hcore : X.pCoreIn 2 ≤ T) (hTY : T ≤ Y) (hY : Y ≤ X ⊔ T) :
    Y ≤ T ∨ X ≤ Y := by
  let I := Y.subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := QuotientGroup.mk' (frattini (XiQuotient X))
  let A := (I.map q).map r
  let : Fact (IsPGroup p (XiQuotient X)) := ⟨IsElementaryAbelian.isPGroup p _⟩
  have hphi : frattini (XiQuotient X) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := p)
  have hstable : ∀ t : T, ∀ a ∈ A, xiFrattiniAction T X hX.invariant t a ∈ A := by
    rintro t a ⟨b,⟨x,hx,rfl⟩,rfl⟩
    let z : X := ⟨(t : G)*x*(t : G)⁻¹,
      (mem_normalizer_iff.mp (hX.invariant t.property) x).mp x.property⟩
    have hz : z ∈ I := Y.mul_mem (Y.mul_mem (hTY t.property) hx)
      (Y.inv_mem (hTY t.property))
    refine ⟨q z,⟨z,hz,rfl⟩,?_⟩
    simp only [r,q,xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    rfl
  rcases hX.irreducible A hstable with hb | ht
  · left
    have hi : I ≤ pCore 2 X := by
      intro x hx
      have hz : r (q x) = 1 := mem_bot.mp (hb ▸ mem_map_of_mem r (mem_map_of_mem q hx))
      have hq := (QuotientGroup.eq_one_iff _).mp hz
      rw [hphi] at hq
      exact (QuotientGroup.eq_one_iff _).mp hq
    intro y hy
    have hyt := hY hy
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hX.invariant] at hyt
    obtain ⟨x,hx,t,ht,hxt⟩ := hyt
    have hxY : x ∈ Y := by
      have hh : x = y*t⁻¹ := by rw [←hxt,mul_inv_cancel_right]
      rw [hh]
      exact Y.mul_mem hy (Y.inv_mem (hTY ht))
    have hxT : x ∈ T := hcore ⟨⟨x,hx⟩,hi hxY,rfl⟩
    rw [←hxt]
    exact T.mul_mem hxT ht
  · right
    have hI : I.map q = ⊤ := by
      apply frattini_nongenerating
      have hh := congrArg (comap r) ht
      simpa only [A,comap_map_eq,r,QuotientGroup.ker_mk',comap_top] using hh
    have hsup : I ⊔ pCore 2 X = ⊤ := by
      have hh := congrArg (comap q) hI
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
    have hc : pCore 2 X ≤ I := fun x hx => hTY (hcore ⟨x,hx,rfl⟩)
    rw [sup_eq_left.mpr hc] at hsup
    exact subgroupOf_eq_top.mp hsup

/-- An escaping elementary-quotient Xi radical gives the literal minimal
outside overgroup, including H-star minimality. -/
theorem elementary_radical_join_HStar
    (T : Sylow 2 G) {X M : Subgroup G} (hX : XiMember (T : Subgroup G) X)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p (XiQuotient X)]
    (hTM : (T : Subgroup G) ≤ M) (hout : ¬ X ≤ M) :
    X ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M := by
  have hc := hX.pCoreIn_le_of_isSylowIn
    (show IsSylowIn 2 (T : Subgroup G) (X ⊔ (T : Subgroup G)) from
      ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩)
  refine ⟨⟨⟨hX.join_mem_H,(show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right)⟩,fun hh => hout (le_sup_left.trans hh)⟩,?_⟩
  intro Y hY hYX
  rcases elementary_Xi_intermediate (p := p) hX hc hY.1.2 hYX with hYT | hXY
  · exact (hY.2 (hYT.trans hTM)).elim
  · exact sup_le hXY hY.1.2

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
