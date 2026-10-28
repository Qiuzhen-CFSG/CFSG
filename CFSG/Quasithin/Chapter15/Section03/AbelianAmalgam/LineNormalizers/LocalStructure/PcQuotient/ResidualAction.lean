module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.Definitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.Action
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Recovering the whole line residual from the P_c action

The two-residual of `Y_E T_E` is `Y_E`. Its full action on the four-group
therefore maps `Y_E` onto the alternating subgroup of `Aut(E) ≃ S₃`.
Every nontrivial two-subgroup of this action is odd and has full commutator
with that cubic subgroup. The remaining kernel is a two-group. Since `Y_E`
is two-perfect, it has no residual quotient supported on that kernel.

This proves `Y_E=[Y_E,P_c]` once the Sylow geometry supplies nontrivial
`P_c` action on `E`. It does not assume relative normality in `G_E`:
that is a subsequent consequence in `ResidualSpan`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, using 15.3.66(5) on printed p.1152.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
private theorem even_cube : ∀ a : Equiv.Perm (Fin 3),
    a ∈ alternatingGroup (Fin 3) → a ^ 3 = 1 := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem odd_commutator : ∀ a b : Equiv.Perm (Fin 3),
    a ∈ alternatingGroup (Fin 3) → b ∉ alternatingGroup (Fin 3) → ⁅a⁻¹,b⁆ = a := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

variable {G : Type*} [Group G]
private theorem commutator_eq_of_perm_three_image (f : G →* Equiv.Perm (Fin 3)) (H P : Subgroup G)
    (hH : IsPPerfect 2 H) (hP : IsPGroup 2 P)
    (hn : P ≤ normalizer (H : Set G))
    (hmap : H.map f = alternatingGroup (Fin 3))
    (hk : IsPGroup 2 f.ker) (hnot : ¬ P ≤ f.ker) : H = ⁅H,P⁆ := by
  have hCH : ⁅H,P⁆ ≤ H := le_normalizer_iff_commutator_le_left.mp hn
  obtain ⟨b,hb,hbn⟩ := SetLike.not_le_iff_exists.mp hnot
  have hbn' : f b ≠ 1 := hbn
  have hbodd : f b ∉ alternatingGroup (Fin 3) := by
    intro heven
    have hc := even_cube (f b) heven
    obtain ⟨n,hn⟩ := hP ⟨b,hb⟩
    have hp : f b ^ 2 ^ n = 1 := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using
        congrArg f (congrArg Subtype.val hn)
    exact hbn' (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((by decide : Nat.Coprime 2 3).pow_left n)
      (orderOf_dvd_of_pow_eq_one hp) (orderOf_dvd_of_pow_eq_one hc)))
  have himage : H.map f ≤ (⁅H,P⁆).map f := by
    intro a ha
    have hae : a ∈ alternatingGroup (Fin 3) := hmap ▸ ha
    have hainv : a⁻¹ ∈ H.map f := (H.map f).inv_mem ha
    obtain ⟨x,hx,hfx⟩ := hainv
    refine ⟨⁅x,b⁆, commutator_mem_commutator hx hb, ?_⟩
    rw [map_commutatorElement, hfx]
    exact odd_commutator a (f b) hae hbodd
  let K := (⁅H,P⁆).subgroupOf H
  let : K.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left H P)
  let r : H →* Equiv.Perm (Fin 3) := f.comp H.subtype
  have hr : IsPGroup 2 r.ker := hk.comap_of_injective H.subtype H.subtype_injective
  have htop : K ⊔ r.ker = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨c,hc,hcx⟩ := himage (mem_map_of_mem f x.property)
    have hcH := hCH hc
    let c' : H := ⟨c,hcH⟩
    have hxker : x * c'⁻¹ ∈ r.ker := by
      change f ((x : G) * c⁻¹) = 1
      rw [map_mul, map_inv, hcx, mul_inv_cancel]
    have hcK : c' ∈ K := hc
    have he : x = (x * c'⁻¹) * c' := by group
    rw [he]
    exact mul_mem (mem_sup_right hxker) (mem_sup_left hcK)
  have hKtop := hH K inferInstance (isPGroup_quotient_of_sup_eq_top K r.ker hr htop)
  apply le_antisymm _ hCH
  intro h hh
  have hm : (⟨h,hh⟩ : H) ∈ K := hKtop.symm ▸ mem_top _
  exact hm

open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
open CFSG.Quasithin.Chapter15.Section03

variable {G : Type*} [Group G] [Finite G]

/-- The genuine line residual is two-perfect. -/
theorem lineY_isPPerfect (Y E : Subgroup G) : IsPPerfect 2 (lineY Y E) := by
  rw [lineY, ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  exact isPPerfect_embedded_pResidual 2 _

/-- Nontrivial `P_c` action on `E` gives the full commutator in the source.
The only geometric premise is noncentrality on `E`; the cubic image and
the two-group kernel are derived from the actual 15.3.66 action. -/
theorem lineY_commutator_of_noncentral_Pc
    (Mc Y E : Subgroup G) (T : Sylow 2 G) [IsKleinFour E]
    (hcore : Stellmacher.twoCoreAmbient Mc ≤ T)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hfull : Function.Surjective
      (lineAction E (lineY Y E ⊔ lineT T E) (lineProduct_le_normalizer Y T E)))
    (hkernel : lineS Y T E = (lineY Y E ⊔ lineT T E) ⊓ lineC E)
    (hnot : ¬ linePc Mc E ≤ lineC E) :
    lineY Y E = ⁅lineY Y E, linePc Mc E⁆ := by
  let A := lineY Y E ⊔ lineT T E
  let H := (lineY Y E).subgroupOf A
  let P := (linePc Mc E).subgroupOf A
  let R := (lineT T E).subgroupOf A
  have hHA : lineY Y E ≤ A := le_sup_left
  have hPcT : linePc Mc E ≤ lineT T E := inf_le_inf_right _ hcore
  have hPA : linePc Mc E ≤ A := hPcT.trans le_sup_right
  have hTA : lineT T E ≤ A := le_sup_right
  have hhn : A ≤ normalizer (lineY Y E : Set G) :=
    sup_le (lineY Y E).le_normalizer (lineT_le_normalizer_lineY Y T E hTY)
  let : H.Normal := normal_subgroupOf_of_le_normalizer hhn
  have hperf : IsPPerfect 2 (lineY Y E) := lineY_isPPerfect Y E
  have hH : IsPPerfect 2 H := hperf.of_surjective
    (subgroupOfEquivOfLe hHA).symm.toMonoidHom (subgroupOfEquivOfLe hHA).symm.surjective
  have hR : IsPGroup 2 R :=
    (T.isPGroup'.to_le (show lineT T E ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  have hP : IsPGroup 2 P :=
    ((isPGroup_pCoreIn 2 Mc).to_le (show linePc Mc E ≤ Mc.pCoreIn 2 from inf_le_left)).comap_subtype
  have hgen : H ⊔ R = ⊤ := by
    change (lineY Y E).subgroupOf A ⊔ (lineT T E).subgroupOf A = ⊤
    rw [← subgroupOf_sup hHA hTA]
    exact subgroupOf_self A
  have hres : pResidual 2 A = H := pResidual_eq_of_isPPerfect_sup H R hH hR hgen
  let e := IsKleinFour.autEquivPermThree E
  let f : A →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp
    (lineAction E A (lineProduct_le_normalizer Y T E))
  have hf : Function.Surjective f := e.surjective.comp hfull
  have hmap : H.map f = alternatingGroup (Fin 3) := by
    rw [← hres, map_pResidual_of_surjective 2 f hf, Equiv.Perm.twoResidual_eq_alternating]
  have hk : f.ker = (lineC E).subgroupOf A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, lineAction_ker]
  have hker : IsPGroup 2 f.ker := by
    rw [hk]
    have hs : (lineC E).subgroupOf A = pCore 2 A := by
      apply map_injective A.subtype_injective
      rw [subgroupOf_map_subtype, inf_comm]
      exact hkernel.symm
    rw [hs]
    exact pCore_isPGroup
  have hnot' : ¬ P ≤ f.ker := by
    intro hp
    apply hnot
    intro p hpc
    have hp' : (⟨p,hPA hpc⟩ : A) ∈ f.ker := hp hpc
    rw [hk] at hp'
    exact hp'
  have hn : P ≤ normalizer (H : Set A) := le_top.trans (normalizer_eq_top H).symm.le
  have he := commutator_eq_of_perm_three_image f H P hH hP hn hmap hker hnot'
  have hm := congrArg (fun K : Subgroup A => K.map A.subtype) he
  simpa only [H, P, map_commutator, map_subgroupOf_eq_of_le hHA,
    map_subgroupOf_eq_of_le hPA] using hm

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
