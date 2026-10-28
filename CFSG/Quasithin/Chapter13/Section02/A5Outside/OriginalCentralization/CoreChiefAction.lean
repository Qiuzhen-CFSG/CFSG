module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CoreTwoFiftySix

/-!
# The literal chief action in the original core of order256

Keep the actual component conjugation on the actual core modulo its chosen
central sixteen. In the noncyclic-derived branch the action is nontrivial,
its kernel is exactly the original component two-core, and five divides its
actual image. This supplies the actor used by the orbit and commutator
arguments, without identifying either possible four-dimensional module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The actual central quotient and its literal conjugation action. -/
theorem core_quotient_simple_action
    (d : Context T L V V₁ V₂ V₃)
    (hsmall : Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≤ 256)
    (hnoncyclic : ¬ IsCyclic (⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,
      (L ⊔ (T : Subgroup G)).pCoreIn 2⁆ : Subgroup G)) :
    ∃ hV : (V.subgroupOf (L ⊔ (T : Subgroup G))).Normal,
      letI := hV
      let H := L ⊔ (T : Subgroup G)
      let π := QuotientGroup.mk' (V.subgroupOf H)
      let A := (pCore 2 H).map π
      ∃ ρ : L →* MulAut A,
        (∀ (l : L) (a : A),
          (ρ l a : H ⧸ V.subgroupOf H) =
            π (inclusion le_sup_left l) * a.val * (π (inclusion le_sup_left l))⁻¹) ∧
        ρ ≠ 1 ∧ Nat.card A = 16 ∧ IsElementaryAbelian 2 A ∧
          ρ.ker = pCore 2 L ∧ 5 ∣ Nat.card ρ.range := by
  obtain ⟨_,hV,hA,hAe,hcomm⟩ :=
    (d.core_cyclic_or_elementary_sixteen_quotient hsmall).resolve_left hnoncyclic
  refine ⟨hV,?_⟩
  let := hV
  let H := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf H
  let π := QuotientGroup.mk' U
  let A := (pCore 2 H).map π
  let : A.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective U)
  let f : L →* H := inclusion le_sup_left
  let ρ : L →* MulAut A := (MulAut.conjNormal : (H ⧸ U) →* MulAut A).comp (π.comp f)
  have hne : ρ ≠ 1 := by
    intro ha
    have hc : f.range.map π ≤ centralizer (A : Set (H ⧸ U)) := by
      rintro _ ⟨_,⟨l,rfl⟩,rfl⟩ a haA
      have he := congrArg (fun b : MulAut A => (b ⟨a,haA⟩ : H ⧸ U))
        (DFunLike.congr_fun ha l)
      change π (f l) * a * (π (f l))⁻¹ = a at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hle : ⁅pCore 2 H,f.range⁆ ≤ U := by
      rw [←QuotientGroup.ker_mk' U,←Subgroup.map_eq_bot_iff,map_commutator]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
    have hf : f.range = L.subgroupOf H := by
      ext x
      constructor
      · rintro ⟨l,rfl⟩
        exact l.property
      · intro hx
        exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
    have hm := map_mono (f := H.subtype) hle
    rw [map_commutator,hf,map_subgroupOf_eq_of_le
      (d.chosen.le_sylow.trans (show (T : Subgroup G) ≤ H from le_sup_right)),
      map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left)] at hm
    apply hcomm
    apply le_antisymm hm
    rw [d.chosen.eq_commutator]
    exact commutator_mono d.chosen.le_core le_rfl
  let : IsSimpleGroup (L ⧸ pCore 2 L) := d.quotient.isSimpleGroup
  have hfive : 5 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr d.quotient.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hk : ρ.ker = pCore 2 L :=
    kernel_eq_core_of_nontrivial_simple_five_action d.twoPerfect hfive
      (pCore_isPGroup.map π) hA.le ρ hne
  have hr : 5 ∣ Nat.card ρ.range := by
    by_contra hn
    have hh := hom_eq_one_of_twoPerfect_simple_five_section d.twoPerfect hfive
      ρ.rangeRestrict (Nat.prime_five.coprime_iff_not_dvd.mpr hn)
    apply hne
    apply MonoidHom.ext
    intro l
    exact congrArg Subtype.val (DFunLike.congr_fun hh l)
  exact ⟨ρ,fun _ _ => rfl,hne,hA,hAe,hk,hr⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
