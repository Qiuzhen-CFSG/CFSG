module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CoreChiefAction
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CoreCosetTransitivity
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CommutingCoreDerived
public import Theory.GroupAction.SixteenQuinticOrbitDichotomy

/-!
# A five-point orbit in the original central quotient

For an original commuting pair with core order at most256, the first
component acts on the actual elementary sixteen quotient with its original
two-core as kernel. Its image contains five. The opposite chosen module
rules out transitivity by transporting its involutions. The literal
quotient therefore has an actual orbit of size five, ready for the
permutation-module marking. No four-dimensional module is postulated.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- An actual five-orbit, with the original quotient and conjugation formula. -/
theorem original_commuting_pair_core_five_orbit
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (he : ∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
      h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q h) w)))
    (hVW : V ≤ centralizer (W : Set G))
    (hsmall : Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≤ 256) :
    ∃ hV : (V.subgroupOf (L ⊔ (T : Subgroup G))).Normal,
      letI := hV
      let J := L ⊔ (T : Subgroup G)
      let π := QuotientGroup.mk' (V.subgroupOf J)
      let A := (pCore 2 J).map π
      ∃ ρ : L →* MulAut A,
        (∀ (l : L) (a : A),
          (ρ l a : J ⧸ V.subgroupOf J) =
            π (inclusion le_sup_left l) * a.val * (π (inclusion le_sup_left l))⁻¹) ∧
        Nat.card A = 16 ∧ IsElementaryAbelian 2 A ∧ ρ.ker = pCore 2 L ∧
          5 ∣ Nat.card ρ.range ∧
          ∃ a : A, a ≠ 1 ∧ (Set.range (fun l : L => ρ l a)).ncard = 5 := by
  obtain ⟨hV,ρ,hρ,_,hA,hAe,hker,hfive⟩ := d.core_quotient_simple_action hsmall
    (original_commuting_pair_noncyclic_cores d e hjoin hH hd q hq hk he hVW).2
  let := hV
  let J := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf J
  let π := QuotientGroup.mk' U
  let A := (pCore 2 J).map π
  have hnot : ¬ (∀ x y : A, x ≠ 1 → y ≠ 1 → ∃ l : L, ρ l x = y) := by
    intro ht
    apply original_commuting_pair_core_cosets_not_transitive d e hjoin hH hd q hq hk hVW
    intro x hx hxV y hy hyV
    obtain ⟨x,hx,rfl⟩ := hx
    obtain ⟨y,hy,rfl⟩ := hy
    let a : A := ⟨π x,mem_map_of_mem π hx⟩
    let b : A := ⟨π y,mem_map_of_mem π hy⟩
    have ha : a ≠ 1 := by
      intro hh
      have hz : π x = 1 := congrArg Subtype.val hh
      exact hxV ((QuotientGroup.eq_one_iff x).mp hz)
    have hb : b ≠ 1 := by
      intro hh
      have hz : π y = 1 := congrArg Subtype.val hh
      exact hyV ((QuotientGroup.eq_one_iff y).mp hz)
    obtain ⟨l,hl⟩ := ht a b ha hb
    refine ⟨l,?_⟩
    let f : L →* J := inclusion le_sup_left
    have hcoord : π (f l * x * (f l)⁻¹) = π y := by
      rw [map_mul,map_mul,map_inv]
      exact (hρ l a).symm.trans (congrArg Subtype.val hl)
    have hm : (f l * x * (f l)⁻¹) / y ∈ U :=
      (QuotientGroup.eq_iff_div_mem (N := U)).mp hcoord
    exact hm
  have horbit := (Theory.GroupAction.transitive_nonidentity_or_orbit_five_of_image_five
    ρ hfive hA).resolve_left hnot
  exact ⟨hV,ρ,hρ,hA,hAe,hker,hfive,horbit⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
