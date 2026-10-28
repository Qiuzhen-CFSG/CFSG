module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PrimeDihedralShear

/-!
# A supplied self-normalizing Sylow inverts a normalized quintic section

If a Sylow two-subgroup normalizes Y with |Y/O₂(Y)|=5, its action on that
quotient is nontrivial whenever the Sylow is self-normalizing. Otherwise
all mutual commutators lie in O₂(Y), which is contained in the supplied
Sylow, and Y normalizes it. The nontrivial two-group action contains an
involution, and a nonidentity involution of a prime-order group is inversion.

The resulting element remains in the caller's original Sylow. Only its
action on the quotient is involutory; no involution lift is claimed.
Source application: Aschbacher--Smith 6.1.4, printed pp.665--666, Tits row.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

/-- An actual supplied-Sylow element inverts the whole normalized quintic
subgroup modulo its full two-core, without a faithfulness or inverter premise. -/
theorem self_normalizing_sylow_quintic_inverter
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (Y : Subgroup G)
    (hS : normalizer (S : Set G) = S)
    (hSY : (S : Subgroup G) ≤ normalizer (Y : Set G))
    (hfive : Nat.card (Y ⧸ pCore 2 Y) = 5) :
    ∃ u : G, u ∈ S ∧ ∀ y ∈ Y, u*y*u⁻¹*y ∈ Y.pCoreIn 2 := by
  let C := Y ⧸ pCore 2 Y
  let q := QuotientGroup.mk' (pCore 2 Y)
  let a : S →* MulAut C := (quotientAut (pCore 2 Y)).comp
    (Y.normalizerMonoidHom.comp (inclusion hSY))
  have hRS : Y.pCoreIn 2 ≤ (S : Subgroup G) := by
    have hn : (S : Subgroup G) ≤ normalizer (Y.pCoreIn 2 : Set G) :=
      hSY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
    have he := S.is_maximal'
      (S.isPGroup'.to_sup_of_normal_right' (isPGroup_pCoreIn 2 Y) hn) le_sup_left
    exact le_sup_right.trans he.le
  have ha : a ≠ 1 := by
    intro he
    have hYN : Y ≤ normalizer (S : Set G) := by
      intro y hy
      apply mem_normalizer_iff_map_conj_eq.mpr
      apply eq_of_le_of_card_ge
      · rintro _ ⟨s,hs,rfl⟩
        have hh := congrArg (fun b : MulAut C => b (q ⟨y,hy⟩)) (DFunLike.congr_fun he ⟨s,hs⟩)
        change quotientAut (pCore 2 Y) (Y.normalizerMonoidHom ⟨s,hSY hs⟩)
          (q ⟨y,hy⟩) = q ⟨y,hy⟩ at hh
        rw [quotientAut_apply_mk] at hh
        have hcomm : s*y*s⁻¹*y⁻¹ ∈ Y.pCoreIn 2 := by
          let z : Y := (Y.normalizerMonoidHom ⟨s,hSY hs⟩) ⟨y,hy⟩ * (⟨y,hy⟩ : Y)⁻¹
          have hz : q z=1 := by
            change q ((Y.normalizerMonoidHom ⟨s,hSY hs⟩) ⟨y,hy⟩ * (⟨y,hy⟩ : Y)⁻¹)=1
            rw [map_mul,map_inv,hh,mul_inv_cancel]
          exact mem_map_of_mem Y.subtype ((QuotientGroup.eq_one_iff z).mp hz)
        have hm := (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hRS hcomm)) hs
        change y*s*y⁻¹ ∈ (S : Subgroup G)
        have heq : y*s*y⁻¹ = (s*y*s⁻¹*y⁻¹)⁻¹*s := by group
        rw [heq]
        exact hm
      · exact le_of_eq (card_map_of_injective (MulAut.conj y).injective).symm
    have hYS : Y ≤ (S : Subgroup G) := hYN.trans hS.le
    have hp : IsPGroup 2 C := (S.isPGroup'.to_le hYS).to_quotient (pCore 2 Y)
    rcases hp.card_eq_or_dvd with hc | hc <;> rw [hfive] at hc <;> norm_num at hc
  have hp : IsPGroup 2 a.range := S.isPGroup'.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  have hn : Nat.card a.range ≠ 1 := by
    intro hc
    have hb : a.range = ⊥ := eq_bot_of_card_eq _ hc
    apply ha
    apply MonoidHom.ext
    intro u
    have hh : a u ∈ a.range := ⟨u,rfl⟩
    rwa [hb,mem_bot] at hh
  have hd : 2 ∣ Nat.card a.range := hp.card_eq_or_dvd.resolve_left hn
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G := a.range) 2 hd
  obtain ⟨u,hu⟩ := v.property
  have hv1 : (v : MulAut C) ≠ 1 := by
    intro hh
    have he : v=1 := Subtype.ext hh
    simp [he] at hv
  have hv2 : (v : MulAut C)^2=1 := by
    have hh : v^2=1 := by simpa only [hv] using pow_orderOf_eq_one v
    exact congrArg Subtype.val hh
  have hi : ∀ c : C, (v : MulAut C) c=c⁻¹ := by
    rcases MulAut.prime_involutive (by rw [hfive]; exact Nat.prime_five) (v : MulAut C)
      (fun c => congrArg (fun b : MulAut C => b c) hv2) with he | hi
    · exact (hv1 he).elim
    · exact hi
  refine ⟨u,u.property,?_⟩
  intro y hy
  let z : Y := (Y.normalizerMonoidHom ⟨u,hSY u.property⟩) ⟨y,hy⟩ * (⟨y,hy⟩ : Y)
  have hz : q z=1 := by
    change q ((Y.normalizerMonoidHom ⟨u,hSY u.property⟩) ⟨y,hy⟩ * (⟨y,hy⟩ : Y))=1
    rw [map_mul,←quotientAut_apply_mk]
    change a u (q ⟨y,hy⟩)*q ⟨y,hy⟩=1
    rw [hu,hi,inv_mul_cancel]
  exact mem_map_of_mem Y.subtype ((QuotientGroup.eq_one_iff z).mp hz)

end Theory.GroupTheory
