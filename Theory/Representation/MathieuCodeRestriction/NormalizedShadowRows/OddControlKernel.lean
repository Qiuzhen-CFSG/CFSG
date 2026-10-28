module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.ChiefKernel
public import Theory.GroupTheory.RelativeSylowFrattini

/-!
# Odd-normalizer control and kernels of reduced actions

A normal subgroup of H contained in M and centralizing V must be a two-group
when all nontrivial odd subgroups in that intersection have normalizer in M
and H is not contained in M. A Sylow subgroup at any odd divisor, together
with Frattini's argument, would put H in M.

If the common chief kernel maps onto the two-core of the whole action image,
this two-group kernel bound lifts to the common chief kernel. For a reduced
surjective action, that kernel is exactly the original two-core. The proofs
use the literal action maps, with no choice of a faithful replacement.
Source application: Aschbacher--Smith 3.1.9(6) and 8.2.2(1), together with
odd-normalizer control 4.4.3; the source adapter is EssentialKernel in Chapter8.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace MathieuCode.NormalizedShadowRows
variable {G : Type*} [Group G] [Finite G] {H M V : Subgroup G}

theorem normal_centralizing_kernel_twoGroup
    (K : Subgroup H) [K.Normal]
    (hKM : K.map H.subtype ≤ M)
    (hKC : K.map H.subtype ≤ centralizer (V : Set G))
    (hHM : ¬ H ≤ M)
    (hcontrol : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ M ⊓ centralizer (V : Set G) → Odd (Nat.card X) →
      normalizer (X : Set G) ≤ M) : IsPGroup 2 K := by
  classical
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpprime,hpdvd,_⟩ := Nat.mem_primeFactors.mp hp
  by_cases hp2 : p = 2
  · simpa only [hp2] using (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_refl 2,by decide⟩)
  let : Fact p.Prime := ⟨hpprime⟩
  let P : Sylow p K := Sylow.nonempty.some
  let XH : Subgroup H := (P : Subgroup K).map K.subtype
  let X : Subgroup G := XH.map H.subtype
  have hXK : X ≤ K.map H.subtype := map_mono (map_subtype_le _)
  have hne : X ≠ ⊥ := by
    intro he
    have hh := (XH.map_eq_bot_iff_of_injective H.subtype_injective).mp he
    exact P.ne_bot_of_dvd_card hpdvd
      (((P : Subgroup K).map_eq_bot_iff_of_injective K.subtype_injective).mp hh)
  have hodd : Odd (Nat.card X) := by
    let e1 := (P : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective
    let e2 := XH.equivMapOfInjective H.subtype H.subtype_injective
    have hcard : Nat.card X = Nat.card P := by
      calc
        Nat.card X = Nat.card XH := (Nat.card_congr e2.toEquiv).symm
        _ = Nat.card P := (Nat.card_congr e1.toEquiv).symm
    rw [hcard]
    obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact (hpprime.odd_of_ne_two hp2).pow
  have hNM := hcontrol X hne (le_inf (hXK.trans hKM) (hXK.trans hKC)) hodd
  have hfr := congrArg (fun B : Subgroup H => B.map H.subtype) P.normalizer_sup_eq_top
  rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype] at hfr
  have hnorm : (normalizer (XH : Set H)).map H.subtype ≤ normalizer (X : Set G) :=
    XH.le_normalizer_map H.subtype
  exact (hHM (hfr.symm.le.trans (sup_le (hnorm.trans hNM) hKM))).elim
section ActionReduction
variable {D W W' : Type*} [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup W'] [Module (ZMod 2) W']
  {ρ : Representation (ZMod 2) D W} {σ : Representation (ZMod 2) D W'}

theorem reduction_kernel_le
    (r : MathieuCode.NormalizedShadowRows.ActionImageReduction ρ σ) :
    (actionHom ρ).ker ≤ (actionHom σ).ker := by
  intro x hx
  change actionHom σ x = 1
  rw [← r.map_action x, show actionHom ρ x = 1 from hx, map_one, map_one]

theorem reduction_kernel_isPGroup
    (r : MathieuCode.NormalizedShadowRows.ActionImageReduction ρ σ)
    (hρ : IsPGroup 2 (actionHom ρ).ker) :
    IsPGroup 2 (actionHom σ).ker := by
  have hi : IsPGroup 2 ((actionHom σ).ker.map (actionHom ρ)) := by
    rw [actionHom_ker_eq, r.kernel_image]
    exact pCore_isPGroup
  have hh := hi.comap_of_ker_isPGroup (actionHom ρ) hρ
  rwa [comap_map_eq_self (reduction_kernel_le r)] at hh
end ActionReduction

section ReducedKernel
variable {D : Type*} [Group D]
omit [Finite G] in
theorem reduced_twoGroup_kernel_eq_core (q : H →* D)
    (hq : Function.Surjective q) (hD : pCore 2 D = ⊥)
    (hk : IsPGroup 2 q.ker) : q.ker = pCore 2 H := by
  have hle : q.ker ≤ pCore 2 H := le_sSup ⟨inferInstance,hk⟩
  apply le_antisymm hle
  have hm : (pCore 2 H).map q ≤ pCore 2 D :=
    le_sSup ⟨Subgroup.Normal.map inferInstance q hq, pCore_isPGroup.map q⟩
  rw [hD] at hm
  exact map_le_iff_le_comap.mp hm
end ReducedKernel

end MathieuCode.NormalizedShadowRows
