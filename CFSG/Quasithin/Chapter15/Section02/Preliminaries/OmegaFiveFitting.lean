module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaFive

/-!
# Sylow-invariant five-subgroups in the original Fitting layer

An order-five subgroup of the Fitting subgroup lies in the first omega
layer of the five-core. In the natural A.3.6 case the actual Sylow-two action
is irreducible on a plane of order twenty-five, excluding that subgroup.
In the nilpotent case the existing omega argument puts it in the central
Frattini line. Thus in both cases the subgroup is central.

This is the sufficient intrinsic conclusion for original15.2.4, printed
p.1107. Its source consumer applies it to the literal image of Y inside
L₁/O₂(L₁); residual lifting then supplies the normalizer contradiction.
No stronger elementary structure of the full five-core is asserted.
Source: Aschbacher--Smith, A.3.6, pp.43--45, and original15.2.4, p.1107.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalActions
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.OmegaFive
variable {K : Type*} [Group K] [Finite K]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem five_le_core (A : Subgroup K) (hc : Nat.card A = 5)
    (hA : A ≤ fittingSubgroup K) : A ≤ pCore 5 K := by
  have hp : IsPGroup 5 A := IsPGroup.of_card (p := 5) (n := 1) (by simpa using hc)
  let F := fittingSubgroup K
  let Q := A.subgroupOf F
  have hQ : IsPGroup 5 Q := hp.of_equiv (subgroupOfEquivOfLe hA).symm
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  have hmap : Q.map F.subtype = A := map_subgroupOf_eq_of_le hA
  rw [← hmap]
  exact (map_mono hS).trans (S.map_le_pCore inferInstance inferInstance 5)

private theorem five_le_omega (A : Subgroup K) (hc : Nat.card A = 5)
    (hA : A ≤ fittingSubgroup K) : A ≤ omegaCore 5 K := by
  have hP := five_le_core A hc hA
  intro a ha
  refine ⟨⟨a,hP ha⟩,Subgroup.subset_closure ?_,rfl⟩
  change (⟨a,hP ha⟩ : pCore 5 K) ^ (5 ^ 1) = 1
  apply Subtype.ext
  change a ^ (5 ^ 1) = 1
  simpa only [hc, pow_one, Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : A)))

private theorem natural_invariant_five_false
    (h : A36Natural K) (S : Sylow 2 K) (A : Subgroup K)
    (hc : Nat.card A = 5) (hA : A ≤ fittingSubgroup K)
    (hS : (S : Subgroup K) ≤ normalizer (A : Set K)) : False := by
  have hd : 5 ∣ Nat.card (fittingSubgroup K) := hc ▸ card_dvd_of_le hA
  let P := omegaCore 5 K
  let U := A.subgroupOf P
  let q := QuotientGroup.mk' (frattini P)
  have hAP : A ≤ P := five_le_omega A hc hA
  have hU : Nat.card U = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv).trans hc
  obtain ⟨_,he,hPcard⟩ := RadicalStructure.natural_core h hd
  let := he
  have hP : P = pCore 5 K := by
    dsimp only [P,omegaCore]
    rw [RadicalStructure.omega_top (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 5 (pCore 5 K))),
      ← MonoidHom.range_eq_map,range_subtype]
  let : IsElementaryAbelian 5 P := hP.symm ▸ he
  let : Fact (IsPGroup 5 P) := ⟨IsElementaryAbelian.isPGroup _ _⟩
  have hfr : frattini P = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := 5)
  have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
    rw [QuotientGroup.ker_mk',hfr])
  have hinv : ∀ (s : S) a, a ∈ U.map q → omegaFrattiniAction 5 K s a ∈ U.map q := by
    rintro s a ⟨u, hu, rfl⟩
    refine ⟨omegaCoreAction 5 K s u, ?_, ?_⟩
    · change ((omegaCoreAction 5 K s u : P) : K) ∈ A
      rw [omegaCoreAction_apply]
      exact (mem_normalizer_iff.mp (hS s.property) u).mp hu
    · dsimp only [q,P,omegaFrattiniAction,MonoidHom.comp_apply]
      rw [quotientAut_apply_mk]
  have hcard : Nat.card (U.map q) = 5 := by
    rw [card_map_of_injective hqi,hU]
  rcases natural_sylow_irreducible h hd S (U.map q) hinv with hb | ht
  · rw [hb,card_bot] at hcard
    norm_num at hcard
  · rw [ht,card_top] at hcard
    have hquot : Nat.card (P ⧸ frattini P) = 25 := by
      rw [hfr,Nat.card_congr (QuotientGroup.quotientBot (G := P)).toEquiv,hP,hPcard]
      norm_num
    omega

/-- The displayed A.3.6 alternatives centralize a Sylow-two-invariant
order-five subgroup of the Fitting subgroup. -/
public theorem fitting_invariant_five_le_center [Group.IsPerfect K]
    (h : A36Natural K ∨ A36Nilpotent K) (S : Sylow 2 K) (A : Subgroup K)
    (hc : Nat.card A = 5) (hA : A ≤ fittingSubgroup K)
    (hS : (S : Subgroup K) ≤ normalizer (A : Set K)) : A ≤ center K := by
  rcases h with h | h
  · exact (natural_invariant_five_false h S A hc hA hS).elim
  · exact invariant_five_le_center h (hc ▸ card_dvd_of_le hA) S A hc
      (five_le_omega A hc hA) hS

universe u
/-- The genuine noncentral A.3.6 producer supplies every structural premise. -/
public theorem cComponent_invariant_five_le_center
    {E : Type u} [Group E] [Finite E] {κ : GroupClass.{u}}
    (hE : IsSQTK κ E) (hO : pCore 2 E = ⊥) {C : Subgroup E}
    (hC : C.IsCComponent)
    (S : Sylow 2 C) (A : Subgroup C) (hc : Nat.card A = 5)
    (hA : A ≤ fittingSubgroup C) (hS : (S : Subgroup C) ≤ normalizer (A : Set C)) :
    A ≤ center C := by
  by_cases hn : fittingSubgroup C ≤ center C
  · exact hA.trans hn
  let := hC.perfect
  exact fitting_invariant_five_le_center
    (ChapterA.Section03.NoncentralFitting.structure_of_noncentral hE hO hC hn).1
    S A hc hA hS

/-- Intrinsic form for the original quotient L₁/O₂(L₁), retaining its
actual Sylow subgroup and order-five Fitting subgroup. -/
public theorem top_cComponent_invariant_five_le_center {Q : Type u} [Group Q] [Finite Q] {κ : GroupClass.{u}}
    (hQ : IsSQTK κ Q) (hO : pCore 2 Q = ⊥)
    (htop : (⊤ : Subgroup Q).IsCComponent)
    (S : Sylow 2 Q) (A : Subgroup Q) (hc : Nat.card A = 5)
    (hA : A ≤ fittingSubgroup Q) (hS : (S : Subgroup Q) ≤ normalizer (A : Set Q)) :
    A ≤ center Q := by
  let e : Q ≃* (⊤ : Subgroup Q) := topEquiv.symm
  let P : Sylow 2 (⊤ : Subgroup Q) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let B := A.map e.toMonoidHom
  have hBc : Nat.card B = 5 := by
    rw [card_map_of_injective e.injective,hc]
  have hBF : B ≤ fittingSubgroup (⊤ : Subgroup Q) := by
    apply (map_mono hA).trans
    exact le_sSup ⟨(inferInstance : (fittingSubgroup Q).Normal).map _ e.surjective,
      Group.nilpotent_of_mulEquiv (e.subgroupMap (fittingSubgroup Q))⟩
  have hPB : (P : Subgroup (⊤ : Subgroup Q)) ≤ normalizer (B : Set (⊤ : Subgroup Q)) := by
    change (S : Subgroup Q).map e.toMonoidHom ≤ normalizer (B : Set (⊤ : Subgroup Q))
    have hh := map_mono (f := e.toMonoidHom) hS
    rwa [map_normalizer_eq_of_bijective _ e.bijective] at hh
  have hz := cComponent_invariant_five_le_center hQ hO htop P B hBc hBF hPB
  intro a ha
  have he := hz (mem_map_of_mem e.toMonoidHom ha)
  apply mem_center_iff.mpr
  intro q
  exact e.injective (mem_center_iff.mp he (e q))

end CFSG.Quasithin.Chapter15.Section02.OmegaFive
