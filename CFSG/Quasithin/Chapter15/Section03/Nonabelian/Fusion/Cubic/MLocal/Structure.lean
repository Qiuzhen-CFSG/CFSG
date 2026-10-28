module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.Actions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientAction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.LocalSylow

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.SylowArrangement

/-!
# The internal symmetric factor of the M-local cubic centralizer

For the actual source subgroups, `source_symmetric_factor` constructs a
Sylow three-subgroup D of C_M(V₁), a subgroup J isomorphic to S₄, and a
Sylow two-subgroup of J inside T. It proves C_M(D) = D × J internally,
with V₁ = O₂(J). Every involution of J outside V₁ fixes a hyperplane in V,
whereas no element of U does.

The explicit earlier-source inputs are the following:
* the prescribed natural orthogonal action and definite plane V₁;
* g in Y with Zᵍ not contained in V ∩ U, and U ≤ T ≤ H;
* relative normality of Y in M and C_Y(V) = O₂(Y), from 15.3.49(3);
* I = YU from 15.3.54(1), and V = Z(P) from 15.3.55;
* the actual two natural Omega constituents of P/V, with both Omega factors
  moving all of V, from 15.3.53(1) and 15.3.54(4), specialized to s = 1
  by 15.3.58(2);
* T_K Sylow in I, [T : T_K] = 2, and M = YT from 15.3.59(2–4);
* the elementary-four U-image distinct from the plane-stabilizer image,
  from 15.3.51(2a).

The quotient calculation gives C_P(D) = V₁ and C_M(V) = P. Coprime
centralizer lifting gives the full actor centralizer. Its companion-plane
projection splits off D, and the compatible natural-four extension gives
J and its actual two-core. Conjugation inside N_M(V₁) arranges its Sylow
subgroup inside T. The two fixed-space statements follow from the literal
orthogonal action. No centralizer splitting or fixed-space conclusion is
an input. The source assembly owner must supply the listed earlier
conclusions; final nonfusion assembly remains with MLocal and Cubic.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1146–1147, 15.3.53–55, and the setup of 15.3.60 on p.1150.
-/


@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
variable {G : Type*} [Group G]

/-- The symmetric cubic centralizer, its arranged Sylow subgroup, and both
actual fixed-space conclusions, from the enumerated earlier source inputs. -/
theorem source_symmetric_factor [Finite G] (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M (localModule T M))
    (i : OrthogonalPlaneIndex) (g : G) :
    let Z := centralInvolutions T
    let V := localModule T M
    let H := centralizerH Z
    let Y := residualY M H
    let V1 := d.plane i
    let ZS := fixedPlane V (planeStabilizer T V1)
    let U := closureU Z ZS
    let I := pairI Z ZS g
    let P := pairP Z ZS g
    let TK := residualSylow T Z
    ∀ (_hg : g ∈ Y) (_hmoving : ¬ rightConjugate Z g ≤ V ⊓ U)
      (hUT : U ≤ T) (_hTH : (T : Subgroup G) ≤ H)
      (_hMY : M ≤ normalizer (Y : Set G))
      (_hCY : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
      (hI : I = Y ⊔ U) (_hM : M = Y ⊔ (T : Subgroup G))
      (hcenter : V = (center P).map P.subtype)
      (S : Sylow 2 I) (_hS : (S : Subgroup I).map I.subtype = TK)
      (_hidx : TK.relIndex T = 2),
    let hIM : I ≤ M := hI.le.trans (sup_le (show Y ≤ M from map_subtype_le _) (hUT.trans hTM))
    letI := normal_lower_of_center hcenter
    ∀ (_r : NaturalQuotientPair d I P hIM (pairI_normalizes_pairP Z ZS g))
      (_hUelementary : IsElementaryAbelian 2 (d.image U))
      (_hUcard : Nat.card (d.image U) = 4)
      (_hUother : d.image U ≠ d.image (planeStabilizer T V1)),
    ∃ (PM3 : Sylow 3 (M ⊓ centralizer (V1 : Set G) : Subgroup G))
      (J : Subgroup G) (_ : J ≃* Equiv.Perm (Fin 4)) (Q : Sylow 2 J),
      let D := planeCubic M V1 PM3
      J ≤ M ∧ Disjoint D J ∧ D ≤ centralizer (J : Set G) ∧
      M ⊓ centralizer (D : Set G) = D ⊔ J ∧
      V1 = Stellmacher.twoCoreAmbient J ∧ factorSylow J Q ≤ (T : Subgroup G) ∧
      (∀ t ∈ J, orderOf t = 2 → t ∉ V1 → Nat.card (fixedPlane V (zpowers t)) = 8) ∧
      (∀ u ∈ U, Nat.card (fixedPlane V (zpowers u)) ≠ 8) := by
  intro Z V H Y V1 ZS U I P TK hg hmoving hUT hTH hMY hCY hI hM hcenter S hS hidx
    hIM r hUelementary hUcard hUother
  let : (V.subgroupOf P).Normal := normal_lower_of_center hcenter
  let : IsElementaryAbelian 2 (d.image U) := hUelementary
  have hp := LocalKernel.action_kernel_isTwoGroup T hTM
    (show Y ≤ M from map_subtype_le _) hMY hM hCY d
  have hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)) := by
    rw [← d.ker_actor]
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hkernel : ∀ PM3 : Sylow 3 (M ⊓ centralizer (V1 : Set G) : Subgroup G),
      (M ⊓ centralizer (planeCubic M V1 PM3 : Set G)) ⊓ centralizer (V : Set G) = V1 := by
    intro PM3
    obtain ⟨_, hk, _, hc, _, _⟩ := source_quotient_centralizer T M hTM d i g
      hg hmoving hUT hMY hCY hI hM hcenter S hS hidx r PM3
    calc
      _ = (M ⊓ centralizer (V : Set G)) ⊓
          centralizer (planeCubic M V1 PM3 : Set G) := by ac_rfl
      _ = V1 := by rw [hk, hc]
  let PM30 : Sylow 3 (M ⊓ centralizer (V1 : Set G) : Subgroup G) := Classical.choice inferInstance
  obtain ⟨J₀, e₀, hJ₀M, hd₀, hc₀, hs₀, hcore₀, _⟩ :=
    exists_symmetric_factor_of_cubic_kernel d hcop i PM30 (hkernel PM30)
  obtain ⟨PM3, J, e, hJM, hd, hc, hs, hcore, Q, hQT⟩ :=
    arrange_symmetric_factor d T hTM i PM30 J₀ e₀ hJ₀M hd₀ hc₀ hs₀ hcore₀
  have hJE : J ≤ M ⊓ centralizer (planeCubic M V1 PM3 : Set G) := by
    rw [hs]
    exact le_sup_right
  exact ⟨PM3, J, e, Q, hJM, hd, hc, hs, hcore, hQT,
    fun t ht ht2 hto => cubic_centralizer_involution_fixed d hcop i PM3 (hkernel PM3)
      t (hJE ht) ht2 hto,
    closureU_no_hyperplane d T hTM i Z ZS hUT hUcard hUother⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
