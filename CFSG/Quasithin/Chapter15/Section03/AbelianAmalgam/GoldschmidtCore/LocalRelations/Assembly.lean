module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalNormalizer
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.NormalizerControl
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.PrimeSupport
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.LocalQuotients
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Sylow

/-!
# The terminal local relations from the earlier source conclusions

The specified orthogonal action constructs the second singular four-group and
proves the residual product. Its finite normalizer calculation makes every
two-overgroup of `T_E` inside `M` equal to `T`; the residual product then gives
the generation premise of the maximal-local Sylow argument. Intrinsic local
quotients and the intersection follow from the earlier cubic residuals and
`S₃ × S₃` quotient. Baumann control gives the two ambient normalizer bounds,
and the earlier core identity gives relative Thompson normality.

The inputs below are genuine earlier conclusions of 15.3.2, 15.3.7,
15.3.66–67, including `M_E=Y_E T_E` proved on p.1154. In particular the
orthogonal action image, the source definite plane, `Z=Ω₁(Z(T))`, the actual
residual `Y`, and `R=C_G(V)=C_T(V)` are retained. None of the terminal line
product, local intersection, generation, or common-core conditions is an
input. The assembly of 15.3.68, including its separate centrality obligation,
remains with the parent module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122 and 1152–1155, PDF pp.1138–1139 and 1169–1172.
-/

public section

open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] [Finite G]

/-- Construct the terminal pair and all local relations from genuine earlier
source conclusions. Both finite orthogonal calculations are discharged. -/
theorem exists_terminal_local_relations
    (T : Sylow 2 G) (M Mc Y V R V₁ E : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hM : M = normalizer (V : Set G))
    (hY : Y = residualY M Mc)
    (hR : R = centralizer (V : Set G))
    (hRT : R = (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hMproduct : (M : Set G) = (Y : Set G) * (T : Set G))
    (hV₁ : V₁ ≤ V) (hV₁card : Nat.card V₁ = 4)
    (hdefinite : ∀ v : V₁, v ≠ 1 → ¬ d.singular ⟨v, hV₁ v.property⟩)
    (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hfour : Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)))
    (hEsingular : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (hZcard : Nat.card (centralInvolutions T) = 2)
    (hZE : centralInvolutions T ≤ E)
    (hS : (planeStabilizer T V₁).relIndex (T : Subgroup G) = 2)
    (hD : (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2)
    (hSD : planeStabilizer T V₁ ≠ lineT (T : Subgroup G) E)
    (himage : actionImage d Y = pResidual 2 OrthogonalFourBinary.TerminalLines.IsometryGroup)
    (hcore : twoCoreAmbient (Y ⊔ (T : Subgroup G)) = R)
    (hYquot : Nat.card (Y ⧸ pCore 2 Y) = 9 ∨ Nat.card (Y ⧸ pCore 2 Y) = 27)
    (hfirst : Nonempty (((lineY Y E ⊔ lineT (T : Subgroup G) E : Subgroup G) ⧸
      pCore 2 (lineY Y E ⊔ lineT (T : Subgroup G) E : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)))
    (hSylow : IsSylowSubgroupIn (lineT (T : Subgroup G) E) (lineNormalizer E))
    (hBaumann : ChapterB.baumann (lineT (T : Subgroup G) E) ≤ R)
    (hcontrol : (ChapterB.baumann (lineT (T : Subgroup G) E)).characteristicNormalizerClosure ≤ M)
    (hYN : ((lineY Y E).subgroupOf (lineNormalizer E)).Normal)
    (hYEq : Nonempty ((lineY Y E ⧸ pCore 2 (lineY Y E)) ≃* Multiplicative (ZMod 3)))
    (hXq : Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)))
    (hGEq : Nonempty ((lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hME : lineM M E = lineY Y E ⊔ lineT (T : Subgroup G) E)
    (hGEproduct : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineX E : Set G) * (lineT (T : Subgroup G) E : Set G))
    (hcomm : lineX E = ⁅lineX E, elementaryAbelianMaxJ R⁆)
    (hmaximal : IsMaximalTwoLocal M) (hXoutside : ¬ lineX E ≤ M) :
    ∃ s ∈ planeStabilizer T V₁, s ∉ lineT (T : Subgroup G) E ∧
      ∃ hFV : otherLine E s ≤ V,
        centralInvolutions T ≤ otherLine E s ∧
        Nat.card (otherLine E s) = 4 ∧
        Nonempty (otherLine E s ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
        (∀ f : otherLine E s, d.singular ⟨f, hFV f.property⟩) ∧
        otherLine E s ≠ E ∧
        lineT (T : Subgroup G) (otherLine E s) = lineT (T : Subgroup G) E ∧
        lineY Y (otherLine E s) = otherLine (lineY Y E) s ∧
        (Y : Set G) = (lineY Y E : Set G) * (lineY Y (otherLine E s) : Set G) *
          (twoCoreAmbient Y : Set G) ∧
        IsMulCommutative (actionImage d Y) ∧
        ((lineY Y E).subgroupOf (Y ⊔ lineT (T : Subgroup G) E)).Normal ∧
        (firstAmalgamGroup Y (T : Subgroup G) E (otherLine E s) : Set G) =
          (lineY Y (otherLine E s) : Set G) * (lineT (T : Subgroup G) E : Set G) ∧
        (secondAmalgamGroup (T : Subgroup G) E : Set G) =
          (lineX E : Set G) * (lineT (T : Subgroup G) E : Set G) ∧
        Nonempty ((firstAmalgamGroup Y (T : Subgroup G) E (otherLine E s) ⧸
          pCore 2 (firstAmalgamGroup Y (T : Subgroup G) E (otherLine E s))) ≃*
            Equiv.Perm (Fin 3)) ∧
        Nonempty ((secondAmalgamGroup (T : Subgroup G) E ⧸
          pCore 2 (secondAmalgamGroup (T : Subgroup G) E)) ≃* Equiv.Perm (Fin 3)) ∧
        firstAmalgamGroup Y (T : Subgroup G) E (otherLine E s) ⊓
          secondAmalgamGroup (T : Subgroup G) E = lineT (T : Subgroup G) E ∧
        M ⊓ normalizer (lineT (T : Subgroup G) E : Set G) = (T : Subgroup G) ∧
        lineY Y (otherLine E s) ⊔ (T : Subgroup G) = M ∧
        (∀ U : Subgroup G, U ≤ M → IsPGroup 2 U → lineT (T : Subgroup G) E < U →
          M ≤ lineY Y (otherLine E s) ⊔ U) ∧
        normalizer (lineT (T : Subgroup G) E : Set G) ≤ M ∧
        normalizer (elementaryAbelianMaxJ (lineT (T : Subgroup G) E) : Set G) ≤ M ∧
        ((elementaryAbelianMaxJ (lineT (T : Subgroup G) E)).subgroupOf
          (firstAmalgamGroup Y (T : Subgroup G) E (otherLine E s))).Normal ∧
        (∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3) ∧
        (∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer (otherLine E s : Set G)) →
          p = 2 ∨ p = 3) ∧
        (∀ K ∈ Theory.GroupTheory.maximalTwoLocalOvergroups
            (amalgamGroup Y (T : Subgroup G) E (otherLine E s)),
          IsSylowSubgroupIn (lineT (T : Subgroup G) E) K) := by
  have hYM : Y ≤ M := by
    rw [hY]
    exact Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hTM : (T : Subgroup G) ≤ M := by
    intro t ht
    rw [← SetLike.mem_coe, hMproduct]
    exact ⟨1, Y.one_mem, t, ht, one_mul t⟩
  have hnormal : (Y.subgroupOf M).Normal := by rw [hY]; exact residualY_normal M Mc
  have hMY := (normal_subgroupOf_iff_le_normalizer hYM).mp hnormal
  have hTY := hTM.trans hMY
  have hMjoin : M = Y ⊔ (T : Subgroup G) := by
    apply SetLike.coe_injective
    exact hMproduct.trans (coe_mul_of_right_le_normalizer_left _ _ hTY).symm
  obtain ⟨s, hs, hsE, hFV, hZF, hFcard, hFfour, hFsingular, hFE, hTF⟩ :=
    exists_other_singular_four T V M V₁ E d hTM hEV hEcard hfour hEsingular hZE hS hD hSD
  obtain ⟨hproduct, himageComm, hlocalNormal, _, hgenerate⟩ :=
    OrthogonalProducts.terminal_relations T M Mc Y V R V₁ E d hM hY hR hRT
      hMproduct hV₁ hV₁card hdefinite hEV hEcard hEsingular hZcard hZE himage s hs hsE
  have hNM := lineT_normalizer_eq d T R E hM (by rwa [← hM]) hEV hR hRT hD
  have hgenerateAll := lineT_generation_of_normalizer T M Y E (otherLine E s)
    hD hNM.le hgenerate.ge
  have hVC : V ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff_isMulCommutative.mpr
    exact ⟨⟨fun a b => d.coordinates.injective (by simp only [map_mul, mul_comm])⟩⟩
  have hCT : centralizer (V : Set G) ≤ (T : Subgroup G) :=
    hR.symm.le.trans (hRT.le.trans inf_le_left)
  have hED : E ≤ lineT (T : Subgroup G) E :=
    le_inf (hEV.trans (hVC.trans hCT)) E.le_normalizer
  have hEne : E ≠ ⊥ := (one_lt_card_iff_ne_bot E).mp (by rw [hEcard]; decide)
  have hElementary : IsElementaryAbelian 2 E := by
    obtain ⟨e⟩ := hfour
    refine {
      toIsMulCommutative := ⟨⟨fun a b => e.injective (by simp only [map_mul, mul_comm])⟩⟩
      exponent_dvd_p := ?_
    }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply e.injective
    rw [map_pow, map_one]
    exact (show ∀ w : Multiplicative (ZMod 2 × ZMod 2), w ^ 2 = 1 from by decide +kernel) _
  have hN := lineT_normalizer_bounds (T : Subgroup G) E M hEne hED hcontrol
  have hJB : elementaryAbelianMaxJ (lineT (T : Subgroup G) E) ≤
      ChapterB.baumann (lineT (T : Subgroup G) E) := by
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    intro j hj
    apply mem_centralizer_iff.mpr
    intro w hw
    obtain ⟨wJ, hwJ, rfl⟩ := hw
    obtain ⟨wZ, _, rfl⟩ := hwJ
    exact congrArg Subtype.val ((mem_center_iff.mp wZ.property) ⟨j, hj⟩).symm
  have hJnormal := firstAmalgam_thompson_normal M Y (T : Subgroup G) V E (otherLine E s)
    hYM hTM (by rw [hMjoin, hcore, hRT]) hEV (by rw [← hRT]; exact hJB.trans hBaumann)
  obtain ⟨U, hU⟩ := hSylow
  have hsecond := secondAmalgam_quotient (T : Subgroup G) V E U hU hEV hXq
    (by rw [← hRT]; exact hcomm)
  have hintersection := amalgam_intersection M Y (T : Subgroup G) E (otherLine E s)
    hYM hTM U hU hYN hYEq hXq hGEq hME hGEproduct
  have hsupport := local_prime_support T M Mc (by rw [← hY]; exact hMjoin)
    (by rw [← hY]; exact hMY) (by rw [← hY]; exact hYquot)
  exact ⟨s, hs, hsE, hFV, hZF, hFcard, hFfour, hFsingular, hFE, hTF,
    lineY_otherLine Y E s (hTY hs.1), hproduct, himageComm, hlocalNormal,
    firstAmalgam_product Y (T : Subgroup G) E (otherLine E s) hTY hTF,
    secondAmalgam_product (T : Subgroup G) E,
    firstAmalgam_quotient Y (T : Subgroup G) E s hs.1 hTY hD hfirst,
    hsecond, hintersection, hNM, hgenerate, hgenerateAll, hN.1, hN.2, hJnormal,
    hsupport, otherLine_centralizer_prime_support E s hGEq,
    amalgam_sylow_in_maximalLocals Y (T : Subgroup G) E (otherLine E s) M
      T.isPGroup' hTM hN.1 hmaximal hXoutside hgenerateAll⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
