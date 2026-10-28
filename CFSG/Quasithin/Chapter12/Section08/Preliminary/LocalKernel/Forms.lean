module
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.LocalKernel.Closure
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.SmallFrattiniForms.LinearApplication
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.Geometry
/-!
# The marked commutator form supplied by the early local theorem

In the nonabelian branch Φ(U) is nontrivial and lies in the order-two point,
so equals that point intrinsically. The finite-two-group Frattini formulas
give both commutator and square bounds. Transporting the existing binary
commutator form along this literal equality supplies the exact form consumed
by the center calculations, without any elementary-center assumption.

Source: Aschbacher--Smith, the paragraph preceding 12.8.8 and 12.8.8(2),
printed pp.851--852.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
variable {K : GroupClass} (hG : IsSimpleQTKE K G)
    (L M : Subgroup G) (hn : 2 ≤ n)
    (hVT : V ≤ (T : Subgroup G)) (hLV : L ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hres : pResidual 2 L = ⊤)
    (hnatural : 3 ≤ n → Nonempty (AmbientNaturalMarking L hLV n))
    (hescape : ¬ F.H ≤ M)

section Source
include hG hn hVT hLV hTL hres hnatural hescape

/-- Nonabelianness turns the source Frattini bound into the literal equality. -/
theorem localKernel_frattini_eq_point (hne : ¬ IsMulCommutative F.U) :
    frattini F.U = (F.Vi 1).subgroupOf F.U := by
  have hJ := F.H_mem_Hz (by omega) L M hescape
  have htwo := F.localKernel_UH_isPGroup hG L M F.H hn hVT hLV hTL hres hnatural hJ
  let : Fact (IsPGroup 2 F.U) := ⟨htwo⟩
  have hb := (F.localKernel_closure hG L M F.H hn hVT hLV hTL hres hnatural hJ).2.1
  have hle : frattini F.U ≤ (F.Vi 1).subgroupOf F.U :=
    fun u hu => hb (mem_map_of_mem F.U.subtype hu)
  have hp : Nat.card ((F.Vi 1).subgroupOf F.U) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))).toEquiv).trans
      (by simpa using F.card 1 (by omega))
  have hd : Nat.card (frattini F.U) ∣ 2 := hp ▸ card_dvd_of_le hle
  have hcard : Nat.card (frattini F.U) = 2 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with he | he
    · have helem := (frattini_eq_bot_iff_isElementaryAbelian (R := F.U) (p := 2)).mp
        ((frattini F.U).eq_bot_of_card_eq he)
      exact False.elim (hne helem.toIsMulCommutative)
    · exact he
  exact eq_of_le_of_card_ge hle (by rw [hp, hcard])

/-- The source square and commutator bounds follow from the finite-group Frattini formulas. -/
theorem localKernel_commutator_squares :
    ⁅F.U, F.U⁆ ≤ F.Vi 1 ∧ ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1 := by
  have hJ := F.H_mem_Hz (by omega) L M hescape
  have htwo := F.localKernel_UH_isPGroup hG L M F.H hn hVT hLV hTL hres hnatural hJ
  let : Fact (IsPGroup 2 F.U) := ⟨htwo⟩
  have hb := (F.localKernel_closure hG L M F.H hn hVT hLV hTL hres hnatural hJ).2.1
  constructor
  · rw [← F.U.map_subtype_commutator]
    exact (map_mono (commutator_le_frattini_of_isPGroup (R := F.U) (p := 2))).trans hb
  · intro u hu
    exact hb (mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u, hu⟩ : F.U)))

end Source

/-- This transport retains the original point, rather than choosing a new abstract line. -/
noncomputable def localKernel_pointFrattiniEquiv
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) : F.Vi 1 ≃* frattini F.U :=
  (subgroupOfEquivOfLe ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))).symm.trans
    (MulEquiv.subgroupCongr hphi.symm)

/-- Pack the previously constructed bilinear form into the exact center-consumer interface. -/
noncomputable def localKernel_markedForm [IsElementaryAbelian 2 F.Uhat]
    (hn : 1 ≤ n) (htwo : IsPGroup 2 F.U)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hc : ⁅F.U, F.U⁆ ≤ F.Vi 1) : F.UhatCommutatorForm hc where
  valueEquiv := (F.localKernel_pointFrattiniEquiv hphi).trans
    (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi))
  form := F.uhatBilinearForm hn htwo hphi
  nondegenerate := F.uhatBilinearForm_nondegenerate hn htwo hphi
  alternating := F.uhatBilinearForm_isAlt hn htwo hphi
  evaluation a b := by
    rw [F.uhatBilinearForm_apply]
    apply congrArg (fun x : frattini F.U =>
      (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi) x).toAdd)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (F.uhatCommutator_apply_mk htwo a b)
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
