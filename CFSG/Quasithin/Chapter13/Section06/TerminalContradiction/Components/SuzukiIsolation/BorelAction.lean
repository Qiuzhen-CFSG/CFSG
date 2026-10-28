module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ModuleIntersections
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Commutator.Action
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourcePair
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.Representation.BinaryPermutation.FiveOrbits
public import Theory.GroupTheory.PResidual.Quotient

/-!
# The Suzuki Borel residual fixes the original A₅ module

The cross-normalization clause of the genuine F.1.1 pair puts the Suzuki
Borel in N(L). Its centralization of the original marked line and the
trivial-intersection property of V then force it to normalize V. On the
original five-letter action it fixes a nonzero singular vector, whose
stabilizer has order twenty-four. Its three-prime order therefore makes
its image a two-group. The literal embedded two-residual consequently
centralizes V.

The final theorem applies this calculation to the actual normal component
of C_G(z), constructing its F.1.1 pair with the earlier source theorem.
This supplies an action prerequisite for the A₅–Suzuki exclusion; it does
not itself assert the mixed-pair classification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
5.2.2–6 (pp.646–651) and 13.6.27 (p.934), with the original marked A₅
module of Notation 13.2.1 and the TI calculation of 12.2.6.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- A three-prime subgroup of the marked point centralizer in N(L)
has its actual two-residual in C_G(V). -/
theorem threeFree_lineCentralizer_residual (H : Subgroup G)
    (hHN : H ≤ normalizer (L : Set G))
    (hHC : H ≤ centralizer (V₁ : Set G))
    (hthree : ¬ 3 ∣ Nat.card H) :
    (pResidual 2 H).map H.subtype ≤ centralizer (V : Set G) := by
  have hne : V₁ ≠ ⊥ := by
    intro he
    have hc := d.flag.one_card
    simp [he] at hc
  have hV₁V := d.flag.one_le_two.trans d.flag.two_le_V
  have hHNv : H ≤ normalizer (V : Set G) :=
    (le_inf hHN hHC).trans
      (inf_centralizer_le_normalizer_of_trivial_intersections
        d.trivial_intersections hne hV₁V)
  let f := d.flag.normalizerAction.comp (inclusion hHNv)
  obtain ⟨⟨z,hz⟩,hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun he => hz1 (Subtype.ext he)
  obtain ⟨x,hx⟩ := d.flag.module.range_eq.ge (hV₁V hz)
  have hx0 : x.toAdd ≠ 0 := by
    intro he
    have hx1 : x = 1 := he
    exact hz1' (hx.symm.trans (hx1 ▸ map_one _))
  have hxs : BinaryPermutation.FiveGeometry.form x.toAdd = 0 :=
    Section05.A5Source.Commutator.source_line_singular d.flag x.toAdd (hx ▸ hz)
  have hweight : BinaryPermutation.FiveOrbits.weight x.toAdd ≠ 2 := by
    intro hh
    exact ((BinaryPermutation.FiveOrbits.nonsingular_iff_weight_two x.toAdd).mpr hh) hxs
  have hstab : f.range ≤ BinaryPermutation.FiveOrbits.stabilizer x.toAdd := by
    rintro g ⟨a,rfl⟩
    change BinaryPermutation.coreRepresentation (Fin 5) (f a) x.toAdd = x.toAdd
    apply Multiplicative.ofAdd.injective
    apply d.flag.module.injective
    dsimp only [f, MonoidHom.comp_apply]
    rw [← d.flag.normalizer_equivariant]
    change a.val * d.flag.module.map x * a.val⁻¹ = d.flag.module.map x
    rw [hx]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp (hHC a.property) z hz).symm
  have hd24 : Nat.card f.range ∣ 24 := by
    have hd := card_dvd_of_le hstab
    rwa [BinaryPermutation.FiveOrbits.stabilizer_card, if_neg hx0, if_neg hweight] at hd
  have hcop : (Nat.card f.range).Coprime 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (fun hh => hthree (hh.trans (card_range_dvd f)))).symm
  have hp : IsPGroup 2 f.range :=
    IsPGroup.of_card_dvd_pow (n := 3)
      (hcop.dvd_mul_right.mp (show Nat.card f.range ∣ 8 * 3 from hd24))
  have hr := pResidual_le_ker_of_isPGroup 2 f.rangeRestrict hp
  rintro a ⟨b,hb,rfl⟩
  apply (Section05.A5Source.actor_eq_one_iff d.flag (inclusion hHNv b)).mp
  exact congrArg Subtype.val (hr hb)

/-- The Suzuki Borel of the genuine source pair fixes V through its
two-residual, using the original marked line and the concrete Suzuki quotient. -/
theorem suzuki_borel_residual_centralizes
    (A : Subgroup G) (hF : HypothesisF11 ![L,A] (T : Subgroup G))
    {z : G} (hz : zpowers z = V₁) (hAC : A ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    (pResidual 2 (borel A (T : Subgroup G))).map
      (borel A (T : Subgroup G)).subtype ≤ centralizer (V : Set G) := by
  apply threeFree_lineCentralizer_residual d
  · simpa [other] using hF.cross 0
  · have he : centralizer (V₁ : Set G) = centralizer ({z} : Set G) := by
      rw [←hz, zpowers_eq_closure, centralizer_closure]
    exact (borel_le A (T : Subgroup G)).trans (hAC.trans_eq he.symm)
  · intro hh
    exact BenderSuzuki.MatrixGroups.three_free_of_suzuki_core_quotient m hm e
      (hh.trans (card_dvd_of_le (borel_le A (T : Subgroup G))))

/-- The literal Borel-residual centralization for the extra normal Suzuki
component of C_G(z), with the F.1.1 input discharged by the actual source pair. -/
theorem component_borel_residual_centralizes
    {z : G} (hz : zpowers z = V₁)
    (D : Subgroup (centralizer ({z} : Set G))) [D.Normal]
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hout : ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G)) :
    let A := D.map (centralizer ({z} : Set G)).subtype
    (pResidual 2 (borel A (T : Subgroup G))).map
      (borel A (T : Subgroup G)).subtype ≤ centralizer (V : Set G) := by
  let eD := D.equivMapOfInjective (centralizer ({z} : Set G)).subtype
    (centralizer ({z} : Set G)).subtype_injective
  let eQ := QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)
  exact suzuki_borel_residual_centralizes d _
    (source_A5_suzuki_pair_F11 d hz D e hout h25) hz (map_subtype_le D)
    hm (eQ.symm.trans e)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
