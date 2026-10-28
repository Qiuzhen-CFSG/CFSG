module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralQuotient
public import GorensteinWalter.PSL2Cardinality
public import Theory.GroupAction.PerfectCentralQuotient
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.ReePlacement
public import Theory.SpecificGroups.ReeF4.LinearLocalFixer

/-!
# Excluding the embedded Ree point configuration

The intrinsic quotient of the original smaller component is preserved by
the containing central quotient. Three-divisibility therefore places its
actual image in the linear Ree residual. Every element of the opposite
moved elementary subgroup induces an involutory automorphism fixing that
residual, hence the identity. Faithfulness of the central-quotient action
lifts this to centralization of the original overcomponent, contradicting
the source moved-normalizer bound.

A binary rank-one quotient supplies the required factor three. This closes
its remaining Ree branch in Quasisimple.Source, retaining all module rows
and vectors fixed by the component. No irreducibility, generation bound or
point-inspection premise is added.
Source: Aschbacher–Smith 10.2.9, printed pp.750–751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02 ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- Full-Sylow placement of the literal central image in the Ree linear residual. -/
theorem ree_placement [IsQuasisimple I]
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {m : ℕ} (hm : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) :
    ∃ f : (I ⧸ center I) ≃* ReeF4.Model m,
      (L.subgroupOf I).map (f.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        ReeF4.Parabolics.localFactor m .linear := by
  obtain ⟨S,_,hB,hSN,_,hproper,_⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let A := B.map eI.toMonoidHom
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsSimpleGroup (ReeF4.Model m) := eI.symm.isSimpleGroup
  let : Group.IsSolvable eI.toMonoidHom.ker := by
    rw [eI.toMonoidHom.ker_eq_bot_iff.mpr eI.injective]
    infer_instance
  have hA : A ∈ localCComponents (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB eI.toMonoidHom
  have hp : A ≠ ⊤ := by
    intro ht
    apply hproper
    apply map_injective (f := eI.toMonoidHom) eI.injective
    rw [map_top_of_surjective _ eI.surjective]
    exact ht
  have hAN : (R.mapSurjective (f := eI.toMonoidHom) eI.surjective :
      Subgroup (ReeF4.Model m)) ≤ normalizer (A : Set _) :=
    (map_mono hSN).trans (le_normalizer_map eI.toMonoidHom)
  have h3A : 3 ∣ Nat.card A := by
    have hc := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le eI).toEquiv
    have hd := (hc ▸ h3).trans (card_quotient_dvd_card
      (pCore 2 ((L.subgroupOf I).map (eI.toMonoidHom.comp q))))
    simpa only [A,B,q,map_map] using hd
  obtain ⟨g,hg⟩ := ReePlacement.local_placement hm
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hA hp hAN h3A
  refine ⟨eI.trans (MulAut.conj g), ?_⟩
  have he : (eI.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp eI.toMonoidHom := by ext; rfl
  simpa only [A,B,q,map_map,he,MonoidHom.comp_assoc] using hg

/-- The opposite elementary moved factor centralizes the actual Ree overcomponent. -/
theorem ree_common_centralizer [IsQuasisimple I]
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {m : ℕ} (hm : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  obtain ⟨f,hf⟩ := ree_placement D c h3 hm eI
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsSimpleGroup (ReeF4.Model m) := f.symm.isSimpleGroup
  let : Group.IsPerfect (ReeF4.Model m) := Group.IsPerfect.ofSurjective
    (f := f.toMonoidHom) f.surjective
  let := source_original_full_moved_elementary D
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  intro u hu
  let a : MulAut I := I.normalizerMonoidHom ⟨u, partner_normalizes D c hu⟩
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := U) u hu
  have ha2 : a ^ 2 = 1 := by
    change (I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩) ^ 2 = 1
    rw [← map_pow]
    have he : (⟨u,partner_normalizes D c hu⟩ : normalizer (I : Set G)) ^ 2 = 1 := Subtype.ext hu2
    rw [he,map_one]
  have hfix : ∀ x ∈ ReeF4.Parabolics.localFactor m .linear,
      MulAut.centralQuotientAction f a x = x := by
    rw [←hf]
    rintro _ ⟨l,hl,rfl⟩
    change MulAut.centralQuotientAction f a (f (QuotientGroup.mk' (center I) l)) =
      f (QuotientGroup.mk' (center I) l)
    rw [MulAut.centralQuotientAction_apply]
    have ha : a l = l := by
      apply Subtype.ext
      change u * l.val * u⁻¹ = l.val
      exact mul_inv_eq_iff_eq_mul.mpr (c.crossed hu l.val hl).symm
    rw [ha]
  have hqa : MulAut.centralQuotientAction f a = 1 :=
    ReeF4.LinearLocalFixer.eq_one_of_fixes_linearLocal hm _
      (by rw [← map_pow,ha2,map_one]) hfix
  have ha : a = 1 := MulAut.centralQuotientAction_injective f
    (hqa.trans (map_one _).symm)
  intro i hi
  have hh := congrArg (fun b : MulAut I => (b ⟨i,hi⟩ : G)) ha
  change u * i * u⁻¹ = i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The source moved-normalizer bound excludes the Ree overcomponent. -/
theorem not_ree_of_three [IsQuasisimple I]
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {m : ℕ} (hm : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) : False :=
  source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer I
    c.escapes (ree_common_centralizer D c h3 hm eI)

/-- The actual binary rank-one quotient supplies the cubic divisor needed for Ree placement. -/
theorem not_ree_of_binary_quotient [IsQuasisimple I]
    {n : ℕ} (_hn : 0 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {m : ℕ} (hm : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) : False := by
  apply not_ree_of_three D c _ hm eI
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let d := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  rw [Nat.card_congr d.toEquiv,GorensteinWalter.sl2_card_formula,hF]
  have hpos : 1 ≤ (2 ^ n) ^ 2 := one_le_pow₀ (one_le_pow₀ (by decide : (1 : ℕ) ≤ 2))
  have hmod : (2 ^ n) ^ 2 % 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num [Nat.pow_mod]
  have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by omega
  exact dvd_mul_of_dvd_right h3 _

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
