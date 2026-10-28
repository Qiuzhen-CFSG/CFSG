module

public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ThreeResidual
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding

/-!
# The supercritical Frattini action for F.6.16

The actual prime-to-three quotient of the SQTK cover has three-rank at
most two. Noncyclicity of its three-core forces rank exactly two, so a
supercritical subgroup has one of the elementary-nine or Heisenberg
models. Its literal Frattini action embeds in GL₂(3), and the three-residual
of the action kernel centralizes the original three-core.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
A.1.25 and F.6.16, printed pp.25, 308–309 (1 March 2004 manuscript).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
universe u
variable {G Ghat : Type u} [Group G] [Finite G] [Group Ghat] [Finite Ghat]

/-- Killing the prime-to-three core also kills the two-core. -/
theorem twoCore_eq_bot_of_primeToThreeCore_eq_bot
    (hprime : pPrimeCore 3 G = ⊥) : pCore 2 G = ⊥ := by
  exact le_bot_iff.mp (twoCore_le_primeToThreeCore.trans hprime.le)

/-- The actual source cover supplies the two-core hypothesis. -/
theorem twoCore_eq_bot_of_cover (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat)) :
    pCore 2 G = ⊥ :=
  twoCore_eq_bot_of_primeToThreeCore_eq_bot (primeToThreeCore_eq_bot_of_quotient e)

/-- The prime-to-three quotient preserves the source three-rank bound. -/
theorem three_rank_le_two_of_cover {K : GroupClass.{u}}
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat)) :
    primeRank 3 G ≤ 2 := by
  rw [primeRank_congr 3 e]
  exact (primeRank_quotient_le_of_coprime 3 _ pPrimeCore_coprime_card).trans
    (hhat.stronglyQuasithin 3 Nat.prime_three (by decide))

private theorem three_core_rank (hr : primeRank 3 G ≤ 2)
    (hn : ¬ IsCyclic (pCore 3 G)) : primeRank 3 (pCore 3 G) = 2 := by
  have hle := (primeRank_subgroup_le 3 (pCore 3 G)).trans hr
  have hgt : ¬ primeRank 3 (pCore 3 G) ≤ 1 := by
    intro hr1
    apply hn
    apply (pCore_isPGroup (p := 3) (G := G)).isCyclic_of_odd_of_elementary_card_le (by decide)
    intro E hE
    let : IsElementaryAbelian 3 E := hE
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr1 E
  omega

/-- Construct the actual supercritical subgroup and its rank-two models. -/
theorem exists_three_core_supercritical (hr : primeRank 3 G ≤ 2)
    (hn : ¬ IsCyclic (pCore 3 G)) :
    ∃ X : Subgroup (pCore 3 G), IsSupercriticalPSubgroup 3 X ∧
      primeRank 3 X = 2 ∧
      ((Nat.card X = 9 ∧ Nonempty (X ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))) ∨
       (Nat.card X = 27 ∧ IsExtraspecial 3 X ∧ Nonempty (X ≃* HeisenbergPrime 3))) := by
  have hrP := three_core_rank hr hn
  have hnt : Nontrivial (pCore 3 G) := by
    by_contra h
    let : Subsingleton (pCore 3 G) := not_nontrivial_iff_subsingleton.mp h
    exact hn inferInstance
  let : Nontrivial (pCore 3 G) := hnt
  obtain ⟨X, hX⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_supercriticalPSubgroup (by decide)
  obtain ⟨hrX, hmodel⟩ := ChapterA.lemma_A_1_25_1 (by decide : Odd 3)
    pCore_isPGroup hrP.le X hX
  have hrX' : primeRank 3 X = 2 := hrX.trans hrP
  refine ⟨X, hX, hrX', ?_⟩
  rcases hmodel with hcyc | hm
  · let : IsCyclic X := isCyclic_of_prime_card hcyc.1
    have hle : primeRank 3 X ≤ 1 := (primeRank_le_iff_elementary_card_le X).mpr (fun E hE => by
      have hd : Nat.card E ∣ 3 := E.card_subgroup_dvd_card.trans hcyc.1.dvd
      simpa using Nat.le_of_dvd (by decide : 0 < 3) hd)
    omega
  · exact hm

/-- The literal supercritical Frattini action has a matrix realization and
its three-residual kernel centralizes the whole original three-core. -/
theorem supercritical_ternary_action
    (hr : primeRank 3 G ≤ 2) (X : Subgroup (pCore 3 G))
    (hX : IsSupercriticalPSubgroup 3 X) :
    letI : X.Characteristic := hX.characteristic
    ∃ j : MulAut (X ⧸ frattini X) →*
        Matrix.GeneralLinearGroup (Fin 2) (ZMod 3),
      Function.Injective j ∧
      let f := j.comp ((quotientAut (frattini X)).comp
        ((MulAut.characteristic X).comp (MulAut.conjNormal : G →* MulAut (pCore 3 G))))
      ((pResidual 3 f.ker).map f.ker.subtype) ≤ centralizer (pCore 3 G : Set G) := by
  let : X.Characteristic := hX.characteristic
  let : Fact (IsPGroup 3 X) := ⟨pCore_isPGroup.to_subgroup X⟩
  let : IsElementaryAbelian 3 (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
  obtain ⟨j, hj⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (X ⧸ frattini X) (ChapterA.lemma_A_1_25_frattini_card (by decide : Odd 3)
      pCore_isPGroup ((primeRank_subgroup_le 3 (pCore 3 G)).trans hr) X hX)
  refine ⟨j, hj, ?_⟩
  let a := (quotientAut (frattini X)).comp (MulAut.characteristic X)
  let c : G →* MulAut (pCore 3 G) := MulAut.conjNormal
  let f := j.comp (a.comp c)
  have hker : f.ker = (a.comp c).ker := MonoidHom.ker_comp_of_injective _ _ hj
  let b : f.ker →* a.ker := (c.comp f.ker.subtype).codRestrict a.ker (fun g => by
    change c g ∈ a.ker
    exact show g.val ∈ (a.comp c).ker from hker ▸ g.property)
  have hb : IsPGroup 3 (f.ker ⧸ b.ker) :=
    ((hX.isPGroup_frattini_action_kernel pCore_isPGroup (by decide)).to_subgroup b.range).of_equiv
      (QuotientGroup.quotientKerEquivRange b).symm
  have hres : pResidual 3 f.ker ≤ b.ker := sInf_le ⟨inferInstance, hb⟩
  change (pResidual 3 f.ker).map f.ker.subtype ≤ _
  rintro _ ⟨g, hg, rfl⟩
  have hb1 : b g = 1 := hres hg
  have hc1 : c g = 1 := congrArg Subtype.val hb1
  intro y hy
  have he := congrArg (fun z : MulAut (pCore 3 G) => (z ⟨y, hy⟩ : G)) hc1
  change g.val * y * g.val⁻¹ = y at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.ChapterF.Noncyclic
