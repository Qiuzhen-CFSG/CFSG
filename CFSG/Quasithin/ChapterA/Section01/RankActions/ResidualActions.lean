module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.ResidualActions.LinearInputs
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ResidualActions.LinearNormalizers
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ResidualActions.OddCore
public import CFSG.Quasithin.Defs
public import Theory.Quasithin.Rank
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Residual two-subgroup actions on odd prime cores

Compose conjugation on an odd prime core with its small-rank representation.
The linear normalizer calculation kills the image of a subgroup V = [V,X].
Its remaining automorphism image is both a two-group and a subgroup of the
odd p-group kernel, so V centralizes the prime core itself. For solvable
strongly quasithin groups, passing to the quotient by O₂(H) and using Fitting
self-centralization then absorbs V into O₂(H).

The final implications instantiate both proved linear normalizer calculations.
Their names display the remaining universal representation and A.1.9 inputs;
the earlier reductions retain their explicit linear inputs for compatibility.
The source-theorem assembly must supply the representation in both parts and
A.1.9 in part (1). Part (2) needs only solvability and strong quasithinness,
so its SQTK specialization requires no model recognition.
Source: Aschbacher–Smith, A.1.26, printed pp.25–26.
-/

public section

namespace CFSG.Quasithin.ChapterA.RankActions

open Subgroup

universe u

variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
private theorem centralizes_of_trivial_linear_image
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (P V : Subgroup H) [P.Normal]
    (hV : IsPGroup 2 V)
    (f : MulAut P →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (hf : IsPGroup p f.ker)
    (hz : V.map (f.comp (MulAut.conjNormal : H →* MulAut P)) = ⊥) :
    V ≤ centralizer (P : Set H) := by
  let c : H →* MulAut P := MulAut.conjNormal
  have hk : V.map c ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp (by
    simpa only [map_map] using hz)
  have hd : Disjoint (V.map c) f.ker :=
    (hV.map c).disjoint_of_coprime hf (Nat.coprime_two_left.mpr hp)
  have hzero : V.map c = ⊥ := le_bot_iff.mp
    ((le_inf le_rfl hk).trans hd.le_bot)
  have hc := (Subgroup.map_eq_bot_iff _).mp hzero
  rwa [MulAut.conjNormal_ker_eq_centralizer P] at hc

/-- The elementary branch centralizes every small-rank odd normal p-subgroup.
Only the two displayed universal inputs remain. -/
theorem centralizes_odd_normal_pGroup_of_representation_and_elementaryNormalizer
    (hrep : SmallRankAutomorphismRepresentation.{u})
    (hlin : ElementaryTwoLinearNormalizer)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (P X V : Subgroup H) [P.Normal]
    (hP : IsPGroup p P) (hrank : primeRank p P ≤ 2)
    (hX : pResidual 2 X = ⊤) (hV : IsPGroup 2 V)
    (hphi : frattini V = ⊥) (hcomm : V = ⁅V, X⁆) :
    V ≤ centralizer (P : Set H) := by
  let : Fact (IsPGroup 2 V) := ⟨hV⟩
  let : IsElementaryAbelian 2 V :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  obtain ⟨f, hf⟩ := hrep p hp P hP hrank
  let g := f.comp (MulAut.conjNormal : H →* MulAut P)
  have hgen : V.map g = ⁅V.map g, X.map g⁆ := by
    rw [← map_commutator, ← hcomm]
  have hx : IsPPerfect 2 (X.map g) :=
    ((pResidual_eq_top_iff 2 X).mp hX).of_surjective
      (g.subgroupMap X) (g.subgroupMap_surjective X)
  have hnorm : X.map g ≤ normalizer (V.map g : Set _) :=
    le_normalizer_iff_commutator_le_left.mpr hgen.ge
  exact centralizes_of_trivial_linear_image hp P V hV f hf
    (hgen.trans (hlin p hp _ _ hx (IsElementaryAbelian.map g) hnorm))

/-- The {2,3}-residual branch centralizes every small-rank odd normal
p-subgroup, without an elementary abelian hypothesis on V. -/
theorem centralizes_odd_normal_pGroup_of_representation_and_twoNormalizer
    (hrep : SmallRankAutomorphismRepresentation.{u}) (hlin : TwoLinearNormalizer)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (P X V : Subgroup H) [P.Normal]
    (hP : IsPGroup p P) (hrank : primeRank p P ≤ 2)
    (hX : piResidual twoThreePrimes X = ⊤) (hV : IsPGroup 2 V)
    (hcomm : V = ⁅V, X⁆) : V ≤ centralizer (P : Set H) := by
  obtain ⟨f, hf⟩ := hrep p hp P hP hrank
  let g := f.comp (MulAut.conjNormal : H →* MulAut P)
  have hgen : V.map g = ⁅V.map g, X.map g⁆ := by
    rw [← map_commutator, ← hcomm]
  have hx : IsPiPerfect twoThreePrimes (X.map g) :=
    ((piResidual_eq_top_iff twoThreePrimes X).mp hX).of_surjective
      (g.subgroupMap X) (g.subgroupMap_surjective X)
  have hnorm : X.map g ≤ normalizer (V.map g : Set _) :=
    le_normalizer_iff_commutator_le_left.mpr hgen.ge
  exact centralizes_of_trivial_linear_image hp P V hV f hf
    (hgen.trans (hlin p hp _ _ hx (hV.map g) hnorm))

private theorem two_subgroup_eq_bot_of_centralizes_odd_pCores
    [Group.IsSolvable H] (hcore : pCore 2 H = ⊥) (V : Subgroup H)
    (hV : IsPGroup 2 V)
    (hc : ∀ (p : ℕ) [Fact p.Prime], Odd p →
      V ≤ centralizer (pCore p H : Set H)) : V = ⊥ := by
  have hfit : V ≤ centralizer (fittingSubgroup H : Set H) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro q
    have hp := Nat.prime_of_mem_primeFactors q.val.property
    let : Fact q.val.val.Prime := ⟨hp⟩
    rcases hp.eq_two_or_odd with h2 | ho
    · rw [h2, hcore]
      intro v _ y hy
      have : y = 1 := hy
      simp [this]
    · exact hc _ (Nat.odd_iff.mpr ho)
  have hle : V ≤ pPrimeCore 2 H :=
    hfit.trans ((centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
      inferInstance).trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))
  obtain ⟨n, hn⟩ := hV.exists_card_eq
  have hd : Disjoint V (pPrimeCore 2 H) := disjoint_of_coprime_natCard (by
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := H)).pow_left n)
  exact le_bot_iff.mp ((le_inf le_rfl hle).trans hd.le_bot)

/-- A.1.26(2), conditional only on the small-rank automorphism representation
and the explicit GL₂ normalizer calculation. Strong quasithinness and
solvability suffice; no recognition or K-group hypothesis is used. -/
theorem twoCore_containment_of_representation_and_twoNormalizer
    (hrep : SmallRankAutomorphismRepresentation.{u}) (hlin : TwoLinearNormalizer)
    [Group.IsSolvable H] (hsqt : IsStronglyQuasithin H)
    (X V : Subgroup H) (hX : piResidual twoThreePrimes X = ⊤)
    (hV : IsPGroup 2 V) (hcomm : V = ⁅V, X⁆) : V ≤ pCore 2 H := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcore : pCore 2 (H ⧸ pCore 2 H) = ⊥ := by
    have hm := congrArg (map q) (q.comap_pCore_of_ker_isPGroup hq hk)
    rw [map_comap_eq_self_of_surjective hq] at hm
    exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  have hx : piResidual twoThreePrimes (X.map q) = ⊤ :=
    (piResidual_eq_top_iff _ _).mpr
      (((piResidual_eq_top_iff _ _).mp hX).of_surjective
        (q.subgroupMap X) (q.subgroupMap_surjective X))
  have hgen : V.map q = ⁅V.map q, X.map q⁆ := by
    rw [← map_commutator, ← hcomm]
  have hz : V.map q = ⊥ := by
    apply two_subgroup_eq_bot_of_centralizes_odd_pCores hcore _ (hV.map q)
    intro p _ hp
    apply centralizes_odd_normal_pGroup_of_representation_and_twoNormalizer
      hrep hlin hp _ (X.map q) _ pCore_isPGroup ?_ hx (hV.map q) hgen
    exact ((Theory.GroupTheory.primeRank_le_of_injective p
      (pCore p (H ⧸ pCore 2 H)).subtype Subtype.val_injective).trans
      (primeRank_quotient_le_of_isTwoGroup p hp (pCore 2 H) pCore_isPGroup)).trans
      (hsqt p Fact.out hp)
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz

/-- A.1.26(1) with exactly the displayed universal representation, linear
normalizer, and A.1.9 inputs. The conclusion concerns the entire odd core. -/
theorem oddCore_centralization_of_representation_elementaryNormalizer_and_fStarInput
    (hrep : SmallRankAutomorphismRepresentation.{u})
    (hlin : ElementaryTwoLinearNormalizer) (hfaith : PGroupFStarCentralizationInput.{u})
    (X V : Subgroup H) (hX : pResidual 2 X = ⊤) (hV : IsPGroup 2 V)
    (hcomm : V = ⁅V, X⁆) (hphi : frattini V = ⊥)
    (hrank : ∀ (p : ℕ) [Fact p.Prime], Odd p → primeRank p (pCore p H) ≤ 2) :
    ⁅V, pPrimeCore 2 H⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply centralizes_oddCore_of_pCores_and_fStarInput hfaith V hV
  intro p _ hp
  exact centralizes_odd_normal_pGroup_of_representation_and_elementaryNormalizer
    hrep hlin hp (pCore p H) X V pCore_isPGroup (hrank p hp) hX hV hphi hcomm

/-- A.1.26(1), with the GL₂ normalizer calculation discharged. The remaining
universal inputs are the small-rank representation from A.1.25(2) and the exact
A.1.9 centralization implication. The odd core is the full O(H). -/
theorem oddCore_centralization_of_representation_and_fStarInput
    (hrep : SmallRankAutomorphismRepresentation.{u})
    (hfaith : PGroupFStarCentralizationInput.{u})
    (X V : Subgroup H) (hX : pResidual 2 X = ⊤) (hV : IsPGroup 2 V)
    (hcomm : V = ⁅V, X⁆) (hphi : frattini V = ⊥)
    (hrank : ∀ (p : ℕ) [Fact p.Prime], Odd p → primeRank p (pCore p H) ≤ 2) :
    ⁅V, pPrimeCore 2 H⁆ = ⊥ :=
  oddCore_centralization_of_representation_elementaryNormalizer_and_fStarInput
    hrep elementaryTwoLinearNormalizer hfaith X V hX hV hcomm hphi hrank

/-- A.1.26(2) for a solvable strongly quasithin group, with only the universal
small-rank representation left explicit. The superscript O^{2,3} is the
intersection of normal subgroups with {2,3}-group quotient. -/
theorem twoCore_containment_of_representation
    (hrep : SmallRankAutomorphismRepresentation.{u})
    [Group.IsSolvable H] (hsqt : IsStronglyQuasithin H)
    (X V : Subgroup H) (hX : piResidual twoThreePrimes X = ⊤)
    (hV : IsPGroup 2 V) (hcomm : V = ⁅V, X⁆) : V ≤ pCore 2 H :=
  twoCore_containment_of_representation_and_twoNormalizer
    hrep twoLinearNormalizer hsqt X V hX hV hcomm

/-- The source SQTK case of A.1.26(2), conditional only on the universal
small-rank representation. The K-group part imposes no additional obligation
on this argument. -/
theorem twoCore_containment_of_sqtk_and_representation
    (hrep : SmallRankAutomorphismRepresentation.{u})
    [Group.IsSolvable H] {K : GroupClass.{u}} (hsqtk : IsSQTK K H)
    (X V : Subgroup H) (hX : piResidual twoThreePrimes X = ⊤)
    (hV : IsPGroup 2 V) (hcomm : V = ⁅V, X⁆) : V ≤ pCore 2 H :=
  twoCore_containment_of_representation hrep hsqtk.stronglyQuasithin X V hX hV hcomm

end CFSG.Quasithin.ChapterA.RankActions

end
