module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.ComponentLocalization
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RankTwoSeedResidual
public import Theory.GroupTheory.CComponent.PrimeResidualPair
public import Theory.GroupTheory.SolvableResidual.PrimeTo

/-!
# The original two-component orbit as a canonical residual

At every odd prime dividing L/O₂(L), the two original components use both
available ranks. All other C-components of M consequently have order prime
to that prime. The component-layer calculation and source 1.2.1 identify
L₀ with O^{p′}(M∞). Functoriality of this exact composite residual places
every conjugate of L contained in M inside L₀, and makes L₀-containment in
a conjugate of M rigid.

This includes the Suzuki row, whose order is prime to three. No stronger
identity O^{p′}(M)=L₀ or outer-automorphism assertion is used.
Source: Aschbacher--Smith 1.2.1 and 10.2.10, printed pp.504,753.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02 Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem other_component_prime_free
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (A B : Subgroup G) (hA : A.IsCComponent) (hB : B.IsCComponent) (hne : A ≠ B)
    [IsSimpleGroup (A ⧸ pCore 2 A)] [IsSimpleGroup (B ⧸ pCore 2 B)]
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (ha : p ∣ Nat.card (A ⧸ pCore 2 A)) (hb : p ∣ Nat.card (B ⧸ pCore 2 B))
    {C : Subgroup G} (hC : C.IsCComponent) (hCA : C ≠ A) (hCB : C ≠ B) :
    Nat.Coprime p (Nat.card C) := by
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hor _ pCore_isPGroup).trans
      (hG.stronglyQuasithin r hr hor)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let : Group.IsPerfect A := hA.perfect
  let : Group.IsPerfect B := hB.perfect
  let : IsSimpleGroup (A.map q) := (cComponentTwoCoreQuotientEquiv hA).symm.isSimpleGroup
  let : IsSimpleGroup (B.map q) := (cComponentTwoCoreQuotientEquiv hB).symm.isSimpleGroup
  let : Group.IsPerfect (A.map q) := Group.IsPerfect.map q
  let : Group.IsPerfect (B.map q) := Group.IsPerfect.map q
  have comm {X Y : Subgroup G} (hX : X.IsCComponent) (hY : Y.IsCComponent) (hne : X ≠ Y) :
      ⁅X.map q,Y.map q⁆ = ⊥ :=
    ChapterA.Section03.CComponentCommutation.commutator_eq_bot hQ
      (pCore_quotient_pCore_eq_bot 2) (hX.map_quotient _) (hY.map_quotient _)
      (fun he => hne (hX.eq_of_map_quotient_eq hY _ he))
  have hab := comm hA hB hne
  have hz : center (A.map q ⊔ B.map q : Subgroup Q) = ⊥ :=
    TwoOrbitThree.join_center_eq_bot _ _ hab center_eq_bot_of_simple_perfect center_eq_bot_of_simple_perfect
  have hrA : 1 ≤ primeRank p (A.map q) := by
    have hd : p ∣ Nat.card (A.map q) := (Nat.card_congr (cComponentTwoCoreQuotientEquiv hA).toEquiv) ▸ ha
    have hh : primeRank p (A.map q) ≠ 0 := fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd
    omega
  have hrB : 1 ≤ primeRank p (B.map q) := by
    have hd : p ∣ Nat.card (B.map q) := (Nat.card_congr (cComponentTwoCoreQuotientEquiv hB).toEquiv) ▸ hb
    have hh : primeRank p (B.map q) ≠ 0 := fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd
    omega
  have hrAB : 2 ≤ primeRank p (A.map q ⊔ B.map q : Subgroup Q) := by
    rw [primeRank_sup_eq_add_of_disjoint_commuting _ _
      (disjoint_of_commuting_of_center_eq_bot hab center_eq_bot_of_simple_perfect)
      (commutator_eq_bot_iff_le_centralizer.mp hab)]
    omega
  have hcomm : C.map q ≤ centralizer (A.map q ⊔ B.map q : Subgroup Q) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (comm hC hA hCA)))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (comm hC hB hCB)))
  have hadd := ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (C.map q) (A.map q ⊔ B.map q) hcomm
    (show Nat.Coprime p (Nat.card (center (A.map q ⊔ B.map q : Subgroup Q))) by simp [hz])
  have hbound := hQ.stronglyQuasithin p (Fact.out : p.Prime) ho
  have hzC : primeRank p (C.map q) = 0 := by
    dsimp only [Q,q] at hrAB hadd hbound ⊢
    omega
  have hc : Nat.Coprime p (Nat.card (C ⧸ pCore 2 C)) := by
    rw [Nat.card_congr (cComponentTwoCoreQuotientEquiv hC).toEquiv]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (PrimeRank.eq_zero_iff_not_dvd_card.mp hzC)
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 C)]
  apply hc.mul_right
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
  rw [hn]
  exact (Nat.coprime_two_right.mpr ho).pow_right n

private theorem component_prime_residual_top
    (A : Subgroup G) [Group.IsPerfect A] [IsSimpleGroup (A ⧸ pCore 2 A)]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card (A ⧸ pCore 2 A)) :
    primeToResidual p A = ⊤ := by
  have hp : IsPPerfect 2 A := by
    intro N hN hquot
    let := hN
    have hs : Subsingleton (A ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  exact primeToResidual_eq_top_of_simple_quotient p 2 (pCore 2 A) pCore_isPGroup hp hd

variable {T : Sylow 2 G} {L : Subgroup G}

/-- The source residual identity retains both intrinsic inclusion maps. -/
theorem orbit_eq_prime_residual_of_solvable_residual
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    localOrbit T L = ((primeToResidual p (solvableResidual D.maximalLocal)).map
      (solvableResidual D.maximalLocal).subtype).map D.maximalLocal.subtype := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tM : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let B := A.map (MulAut.conj tM).toMonoidHom
  have hA : A.IsCComponent := D.component_in_maximalLocal
  have hB : B.IsCComponent := hA.map_equiv (MulAut.conj tM)
  have hmA : A.map M.subtype = L := map_subgroupOf_eq_of_le hLM
  have hmB : B.map M.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [map_map,show M.subtype.comp (MulAut.conj tM).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp M.subtype from rfl,←map_map,hmA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmB.symm.trans ((congrArg (map M.subtype) he).symm.trans hmA)
  let a : A ≃* L := subgroupOfEquivOfLe hLM
  let b : B ≃* L := ((MulAut.conj tM).subgroupMap A).symm.trans a
  let ea := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let eb := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let := quotient_simple D hn
  let : IsSimpleGroup (A ⧸ pCore 2 A) := ea.isSimpleGroup
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eb.isSimpleGroup
  have ha : p ∣ Nat.card (A ⧸ pCore 2 A) := (Nat.card_congr ea.toEquiv).symm ▸ hd
  have hb : p ∣ Nat.card (B ⧸ pCore 2 B) := (Nat.card_congr eb.toEquiv).symm ▸ hd
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hM : IsSQTK KnownSimple.IsKnownSimple M := D.simpleQTKE.twoLocal_sqtk
    hu.normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hM.isKGroup.quotient _⟩
    intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hor _ pCore_isPGroup).trans
      (hM.stronglyQuasithin r hr hor)
  have hgen : cComponentLayer M = solvableResidual M :=
    proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO) hQ
  let : Group.IsPerfect A := hA.perfect
  let : Group.IsPerfect B := hB.perfect
  have he := cComponent_pair_eq_layer_primeToResidual A B hA hB
    (component_prime_residual_top A ha) (component_prime_residual_top B hb)
    (fun C hC hCA hCB => other_component_prime_free hM A B hA hB hne ho ha hb hC hCA hCB)
  rw [hgen] at he
  have hm := congrArg (map M.subtype) he
  rw [Subgroup.map_sup,hmA,hmB] at hm
  exact hpair.trans hm

/-- The original orbit is the canonical composite residual at every odd divisor. -/
theorem orbit_eq_perfectPrimeResidual
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    localOrbit T L = perfectPrimeResidual p D.maximalLocal :=
  (orbit_eq_prime_residual_of_solvable_residual D hn ho hd).trans
    (perfectPrimeResidual_eq p D.maximalLocal).symm

/-- The intrinsic original component is fixed by the same residual operation. -/
theorem component_perfectPrimeResidual_eq
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    perfectPrimeResidual p L = L := by
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let := quotient_simple D hn
  exact perfectPrimeResidual_eq_self p L (component_prime_residual_top L hd)

/-- Every conjugate copy of the original component contained in M lies in L₀,
including the three-free Suzuki row. -/
theorem conjugate_component_le_orbit
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (g : G) (hg : L.map (MulAut.conj g).toMonoidHom ≤ D.maximalLocal) :
    L.map (MulAut.conj g).toMonoidHom ≤ localOrbit T L := by
  obtain ⟨p,hp,ho,hd⟩ := source_component_quotient_has_odd_prime D
  let : Fact p.Prime := ⟨hp⟩
  have hh := perfectPrimeResidual_mono p hg
  rwa [←map_perfectPrimeResidual,component_perfectPrimeResidual_eq D hn hd,
    ←orbit_eq_perfectPrimeResidual D hn ho hd] at hh

/-- The original orbit is generated by its prime-to-p residual at any divisor
of the simple component quotient. -/
theorem orbit_prime_residual_eq_top
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    primeToResidual p (localOrbit T L) = ⊤ := by
  let S := (solvableResidual D.maximalLocal).map D.maximalLocal.subtype
  have hr : (primeToResidual p S).map S.subtype = localOrbit T L :=
    (orbit_eq_perfectPrimeResidual D hn ho hd).symm
  have he := map_embedded_primeToResidual_of_hom p (primeToResidual p S) S.subtype
  rw [embedded_primeToResidual_eq_of_normal p (primeToResidual p S) le_rfl,hr] at he
  apply map_injective (localOrbit T L).subtype_injective
  rw [←MonoidHom.range_eq_map,range_subtype]
  exact he.symm

/-- Containment of the original orbit in a conjugate maximal local is rigid,
without requiring three to divide the component quotient. -/
theorem orbit_le_conjugate_maximal_iff
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (g : G) :
    localOrbit T L ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom ↔
      g ∈ D.maximalLocal := by
  let R := localOrbit T L
  let M := D.maximalLocal
  constructor
  · intro hg
    obtain ⟨p,hp,ho,hd⟩ := source_component_quotient_has_odd_prime D
    let : Fact p.Prime := ⟨hp⟩
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
    let : Group.IsPerfect R := isPerfect_iSup_conjugates L T
    have hh := perfectPrimeResidual_mono p hg
    rw [perfectPrimeResidual_eq_self p R (orbit_prime_residual_eq_top D hn ho hd),
      ←map_perfectPrimeResidual,←orbit_eq_perfectPrimeResidual D hn ho hd] at hh
    have he : R = R.map (MulAut.conj g).toMonoidHom := eq_of_le_of_card_ge hh
      (Nat.card_congr ((MulAut.conj g).subgroupMap R).toEquiv).ge
    exact mem_normalizer_iff_map_conj_eq.mpr he.symm
  · intro hg
    have he : M.map (MulAut.conj g).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hg)
    exact R.le_normalizer.trans_eq he.symm

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
