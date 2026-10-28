module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.OddPrimeAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ActionKernel
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PCoreLocalKernel
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SolvableReduction
public import Theory.GroupTheory.Fitting.PrimeResidual

/-!
# The actual odd-prime obstruction in the solvable original pair

Apply F.6.9 to X/O₂(X), with the original SQTK cover. Failure of its
{2,3}-group conclusion selects a prime p > 3 whose prime core is moved by
the first local residual. OddPrimeAction constructs a rank-two prime core
and its literal supercritical Frattini action in GL₂(p), retaining the
centralizer kernels on both parabolics and the full action kernel.

If the second residual also acts nontrivially, F.6.7--8 make the local
maps injective. Their distinct two-cores remain distinct, and the actual
matrix range has the same genuine Goldschmidt pair with a full common
Sylow subgroup. If its action is trivial, the original second residual
centralizes the prime core. The source hypotheses supply locality,
quotient parabolics and the rank bound; neither the prime nor its movement
nor its matrix representation is an extra input in the final application.

The remaining source work is to exclude the solvable GL₂(p) pair and then
the single surviving action by the normal p-complement argument. This
module does not assert the universal 13.4.7 alternatives or Thompson
normality. Source: Aschbacher--Smith 13.4.7, printed p.901, using A.1.21,25
and F.6.7--9.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem local_card_coprime {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (A : Subgroup G) (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) :
    Nat.Coprime p (Nat.card A) := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  rw [SymmetricThreeTwoCore.card_eq eA,hn]
  have h2 := (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2
  have h3 := (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_three).mpr hp3
  exact (h2.mul_right h3).mul_right (h2.pow_right n)

omit [Finite G] in
private theorem restricted_injective {H : Type*} [Group H]
    (f : G →* H) (A : Subgroup G) (hk : A ⊓ f.ker = ⊥) :
    Function.Injective (f.subgroupMap A) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply Subtype.ext
  exact mem_bot.mp (hk ▸ (show (a : G) ∈ A ⊓ f.ker from
    ⟨a.property,congrArg Subtype.val ha⟩))

private theorem local_image_quotient {H : Type*} [Group H] [Finite H]
    (f : G →* H) (A : Subgroup G)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hk : A ⊓ f.ker ≤ A.pCoreIn 2) :
    Nonempty (((A.map f) ⧸ pCore 2 (A.map f)) ≃* Equiv.Perm (Fin 3)) := by
  let fA := f.subgroupMap A
  have hker : IsPGroup 2 fA.ker := by
    have hle : fA.ker ≤ pCore 2 A := by
      intro a ha
      obtain ⟨b,hb,he⟩ := hk ⟨a.property,congrArg Subtype.val ha⟩
      exact (show b = a from Subtype.ext he) ▸ hb
    exact pCore_isPGroup.to_le hle
  let q := (QuotientGroup.mk' (pCore 2 (A.map f))).comp fA
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp
    (f.subgroupMap_surjective A)
  have hqker : q.ker = pCore 2 A := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact fA.comap_pCore_of_ker_isPGroup (f.subgroupMap_surjective A) hker
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective q hq).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hqker)).trans eA⟩

/-- If both residuals survive, the literal matrix range retains the genuine
Goldschmidt triple and distinct local two-cores, even with an odd full kernel. -/
theorem pair_action_range_triple {A B : Subgroup G}
    (hg : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2)
    {H : Type*} [Group H] [Finite H] (f : G →* H)
    (hA : ((pResidual 2 A).map A.subtype).map f ≠ ⊥)
    (hB : ((pResidual 2 B).map B.subtype).map f ≠ ⊥) :
    let q := f.rangeRestrict
    Function.Injective (q.subgroupMap A) ∧ Function.Injective (q.subgroupMap B) ∧
      (A.map q).pCoreIn 2 ≠ (B.map q).pCoreIn 2 ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) := by
  let q := f.rangeRestrict
  obtain ⟨ha,hb,_⟩ := pair_action_local_kernels hg hcore f hA hB
  have ha' : A ⊓ q.ker = ⊥ := by simpa only [q,MonoidHom.ker_rangeRestrict] using ha
  have hb' : B ⊓ q.ker = ⊥ := by simpa only [q,MonoidHom.ker_rangeRestrict] using hb
  have hia := restricted_injective q A ha'
  have hib := restricted_injective q B hb'
  have hka : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hia]
    exact IsPGroup.of_bot
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hib]
    exact IsPGroup.of_bot
  have hne := pCoreIn_image_ne_of_local_kernels 2 q A B hka hkb
    (hg.local_twoCore_le_intersection.trans inf_le_right)
    (hg.symm.local_twoCore_le_intersection.trans inf_le_right) hcores
  let eA := (local_image_quotient q A hg.quotient_left.some (ha' ▸ bot_le)).some
  let eB := (local_image_quotient q B hg.quotient_right.some (hb' ▸ bot_le)).some
  obtain ⟨T,hT⟩ := hg.intersection_sylow
  let S := T.mapSurjective f.rangeRestrict_surjective
  have hSA : (S : Subgroup f.range) ≤ A.map q := map_mono (hT.symm.le.trans inf_le_left)
  have hSB : (S : Subgroup f.range) ≤ B.map q := map_mono (hT.symm.le.trans inf_le_right)
  refine ⟨hia,hib,hne,?_,⟨eA⟩,⟨eB⟩,S,?_⟩
  · rw [←Subgroup.map_sup,hg.generated,map_top_of_surjective q f.rangeRestrict_surjective]
  · exact intersection_eq_sylow hSA hSB eA eB (fun hh => hne (congrArg (fun C => C.pCoreIn 2) hh))

/-- The odd-prime action step for a solvable core-free pair. Every matrix
and kernel is constructed from the same prime core; no action is supplied. -/
theorem solvable_pair_odd_prime_action {A B : Subgroup G}
    (hg : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable G)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hr : primeRank p G ≤ 2)
    (hm : ¬ (pResidual 2 A).map A.subtype ≤ centralizer (pCore p G : Set G)) :
    ¬ IsCyclic (pCore p G) ∧ primeRank p (pCore p G) = 2 ∧
    ∃ f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p),
      Group.IsSolvable f.range ∧
      (pResidual p f.ker).map f.ker.subtype ≤ centralizer (pCore p G : Set G) ∧
      A ⊓ f.ker = A ⊓ centralizer (pCore p G : Set G) ∧
      B ⊓ f.ker = B ⊓ centralizer (pCore p G : Set G) ∧
      ((pResidual 2 A).map A.subtype).map f ≠ ⊥ ∧
      Nonempty (((A.map f) ⧸ pCore 2 (A.map f)) ≃* Equiv.Perm (Fin 3)) ∧
      (((pResidual 2 B).map B.subtype).map f = ⊥ ↔
        (pResidual 2 B).map B.subtype ≤ centralizer (pCore p G : Set G)) ∧
      (¬ (pResidual 2 B).map B.subtype ≤ centralizer (pCore p G : Set G) →
        Odd (Nat.card f.ker) ∧
        Function.Injective (f.rangeRestrict.subgroupMap A) ∧
        Function.Injective (f.rangeRestrict.subgroupMap B) ∧
        (A.map f.rangeRestrict).pCoreIn 2 ≠ (B.map f.rangeRestrict).pCoreIn 2 ∧
        ChapterF.IsGoldschmidtTriple (A.map f.rangeRestrict) (B.map f.rangeRestrict)) := by
  obtain ⟨S,hS,hcard,j,hj,hcentral,hdetect⟩ := exists_prime_core_matrix_action hp2 hr
  let : S.Characteristic := hS.characteristic
  let f := j.comp ((quotientAut (frattini S)).comp
    ((MulAut.characteristic S).comp (MulAut.conjNormal : G →* MulAut (pCore p G))))
  have hca := local_card_coprime hp2 hp3 A hg.quotient_left.some
  have hcb := local_card_coprime hp2 hp3 B hg.quotient_right.some
  have ha := hdetect A hca
  have hb := hdetect B hcb
  have detect (C : Subgroup G) (he : C ⊓ f.ker = C ⊓ centralizer (pCore p G : Set G))
      (K : Subgroup G) (hKC : K ≤ C) : K.map f = ⊥ ↔ K ≤ centralizer (pCore p G : Set G) := by
    rw [Subgroup.map_eq_bot_iff]
    constructor
    · intro hh
      exact (le_inf hKC hh).trans (he.le.trans inf_le_right)
    · intro hh
      exact (le_inf hKC hh).trans (he.ge.trans inf_le_right)
  have hneA : ((pResidual 2 A).map A.subtype).map f ≠ ⊥ :=
    fun hz => hm ((detect A ha _ (map_subtype_le _)).mp hz)
  have hiffB := detect B hb _ (map_subtype_le (pResidual 2 B))
  have hkA := (hg.left_subnormal_core_iff_not_residual_le f.ker
    (Normal.isSubnormal inferInstance)).mpr
      (fun hh => hneA ((Subgroup.map_eq_bot_iff _).mpr hh))
  let : Group.IsSolvable G := hs
  refine ⟨prime_core_not_cyclic_of_local_movement A hg.quotient_left.some hm,
    prime_core_rank_two_of_local_movement hp2 hr A hg.quotient_left.some hm,
    f,Group.isSolvable_of_surjective f.rangeRestrict_surjective,hcentral,
    ha,hb,hneA,local_image_quotient f A hg.quotient_left.some hkA,hiffB,?_⟩
  intro hmoveB
  have hneB : ((pResidual 2 B).map B.subtype).map f ≠ ⊥ := fun hz => hmoveB (hiffB.mp hz)
  exact ⟨(pair_action_local_kernels hg hcore f hneA hneB).2.2,
    pair_action_range_triple hg hcore hcores f hneA hneB⟩


/-- Apply the odd-prime reduction to the literal original join modulo O₂.
Locality, both quotient parabolics, unequal cores and the odd-prime rank
bound are derived from the original source hypotheses. -/
theorem original_pair_solvable_odd_prime_action
    {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    let X := A ⊔ B
    let Q := X ⧸ pCore 2 X
    let q := QuotientGroup.mk' (pCore 2 X)
    let A₀ := (A.subgroupOf X).map q
    let B₀ := (B.subgroupOf X).map q
    let R := (pResidual 2 A₀).map A₀.subtype
    let S := (pResidual 2 B₀).map B₀.subtype
    ¬ R ≤ centralizer (pCore p Q : Set Q) →
      ¬ IsCyclic (pCore p Q) ∧ primeRank p (pCore p Q) = 2 ∧
      ∃ f : Q →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p),
        Group.IsSolvable f.range ∧
        (pResidual p f.ker).map f.ker.subtype ≤ centralizer (pCore p Q : Set Q) ∧
        A₀ ⊓ f.ker = A₀ ⊓ centralizer (pCore p Q : Set Q) ∧
        B₀ ⊓ f.ker = B₀ ⊓ centralizer (pCore p Q : Set Q) ∧
        R.map f ≠ ⊥ ∧
        Nonempty (((A₀.map f) ⧸ pCore 2 (A₀.map f)) ≃* Equiv.Perm (Fin 3)) ∧
        (S.map f = ⊥ ↔ S ≤ centralizer (pCore p Q : Set Q)) ∧
        (¬ S ≤ centralizer (pCore p Q : Set Q) →
          Odd (Nat.card f.ker) ∧
          Function.Injective (f.rangeRestrict.subgroupMap A₀) ∧
          Function.Injective (f.rangeRestrict.subgroupMap B₀) ∧
          (A₀.map f.rangeRestrict).pCoreIn 2 ≠ (B₀.map f.rangeRestrict).pCoreIn 2 ∧
          ChapterF.IsGoldschmidtTriple (A₀.map f.rangeRestrict) (B₀.map f.rangeRestrict)) := by
  let X := A ⊔ B
  let q := QuotientGroup.mk' (pCore 2 X)
  let A' := A.subgroupOf X
  let B' := B.subgroupOf X
  let Q := X ⧸ pCore 2 X
  have hg := pair_goldschmidt hTA hTB eA eB hne
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hcores' : A'.pCoreIn 2 ≠ B'.pCoreIn 2 := by
    intro he
    have hm := congrArg (map X.subtype) he
    rw [pCoreIn_subgroupOf 2 A X le_sup_left,pCoreIn_subgroupOf 2 B X le_sup_right,
      map_subgroupOf_eq_of_le ((A.pCoreIn_le 2).trans le_sup_left),
      map_subgroupOf_eq_of_le ((B.pCoreIn_le 2).trans le_sup_right)] at hm
    exact hcores hm
  have hcoresQ := pCoreIn_image_ne_of_local_kernels 2 q A' B'
    (by rw [ker_subgroupMap]; exact hq.comap_subtype)
    (by rw [ker_subgroupMap]; exact hq.comap_subtype)
    (hg.local_twoCore_le_intersection.trans inf_le_right)
    (hg.symm.local_twoCore_le_intersection.trans inf_le_right) hcores'
  have hlocal := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
  have hrX := (Chapter3.sqtk_of_mem_H h₀.qtke hlocal.1).stronglyQuasithin
    p (Fact.out : p.Prime) ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have hcop : Nat.Coprime p (Nat.card (pCore 2 X)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
    rw [hn]
    exact ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2).pow_right n
  have hrQ : primeRank p Q ≤ 2 :=
    (primeRank_quotient_le_of_coprime p (pCore 2 X) hcop).trans hrX
  let : Group.IsSolvable X := hs
  dsimp only
  intro hm
  exact solvable_pair_odd_prime_action hg.quotient_twoCore hg.quotient_twoCore_eq_bot
    hcoresQ inferInstance hp2 hp3 hrQ hm


/-- Failure of the two-three conclusion supplies an actual moved prime core;
cyclic or unused odd-prime cores are not added as external hypotheses. -/
theorem solvable_pair_exists_moved_large_prime
    {H : Type u} [Group H] [Finite H] {K : GroupClass.{u}}
    (hH : IsSQTK K H) (q : H →* G) (hq : Function.Surjective q)
    {A B : Subgroup G} (hg : ChapterF.IsGoldschmidtTriple A B)
    (hs : Group.IsSolvable G) (hc : pCore 2 G = ⊥)
    (hnot : ¬ IsPiGroup twoThreePrimes G) :
    ∃ p : Nat.Primes, p.val ≠ 2 ∧ p.val ≠ 3 ∧ p.val ∣ Nat.card G ∧
      ¬ (pResidual 2 A).map A.subtype ≤ centralizer (pCore p.val G : Set G) := by
  classical
  by_contra! hn
  apply hnot
  apply ChapterF.SourceAssembly.source_lemma_F_6_9 hH q hq hs hg
  apply Or.inl
  apply le_centralizer_iff.mpr
  rw [fitting_pResidual_eq_sup_prime_cores]
  refine iSup_le fun p => iSup_le fun hp3 => ?_
  by_cases hp2 : p.val.val = 2
  · rw [hp2,hc]
    exact bot_le
  · exact le_centralizer_iff.mp (hn ⟨p.val.val,Nat.prime_of_mem_primeFactors p.val.property⟩
      hp2 hp3 (Nat.dvd_of_mem_primeFactors p.val.property))

/-- In the original unequal-core solvable pair, failure of the two-three
quotient produces the actual rank-two matrix obstruction with both literal
local maps. The moving prime and its action are constructed, not supplied. -/
theorem original_pair_solvable_odd_prime_obstruction
    {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable (A ⊔ B : Subgroup G)) :
    let X := A ⊔ B
    let Q := X ⧸ pCore 2 X
    let q := QuotientGroup.mk' (pCore 2 X)
    let A₀ := (A.subgroupOf X).map q
    let B₀ := (B.subgroupOf X).map q
    let R := (pResidual 2 A₀).map A₀.subtype
    let S := (pResidual 2 B₀).map B₀.subtype
    ¬ IsPiGroup twoThreePrimes Q →
      ∃ p : Nat.Primes, p.val ≠ 2 ∧ p.val ≠ 3 ∧ p.val ∣ Nat.card Q ∧
        ¬ IsCyclic (pCore p.val Q) ∧ primeRank p.val (pCore p.val Q) = 2 ∧
        letI : Fact p.val.Prime := ⟨p.property⟩
        ∃ f : Q →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p.val),
          Group.IsSolvable f.range ∧
          (pResidual p.val f.ker).map f.ker.subtype ≤ centralizer (pCore p.val Q : Set Q) ∧
          A₀ ⊓ f.ker = A₀ ⊓ centralizer (pCore p.val Q : Set Q) ∧
          B₀ ⊓ f.ker = B₀ ⊓ centralizer (pCore p.val Q : Set Q) ∧
          R.map f ≠ ⊥ ∧
          Nonempty (((A₀.map f) ⧸ pCore 2 (A₀.map f)) ≃* Equiv.Perm (Fin 3)) ∧
          (S.map f = ⊥ ↔ S ≤ centralizer (pCore p.val Q : Set Q)) ∧
          (¬ S ≤ centralizer (pCore p.val Q : Set Q) →
            Odd (Nat.card f.ker) ∧
            Function.Injective (f.rangeRestrict.subgroupMap A₀) ∧
            Function.Injective (f.rangeRestrict.subgroupMap B₀) ∧
            (A₀.map f.rangeRestrict).pCoreIn 2 ≠ (B₀.map f.rangeRestrict).pCoreIn 2 ∧
            ChapterF.IsGoldschmidtTriple (A₀.map f.rangeRestrict) (B₀.map f.rangeRestrict)) := by
  let X := A ⊔ B
  let q := QuotientGroup.mk' (pCore 2 X)
  have hg := pair_goldschmidt hTA hTB eA eB hne
  have hlocal := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
  let : Group.IsSolvable X := hs
  dsimp only
  intro hnot
  obtain ⟨p,hp2,hp3,hdiv,hmove⟩ := solvable_pair_exists_moved_large_prime
    (Chapter3.sqtk_of_mem_H h₀.qtke hlocal.1) q (QuotientGroup.mk'_surjective _)
      hg.quotient_twoCore inferInstance hg.quotient_twoCore_eq_bot hnot
  let : Fact p.val.Prime := ⟨p.property⟩
  obtain ⟨hnc,hr,haction⟩ := original_pair_solvable_odd_prime_action h₀ D m hTA hTB eA eB hne
    hindexA hindexB hcores hs hp2 hp3 hmove
  exact ⟨p,hp2,hp3,hdiv,hnc,hr,haction⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
