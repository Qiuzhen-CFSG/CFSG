module
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CyclicComponent
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.OddNormalImage

/-!
# Detecting odd-prime core actions in the original solvable amalgam

For an odd prime core of rank at most two, choose its actual supercritical
subgroup and embed the automorphisms of its Frattini quotient in GL₂(p).
The p-residual of the full action kernel centralizes the original prime
core. On every p-prime subgroup the matrix kernel is exactly the original
centralizer, so local residual movement survives this construction.

A moved prime core is noncyclic: the local two-residual lies in the derived
subgroup, which centralizes any normal cyclic group. It consequently has
rank two. If both residuals survive an action of a core-free Goldschmidt
triple, F.6.7--8 make both local kernels trivial and the full kernel odd.
The application to the literal original quotient X/O₂(X) is in
SolvableOddPrimeReduction; this does not yet exclude its odd primes.

Source: Aschbacher--Smith 13.4.7, printed p.901, and A.1.21,25,
printed pp.24--25.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
variable {G : Type*} [Group G] [Finite G]

/-- The actual rank-two supercritical action detects every coprime subgroup. -/
theorem exists_prime_core_matrix_action {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hr : primeRank p G ≤ 2) :
    ∃ S : Subgroup (pCore p G), ∃ hS : IsSupercriticalPSubgroup p S,
      letI : S.Characteristic := hS.characteristic
      Nat.card (S ⧸ frattini S) ≤ p ^ 2 ∧
      ∃ j : MulAut (S ⧸ frattini S) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p),
        Function.Injective j ∧
        let f := j.comp ((quotientAut (frattini S)).comp
          ((MulAut.characteristic S).comp (MulAut.conjNormal : G →* MulAut (pCore p G))))
        (pResidual p f.ker).map f.ker.subtype ≤ centralizer (pCore p G : Set G) ∧
        ∀ K : Subgroup G, Nat.Coprime p (Nat.card K) →
          K ⊓ f.ker = K ⊓ centralizer (pCore p G : Set G) := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨S,hS⟩ := (pCore_isPGroup (p := p) (G := G)).exists_supercriticalPSubgroup hp
  let : S.Characteristic := hS.characteristic
  let : Fact (IsPGroup p S) := ⟨pCore_isPGroup.to_subgroup S⟩
  let : IsElementaryAbelian p (S ⧸ frattini S) := isElementaryAbelian_quotient_frattini
  have hcard := ChapterA.lemma_A_1_25_frattini_card hodd pCore_isPGroup
    ((primeRank_subgroup_le p (pCore p G)).trans hr) S hS
  obtain ⟨j,hj⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (S ⧸ frattini S) hcard
  refine ⟨S,hS,hcard,j,hj,?_,?_⟩
  · let a := (quotientAut (frattini S)).comp (MulAut.characteristic S)
    let c : G →* MulAut (pCore p G) := MulAut.conjNormal
    let f := j.comp (a.comp c)
    have hker : f.ker = (a.comp c).ker := MonoidHom.ker_comp_of_injective _ _ hj
    let b : f.ker →* a.ker := (c.comp f.ker.subtype).codRestrict a.ker (fun g => by
      change c g ∈ a.ker
      exact show g.val ∈ (a.comp c).ker from hker ▸ g.property)
    have hb : IsPGroup p (f.ker ⧸ b.ker) :=
      ((hS.isPGroup_frattini_action_kernel pCore_isPGroup hodd).to_subgroup b.range).of_equiv
        (QuotientGroup.quotientKerEquivRange b).symm
    have hres : pResidual p f.ker ≤ b.ker := sInf_le ⟨inferInstance,hb⟩
    rintro _ ⟨g,hg,rfl⟩ y hy
    have hc : c g = 1 := congrArg Subtype.val (show b g = 1 from hres hg)
    have he := congrArg (fun z : MulAut (pCore p G) => (z ⟨y,hy⟩ : G)) hc
    change g.val * y * g.val⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro K hK
    let c : G →* MulAut (pCore p G) := MulAut.conjNormal
    let a := (quotientAut (frattini S)).comp (MulAut.characteristic S)
    have hc (g : G) : c g = 1 ↔ g ∈ centralizer (pCore p G : Set G) := by
      constructor
      · intro he y hy
        have hh := congrArg (fun z : MulAut (pCore p G) => (z ⟨y,hy⟩ : G)) he
        change g*y*g⁻¹=y at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      · intro he
        apply MulEquiv.ext
        intro y
        exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr (he y y.property).symm)
    ext g
    constructor
    · rintro ⟨hg,hf⟩
      refine ⟨hg,(hc g).mp ?_⟩
      have hz : a (c g) = 1 := hj (by
        simpa only [map_one] using (show j (a (c g)) = 1 from hf))
      have hcop : Nat.Coprime p (orderOf (c g)) := hK.of_dvd_right
        ((orderOf_map_dvd c g).trans (by
          simpa only [orderOf_mk] using orderOf_dvd_natCard (⟨g,hg⟩ : K)))
      have ho := hS.orderOf_frattini_action_eq_of_coprime pCore_isPGroup hodd (c g) hcop
      change orderOf (a (c g)) = orderOf (c g) at ho
      rw [hz,orderOf_one] at ho
      exact orderOf_eq_one_iff.mp ho.symm
    · rintro ⟨hg,hgC⟩
      refine ⟨hg,?_⟩
      change j (a (c g)) = 1
      rw [(hc g).mpr hgC,map_one,map_one]

/-- A moved prime core in an S3-over-two-core local group is noncyclic. -/
theorem prime_core_not_cyclic_of_local_movement {p : ℕ}
    (A : Subgroup G) (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hm : ¬ (pResidual 2 A).map A.subtype ≤ centralizer (pCore p G : Set G)) :
    ¬ IsCyclic (pCore p G) := by
  intro hc
  let := hc
  apply hm
  have hr := map_mono (f := A.subtype)
    (ChapterF.Cyclic.residual_le_derived_of_symmetric_three eA)
  rw [map_subtype_commutator] at hr
  exact hr.trans ((commutator_mono le_top le_top).trans
    (commutator_le_centralizer_of_isCyclic_normal (pCore p G)))

/-- Both surviving residuals force trivial local kernels, without asserting
that the full matrix-action kernel is trivial. -/
theorem pair_action_local_kernels {A B : Subgroup G}
    (hg : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    {H : Type*} [Group H] (f : G →* H)
    (hA : ((pResidual 2 A).map A.subtype).map f ≠ ⊥)
    (hB : ((pResidual 2 B).map B.subtype).map f ≠ ⊥) :
    A ⊓ f.ker = ⊥ ∧ B ⊓ f.ker = ⊥ ∧ Odd (Nat.card f.ker) := by
  have ha := (hg.left_subnormal_core_iff_not_residual_le f.ker
    (Normal.isSubnormal inferInstance)).mpr (fun hh => hA ((Subgroup.map_eq_bot_iff _).mpr hh))
  have hb := (hg.right_subnormal_core_iff_not_residual_le f.ker
    (Normal.isSubnormal inferInstance)).mpr (fun hh => hB ((Subgroup.map_eq_bot_iff _).mpr hh))
  have ht := (hg.normal_intersection_le_twoCore f.ker ha hb).trans hcore.le
  have hea := hg.left_intersection_eq_core_intersection f.ker ha
  have heb := hg.symm.left_intersection_eq_core_intersection f.ker hb
  refine ⟨?_,?_,ChapterF.Noncyclic.odd_card_normal_of_local_intersections hg hcore f.ker ha hb⟩
  · exact le_bot_iff.mp ((hea.1.trans hea.2).le.trans ht)
  · apply le_bot_iff.mp
    rw [heb.1,heb.2,inf_comm B A]
    exact ht

/-- Movement forces the odd prime core to have the full available rank two. -/
theorem prime_core_rank_two_of_local_movement {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hr : primeRank p G ≤ 2)
    (A : Subgroup G) (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hm : ¬ (pResidual 2 A).map A.subtype ≤ centralizer (pCore p G : Set G)) :
    primeRank p (pCore p G) = 2 := by
  have hle := (primeRank_subgroup_le p (pCore p G)).trans hr
  have hnot : ¬ primeRank p (pCore p G) ≤ 1 := by
    intro hsmall
    apply prime_core_not_cyclic_of_local_movement A eA hm
    apply (pCore_isPGroup (p := p) (G := G)).isCyclic_of_odd_of_elementary_card_le
      ((Fact.out : p.Prime).odd_of_ne_two hp)
    intro E hE
    let := hE
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hsmall E
  omega

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
