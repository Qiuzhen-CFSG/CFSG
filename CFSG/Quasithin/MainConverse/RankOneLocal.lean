module

public import CFSG.Quasithin.Defs
public import Theory.Quasithin.EvenCharacteristic
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import BenderSuzuki.Converse.PSU3
public import BenderSuzuki.PFchapter1section1.proposition_1_c
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup

/-!
# QT and even characteristic for the linear and unitary rank-one families

For PSL₂(2^f) and PSU₃(2^f), a Sylow two-subgroup acts regularly on the
complement of its unique fixed point in the natural action. The normalizer
of every nontrivial subgroup of this Sylow subgroup therefore lies in its
Borel. The cyclic torus supplement makes the quotient of the Borel by the
Sylow subgroup cyclic; every odd prime-power subgroup embeds in that quotient.
Sylow conjugacy then bounds all odd two-local ranks by one and proves QT.

Faithfulness of the natural action makes the Sylow subgroup self-centralizing:
a commuting element fixes the distinguished point, and its action on one
other point shows that its order is a power of two. The proper-overgroup
clause of the genuine rank-one Borel theorem then gives a self-centralizing
two-core in each maximal two-local containing a Sylow subgroup. Simplicity
and nonabelianity are inherited from the consumer and ensure that these
locals are proper.

The unitary matrix field has order (2^f)² and its involution is x ↦ x^(2^f).
An actual change of Hermitian basis and the supplied group equivalences
transport the results, also when the consumer lives in another universe.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Theorem 0.1.2(1), printed pp.4 and 482, and
F.1.3(1), printed pp.259–260. This module supplies the QT and E clauses;
proper simple sections belong to the separate converse assembly.
-/

open Subgroup
open CFSG.Quasithin

namespace CFSG.Quasithin.MainConverse

private theorem cyclic_supplement_rank {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (D : Subgroup G)
    (hD : D ≤ normalizer (S : Set G)) (hcyc : IsCyclic D)
    (hsup : (S : Subgroup G) ⊔ D = normalizer (S : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p (normalizer (S : Set G)) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let B := normalizer (S : Set G)
  let Q := (S : Subgroup G).subgroupOf B
  let E := D.subgroupOf B
  let : Q.Normal := normal_subgroupOf_of_le_normalizer (le_refl B)
  let : IsCyclic D := hcyc
  let : IsCyclic E := (subgroupOfEquivOfLe hD).isCyclic.mpr hcyc
  have hQE : Q ⊔ E = ⊤ := by
    change (S : Subgroup G).subgroupOf B ⊔ D.subgroupOf B = ⊤
    rw [← subgroupOf_sup (show (S : Subgroup G) ≤ B from
      (S : Subgroup G).le_normalizer) hD, hsup]
    exact subgroupOf_self B
  let q := QuotientGroup.mk' Q
  have hsurj : Function.Surjective (q.comp E.subtype) := by
    intro z
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective Q z
    obtain ⟨s, hs, d, hd, rfl⟩ := mem_sup_of_normal_left.mp (hQE ▸ mem_top b)
    refine ⟨⟨d, hd⟩, ?_⟩
    change q d = q (s * d)
    have hs1 : q s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
    rw [map_mul, hs1, one_mul]
  let : IsCyclic (B ⧸ Q) := isCyclic_of_surjective (q.comp E.subtype) hsurj
  let P : Sylow p B := Classical.choice inferInstance
  apply P.primeRank_le_one_of_isCyclic
  apply isCyclic_of_injective (q.comp (P : Subgroup B).subtype)
  apply injective_comp_subtype_of_coprime_ker q _ _ P.isPGroup'
  rw [QuotientGroup.ker_mk']
  have hQp : IsPGroup 2 Q := S.isPGroup'.comap_subtype
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  change Nat.Coprime p (Nat.card Q)
  rw [hn]
  exact (Nat.coprime_two_right.mpr ho).pow_right n

private theorem regular_free {G Ω : Type*} [Group G] [MulAction G Ω]
    (S : Subgroup G) {α β : Ω}
    (heval : Set.BijOn (fun s : S => (s : G) • β) Set.univ {a | a ≠ α})
    (s : S) {a : Ω} (ha : a ≠ α) (hsa : (s : G) • a = a) : s = 1 := by
  obtain ⟨r, _, hr⟩ := heval.surjOn ha
  have hsr : s * r = r := heval.injOn (Set.mem_univ _) (Set.mem_univ _) (by
    simpa only [coe_mul, mul_smul, hr] using hsa)
  exact mul_right_cancel (hsr.trans (one_mul r).symm)

private theorem regular_normalizer_le {G Ω : Type*} [Group G] [MulAction G Ω]
    (S : Subgroup G) {α β : Ω}
    (hN : normalizer (S : Set G) = MulAction.stabilizer G α)
    (heval : Set.BijOn (fun s : S => (s : G) • β) Set.univ {a | a ≠ α})
    (R : Subgroup G) (hR : R ≠ ⊥) (hRS : R ≤ S) :
    normalizer (R : Set G) ≤ normalizer (S : Set G) := by
  intro g hg
  rw [hN, MulAction.mem_stabilizer_iff]
  by_contra hmove
  obtain ⟨r, hr⟩ := ne_bot_iff_exists_ne_one.mp hR
  have hconj : g⁻¹ * (r : G) * g ∈ R := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (R : Set G)).inv_mem hg) (r : G)).mp r.property
  have hfix : (g⁻¹ * (r : G) * g) • α = α :=
    MulAction.mem_stabilizer_iff.mp (hN ▸ S.le_normalizer (hRS hconj))
  have hfix' : (r : G) • (g • α) = g • α := by
    have := congrArg (fun a => g • a) hfix
    simpa only [mul_smul, smul_inv_smul] using this
  have h1 := regular_free S heval ⟨r, hRS r.property⟩ hmove hfix'
  have hrG : (r : G) = 1 := congrArg (fun s : S => (s : G)) h1
  exact hr (Subtype.ext hrG)

private theorem quasithin_of_sylow_normalizers {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hnorm : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ (S : Subgroup G) →
      normalizer (R : Set G) ≤ normalizer (S : Set G))
    (hrank : IsStronglyQuasithin (normalizer (S : Set G))) : IsQuasithin G := by
  apply CFSG.Quasithin.isQuasithin_iff_twoLocal.mpr
  rintro M ⟨R, hR, hRp, rfl⟩ p hp ho
  obtain ⟨T, hRT⟩ := hRp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let e := MulAut.conj g
  have hmap : (T : Subgroup G).map e.toMonoidHom = (S : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  have hle : normalizer (R.map e.toMonoidHom : Set G) ≤ normalizer (S : Set G) :=
    hnorm _ (fun h => hR ((map_eq_bot_iff_of_injective R e.injective).mp h))
      ((map_mono hRT).trans_eq hmap)
  have hle' : (normalizer (R : Set G)).map e.toMonoidHom ≤
      normalizer (S : Set G) := by
    rwa [map_equiv_normalizer_eq]
  rw [Theory.GroupTheory.primeRank_equiv p
    (equivMapOfInjective (normalizer (R : Set G)) e.toMonoidHom e.injective)]
  exact (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hle')
    (inclusion_injective hle')).trans (hrank p hp ho)

private theorem regular_sylow_selfCentralizing {G Ω : Type*} [Group G] [Finite G]
    [MulAction G Ω] [FaithfulSMul G Ω] (S : Sylow 2 G) {α β : Ω}
    (hN : normalizer (S : Set G) = MulAction.stabilizer G α)
    (heval : Set.BijOn (fun s : S => (s : G) • β) Set.univ {a | a ≠ α}) :
    centralizer (S : Set G) ≤ (S : Subgroup G) := by
  let C := centralizer (S : Set G)
  have hCp : IsPGroup 2 C := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    have hxα : (x : G) • α = α :=
      MulAction.mem_stabilizer_iff.mp (hN ▸ Subgroup.centralizer_le_normalizer _ x.property)
    have hβ : β ≠ α := by
      simpa using heval.mapsTo (Set.mem_univ (1 : S))
    have hxβ : (x : G) • β ≠ α := by
      rw [← hxα]
      exact (MulAction.injective (x : G)).ne hβ
    obtain ⟨s, _, hs⟩ := heval.surjOn hxβ
    have hpowers : ∀ n : ℕ, (x : G) ^ n • β = (s : G) ^ n • β := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', mul_smul, ih,
          ← mul_smul, ← mem_centralizer_iff.mp x.property _
            ((S : Subgroup G).pow_mem s.property n), mul_smul, ← hs,
          ← mul_smul, ← pow_succ]
    obtain ⟨n, hn⟩ := isPGroup_iff_pow_pow_eq_one.mp S.isPGroup' s
    have hpowβ : (x : G) ^ 2 ^ n • β = β := by
      rw [hpowers, ← coe_pow, hn, coe_one, one_smul]
    refine ⟨n, Subtype.ext ((faithfulSMul_iff (G := G) (α := Ω)).mp inferInstance _ ?_)⟩
    intro a
    by_cases ha : a = α
    · subst a
      exact MulAction.mem_stabilizer_iff.mp
        ((MulAction.stabilizer G α).pow_mem (MulAction.mem_stabilizer_iff.mpr hxα) _)
    · obtain ⟨r, _, rfl⟩ := heval.surjOn ha
      change (x : G) ^ 2 ^ n • ((r : G) • β) = (r : G) • β
      rw [← mul_smul, ← mem_centralizer_iff.mp (C.pow_mem x.property (2 ^ n))
        _ r.property, mul_smul, hpowβ]
  have hsup := S.is_maximal' (S.isPGroup'.to_sup_of_normal_left' hCp
    (Subgroup.centralizer_le_normalizer (S : Set G))) le_sup_left
  exact le_sup_right.trans_eq hsup

private theorem local_of_regular {G Ω : Type*} [Group G] [Finite G]
    [MulAction G Ω] [FaithfulSMul G Ω] (S : Sylow 2 G) {α β : Ω}
    (hN : normalizer (S : Set G) = MulAction.stabilizer G α)
    (heval : Set.BijOn (fun s : S => (s : G) • β) Set.univ {a | a ≠ α})
    (D : Subgroup G) (hD : D ≤ normalizer (S : Set G)) (hcyc : IsCyclic D)
    (hsup : (S : Subgroup G) ⊔ D = normalizer (S : Set G)) :
    IsQuasithin G ∧ centralizer (S : Set G) ≤ (S : Subgroup G) := by
  refine ⟨quasithin_of_sylow_normalizers S
    (regular_normalizer_le (S : Subgroup G) hN heval) ?_,
    regular_sylow_selfCentralizing S hN heval⟩
  intro p hp ho
  exact (cyclic_supplement_rank S D hD hcyc hsup p hp ho).trans (by decide)

private theorem even_of_rankOne {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (S : Sylow 2 G)
    (hfacts : ChapterF.Source.RankOneSylowFacts S)
    (hc : centralizer (S : Set G) ≤ (S : Subgroup G)) : IsEvenCharacteristic G := by
  apply IsEvenCharacteristicAt.all (T := S)
  intro M hM hSM
  exact centralizer_pCore_le_of_normalized 2 (S : Subgroup G) M S.isPGroup' hSM
    (hfacts.unique_maximal M hSM
      (lt_top_iff_ne_top.mpr (twoLocal_ne_top_of_nonabelian_simple hna hM.1))) hc

private theorem nonabelian_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hna : ¬ IsMulCommutative G) : ¬ IsMulCommutative H := by
  intro h
  let := h
  apply hna
  exact ⟨⟨fun a b => e.injective (by simp only [map_mul]; exact mul_comm' _ _)⟩⟩

private theorem even_of_equiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (hH : IsEvenCharacteristic H) : IsEvenCharacteristic G := by
  intro T
  apply (Theory.Quasithin.evenCharacteristicAt_map_iff e (T : Subgroup G)).mpr
  exact hH (T.mapSurjective (f := e.toMonoidHom) e.surjective)

open BenderSuzuki.Converse
open BenderSuzuki.PFchapter1section1

private theorem linear_local (F : Type*) [Field F] [Finite F] [CharP F 2]
    (f : ℕ) (hf : 0 < f) (hcard : Nat.card F = 2 ^ f) :
    IsQuasithin (PSL2 F) ∧
      centralizer (ChapterF.Source.Linear.projectiveSylow F : Set (PSL2 F)) ≤
        (ChapterF.Source.Linear.projectiveSylow F : Subgroup (PSL2 F)) := by
  let S := ChapterF.Source.Linear.projectiveSylow F
  have heven : Even (Nat.card F) := by
    rw [hcard]
    exact (Nat.even_pow' (Nat.ne_of_gt hf)).mpr even_two
  have hodd : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units, hcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (hcard ▸ heven) odd_one
  have hβ : pZero F ≠ pInf F := by
    intro h
    exact PWeyl_notMem_PBorel (F := F)
      (show PWeyl F • pInf F = pInf F from (PWeyl_smul_pInf).trans h)
  have heval := hypothesisA1_Q_regular_on_complement
    (hypothesisA1_psl2 heven hodd) hβ (PTorus_eq (F := F))
  have heval' : Set.BijOn (fun s : S => (s : PSL2 F) • pZero F)
      Set.univ {a | a ≠ pInf F} := by
    exact (congrArg (fun Q : Subgroup (PSL2 F) =>
      Set.BijOn (fun s : Q => (s : PSL2 F) • pZero F) Set.univ {a | a ≠ pInf F})
        (ChapterF.Source.Linear.projectiveSylow_coe F)).mpr heval
  apply local_of_regular S (ChapterF.Source.Linear.projectiveSylow_normalizer F)
    heval' (PTorus F)
  · rw [ChapterF.Source.Linear.projectiveSylow_normalizer]
    exact PTorus_le_PBorel
  · have : IsCyclic (Torus F) := by
      rw [Torus_eq_range]
      exact isCyclic_of_surjective (torHom F).rangeRestrict (torHom F).rangeRestrict_surjective
    change IsCyclic ((Torus F).map (pi F))
    exact isCyclic_of_surjective ((pi F).subgroupMap (Torus F))
      ((pi F).subgroupMap_surjective (Torus F))
  · rw [ChapterF.Source.Linear.projectiveSylow_coe,
      ChapterF.Source.Linear.projectiveSylow_normalizer]
    exact PUnip_sup_PTorus

/-- The linear rank-one family satisfies QT through its actual projective model. -/
public theorem psl2_quasithin {G : Type*} [Group G] [Finite G] {f : ℕ}
    (hf : 2 ≤ f) (hG : ClassicalGroup.IsPSL G 2 (2 ^ f)) : IsQuasithin G := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hG
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact Theory.GroupTheory.isQuasithin_of_equiv e.symm
    (linear_local F f (by omega) hcard).1

/-- The linear rank-one family satisfies E under the consumer's simple-group hypotheses. -/
public theorem psl2_evenCharacteristic {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) {f : ℕ}
    (hf : 2 ≤ f) (hG : ClassicalGroup.IsPSL G 2 (2 ^ f)) : IsEvenCharacteristic G := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hG
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : IsSimpleGroup (PSL2 F) := (MulEquiv.isSimpleGroup_congr e).mp inferInstance
  apply even_of_equiv e
  exact even_of_rankOne (nonabelian_of_equiv e hna)
    (ChapterF.Source.Linear.projectiveSylow F)
    (ChapterF.Source.rankOneSylowFacts_psl2 F f (by omega) hcard _)
    (linear_local F f (by omega) hcard).2

open BenderSuzuki.MatrixGroups
open scoped Matrix

private theorem unitary_standard_local {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (f : ℕ) (hf : 0 < f)
    (hcard : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J) ∧
      ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
        centralizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
          (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨rho, α, S, ⟨D, hD, _, hcyc, _, hsup⟩, hproper, _, hinj, _, _, hN,
    hregular, _⟩ := ChapterF.Source.Unitary.standard_psu_borel_data
      J f hf hcard hconj hstandard
  let Ω := psuOmega J
  let U := ProjectiveSpecialUnitaryMatrixGroup J
  let : MulAction U Ω := MulAction.compHom Ω rho
  let : FaithfulSMul U Ω := ⟨fun {_ _} h => hinj (Equiv.ext h)⟩
  obtain ⟨g, hg⟩ : ∃ g : U, g ∉ normalizer (S : Set U) := by
    by_contra! h
    exact hproper.ne (eq_top_iff.mpr fun g _ => h g)
  let β : Ω := g • α
  have hN' : normalizer (S : Set U) = MulAction.stabilizer U α := hN
  have hβ : β ≠ α := by
    intro h
    apply hg
    rw [hN']
    exact h
  have heval : Set.BijOn (fun s : S => (s : U) • β) Set.univ {a | a ≠ α} := by
    have hmap : ∀ s : S, (s : U) • β ≠ α := by
      intro s
      have hsα : (s : U) • α = α := MulAction.mem_stabilizer_iff.mp
        (hN' ▸ (S : Subgroup U).le_normalizer s.property)
      rw [← hsα]
      exact (MulAction.injective (s : U)).ne hβ
    refine ⟨fun s _ => hmap s, ?_, ?_⟩
    · intro s _ r _ h
      exact ExistsUnique.unique (hregular β ((r : U) • β) hβ (hmap r)) h rfl
    · intro a ha
      obtain ⟨s, hs, _⟩ := hregular β a hβ ha
      exact ⟨s, Set.mem_univ _, hs⟩
  obtain ⟨hqt, hc⟩ := local_of_regular S hN' heval D hD hcyc hsup
  exact ⟨hqt, S, hc⟩

/-- The unitary rank-one family satisfies QT, with 2^f the fixed-field order. -/
public theorem psu3_quasithin {G : Type*} [Group G] [Finite G] {f : ℕ}
    (hf : 2 ≤ f) (hG : ClassicalGroup.IsPSU G 3 (2 ^ f)) : IsQuasithin G := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hG
  obtain ⟨C, hC⟩ := ChapterF.Source.Unitary.FormTransport.exists_standard_basis
    J f (by omega) hcard hconj
  let ep := e.trans (ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup
      (ChapterF.Source.Unitary.FormTransport.standardForm J)) :=
    Finite.of_surjective ep ep.surjective
  exact Theory.GroupTheory.isQuasithin_of_equiv ep.symm
    (unitary_standard_local (ChapterF.Source.Unitary.FormTransport.standardForm J)
      f (by omega) hcard hconj rfl).1

/-- The unitary rank-one family satisfies E through an actual Hermitian basis change. -/
public theorem psu3_evenCharacteristic {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) {f : ℕ}
    (hf : 2 ≤ f) (hG : ClassicalGroup.IsPSU G 3 (2 ^ f)) : IsEvenCharacteristic G := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hG
  obtain ⟨C, hC⟩ := ChapterF.Source.Unitary.FormTransport.exists_standard_basis
    J f (by omega) hcard hconj
  let J₀ := ChapterF.Source.Unitary.FormTransport.standardForm J
  let ep := e.trans (ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective ep ep.surjective
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    (MulEquiv.isSimpleGroup_congr ep).mp inferInstance
  apply even_of_equiv ep
  obtain ⟨S, hc⟩ := (unitary_standard_local J₀ f (by omega) hcard hconj rfl).2
  exact even_of_rankOne (nonabelian_of_equiv ep hna) S
    (ChapterF.Source.rankOneSylowFacts_psu3 J₀ f (by omega) hcard hconj S) hc

end CFSG.Quasithin.MainConverse
