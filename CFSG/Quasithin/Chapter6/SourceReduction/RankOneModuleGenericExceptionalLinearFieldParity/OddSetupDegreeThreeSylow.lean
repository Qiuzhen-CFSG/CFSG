module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupPointSylowAction
public import Theory.GroupTheory.PCoreNormalizerAction.Kernel
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# The full quotient-centralizer Sylow in degree three

For the literal PSL₃(4) residual, odd-rank addition leaves seven-rank at
most one in its quotient-action kernel C_K. In field degree three the
original Cartan has order seven. The full C_K Sylow construction and
its disjoint commuting local factors therefore force the L/O₂(L) action
kernel to vanish. This proves preservation of the original chosen point,
without a module-invariance premise. The point action and cyclicity then
show that the entire Sylow equals the original Cartan.

The same Sylow supplies the residual-normalizer Frattini product and TI
under its normalizer. This does not infer TI under the full Frattini
product. Higher odd degrees, residual/global TI, and parity assembly
remain with qt-d-1222-linear-field-parity. The independent Suzuki input
is retained as solvability of the literal quotient-action kernel.
Source: Aschbacher–Smith, proof of 5.1.17, printed p.640
(refs/quasithin.pdf), specialized to its eventual degree-three branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
local instance degreeThreeSylowSevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The residual consumes one unit of seven-rank, leaving at most one in C_K. -/
theorem residual_kernel_seven_rank_le_one (K : Subgroup G)
    (hN : IsStronglyQuasithin (normalizer (K : Set G)))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    primeRank 7 ((normalizerQuotientAction K (pCore 2 K)).ker.map
      (normalizer (K : Set G)).subtype) ≤ 1 := by
  let N := normalizer (K : Set G)
  let C := (normalizerQuotientAction K (pCore 2 K)).ker.map N.subtype
  have hz : Nat.Coprime 7 (Nat.card (center (K ⧸ pCore 2 K))) := by
    obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)]
    simp
  have hr := pCoreActionKernelIn_rank_add_le K N (by decide : Odd 7) K.le_normalizer hz
  have he : pCoreActionKernelIn 2 K N = C :=
    inf_eq_right.mpr (map_subtype_le _)
  rw [he] at hr
  have hu : primeRank 7 N ≤ 2 := hN 7 (by decide) (by decide)
  have hd : 7 ∣ Nat.card K := by
    apply dvd_trans _ (pCore 2 K).card_quotient_dvd_card
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let := Fintype.ofFinite Matrix.PSL3Four.F
    let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
      (by rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,
        hF,Matrix.PSL3Four.card_F])
    rw [Nat.card_congr (e.trans (Atlas.fieldEquivPSL 3 eF)).toEquiv,
      Matrix.PSL3Four.card_PSL]
    decide
  have hp : primeRank 7 K ≠ 0 := fun h0 => PrimeRank.eq_zero_iff_not_dvd_card.mp h0 hd
  change primeRank 7 C ≤ 1
  omega

private theorem disjoint_commuting_seven_factor_eq_bot
    (C A Q : Subgroup G) (hAC : A ≤ C) (hQC : Q ≤ C)
    (hr : primeRank 7 C ≤ 1) (hd : 7 ∣ Nat.card A)
    (hQ : IsPGroup 7 Q) (hdis : Disjoint A Q)
    (hc : Q ≤ centralizer (A : Set G)) : Q = ⊥ := by
  have hsum := A.primeRank_sup_eq_add_of_disjoint_commuting Q hdis
    (le_centralizer_iff.mp hc) 7
  have hu := (primeRank_mono 7 (sup_le hAC hQC)).trans hr
  have ha : primeRank 7 A ≠ 0 := fun h0 => PrimeRank.eq_zero_iff_not_dvd_card.mp h0 hd
  have hq : primeRank 7 Q = 0 := by omega
  have hnd := PrimeRank.eq_zero_iff_not_dvd_card.mp hq
  obtain ⟨k,hk⟩ := hQ.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hh
    exact hnd (hk ▸ dvd_pow_self 7 hh)
  exact card_eq_one.mp (by simpa only [hk0,pow_zero] using hk)

variable {T : Sylow 2 G} {L W H A B : Subgroup G}

/-- In degree three the original Cartan is a full C_K Sylow, with the
actual point action, local kernel, Frattini product and normalizer TI. -/
theorem fundamental_degree_three_full_sylow_point_action
    (h : Input KnownSimple.IsKnownSimple T L W 3)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup 3)
    (c : CartanPair T L H A B) :
    let N := normalizer (residual H : Set G)
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map N.subtype
    let Cₗ := (normalizerQuotientAction L (pCore 2 L)).ker.map
      (normalizer (L : Set G)).subtype
    let Z := (setup T L D.moduleSubgroup H A).V₁
    ∃ P : Sylow 7 C,
      (P : Subgroup C).map C.subtype = A ∧
      (P : Subgroup C).map C.subtype ⊓ Cₗ = ⊥ ∧
      (P : Subgroup C).map C.subtype ≤ normalizer (Z : Set G) ∧
      (P : Subgroup C).map C.subtype = A ⊔
        ((P : Subgroup C).map C.subtype ⊓ centralizer (Z : Set G)) ∧
      N = C ⊔ (N ⊓ normalizer ((P : Subgroup C).map C.subtype : Set G)) ∧
      ∀ g ∈ normalizer ((P : Subgroup C).map C.subtype : Set G),
        Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨ Z.map (MulAut.conj g).toMonoidHom = Z := by
  obtain ⟨p,hp,E,P,R,hp2,ho,hEA,hE,hEP,hR,hlocal,hdis,hcent,hfactor⟩ :=
    residual_kernel_sylow_local_factors h hH hK hnf hm hsolv c (by decide)
  have hA : Nat.card A = 7 := by
    simpa using (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hp7 : p = 7 := by
    have hd : p ∣ 7 := hA ▸ hE ▸ card_dvd_of_le hEA
    exact ((by decide : Nat.Prime 7).eq_one_or_self_of_dvd p hd).resolve_left
      (Fact.out : Nat.Prime p).ne_one
  have hE7 : Nat.card E = 7 := hE.trans hp7
  clear hE
  subst p
  let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
    (normalizer (residual H : Set G)).subtype
  let Cₗ := (normalizerQuotientAction L (pCore 2 L)).ker.map
    (normalizer (L : Set G)).subtype
  let PG := (P : Subgroup C).map C.subtype
  let RA := (R : Subgroup A).map A.subtype
  let Z := (setup T L D.moduleSubgroup H A).V₁
  let Z₀ := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C
  have hEAeq : E = A := eq_of_le_of_card_ge hEA (by omega)
  have hAP : A ≤ PG := hEAeq ▸ hEP
  have hRA : RA = A := hR.trans (inf_eq_right.mpr hAP)
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_maximal
  have horbit : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (hH.1.1.2.trans (le_normalizer_residual H))) (le_componentOrbit _ _)
  rw [horbit] at hmax
  have hr : primeRank 7 C ≤ 1 := residual_kernel_seven_rank_le_one (residual H)
    (h.qtke.twoLocal_sqtk hmax.1).stronglyQuasithin (linear_residual_quotient hm)
  have hker : PG ⊓ Cₗ = ⊥ := by
    apply disjoint_commuting_seven_factor_eq_bot C RA (PG ⊓ Cₗ)
      ((hR.le.trans inf_le_left).trans (map_subtype_le _))
      (inf_le_left.trans (map_subtype_le _)) hr (by rw [hRA,hA])
      ((P.isPGroup'.map C.subtype).of_injective (inclusion inf_le_left)
        (inclusion_injective inf_le_left)) hdis
    exact (le_inf inf_le_left (inf_le_right.trans (map_subtype_le _))).trans hcent
  have hAZ : A ≤ normalizer (Z : Set G) :=
    (c.left_le.trans (fundamental_point_normalizer D h.sylow_normalizes h.linear
      (by decide) hnat).ge).trans inf_le_right
  have hPZ : PG ≤ normalizer (Z : Set G) := by
    change PG = (PG ⊓ centralizer (Z₀ : Set G)) ⊔ RA ⊔ (PG ⊓ Cₗ) at hfactor
    rw [hker,sup_bot_eq,hRA] at hfactor
    exact hfactor.le.trans (sup_le
      ((inf_le_right.trans (centralizer_le (inf_le_left.trans (le_conjugateSpanBy _ _)))).trans
        (Subgroup.centralizer_le_normalizer _)) hAZ)
  have hsplit := (fundamental_primitive_sylow_point_stabilizer D h.sylow_normalizes
    h.linear (by decide) (by decide) hnat c ho PG (P.isPGroup'.map C.subtype) R
      (hRA.le.trans hAP)).1
  change PG ⊓ normalizer (Z : Set G) = RA ⊔ (PG ⊓ centralizer (Z : Set G)) at hsplit
  rw [inf_eq_left.mpr hPZ,hRA] at hsplit
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  let : IsCyclic PG := isCyclic_of_surjective
    (C.subtype.subgroupMap (P : Subgroup C)) (C.subtype.subgroupMap_surjective _)
  have hcentral : PG ⊓ centralizer (Z : Set G) = ⊥ := by
    apply disjoint_commuting_seven_factor_eq_bot C A (PG ⊓ centralizer (Z : Set G))
      (hAP.trans (map_subtype_le _)) (inf_le_left.trans (map_subtype_le _)) hr
      (by rw [hA]) ((P.isPGroup'.map C.subtype).to_le inf_le_left)
      ((fundamental_cartan_point_disjoint_centralizer D h.sylow_normalizes h.linear
        (by decide) (by decide) hnat c).mono_right inf_le_right)
    exact inf_le_left.trans ((le_centralizer PG).trans (centralizer_le hAP))
  have hpeq : PG = A := by simpa only [hcentral,sup_bot_eq] using hsplit
  refine ⟨P,hpeq,hker,hPZ,hsplit,residual_normalizer_kernel_sylow_factorization P,?_⟩
  intro g hg
  exact fundamental_point_ti_under_primitive_actor_normalizer D h.sylow_normalizes h.linear
    (by decide) hnat c (by decide) (by decide) ho A PG le_rfl hA hAP hPZ hg

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
