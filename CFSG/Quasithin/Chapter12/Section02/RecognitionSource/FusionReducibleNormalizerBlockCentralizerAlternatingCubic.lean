module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternating
public import Theory.GroupTheory.CoprimeConjugateCore
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CubicCentralizer

public import Theory.GroupTheory.Hall.InvariantCubic
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.fourLetter
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The alternating invariant-core argument from a literal six-letter marking

The marked quotient has the actual local two-core as kernel, sends the local
residual to the embedded A₄, and sends the moved omega-generated module to
the complementary transposition. Its cubic centralizer calculation gives
C_T(B) ≤ QWᵈ. An odd Hall subgroup supplies an invariant cubic B internally.
Coprime action then makes QWᵈ invariant, and its index-two centralizers give
the factorization needed by the existing Frattini contradiction.

The movement and original normalizer consumer are connected below. Constructing
the literal marking from the intrinsic A₆ block and proving local invariance
remain with `qt-d-12216-normalizer-block-centralizer`; this module does not
assert those source inputs. The omega-generated module is never identified
with the separately chosen V.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 3.3.26–31,
printed pp.600–602, especially the first half of 3.3.31.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem core_le_sylow : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

omit [Finite G] in
private theorem join_normalizes_core : L ⊔ (T : Subgroup G) ≤
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
  (L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

private theorem short_residual (hb : ChapterC.IsShort L) :
    Stellmacher.twoResidualAmbient L = L := by
  have hi : Stellmacher.twoResidualSubgroup L = ⊤ := by
    apply top_unique
    apply le_sInf
    rintro N ⟨hn, n, hi⟩
    let := hn
    have hp : IsPGroup 2 (L ⧸ N) := IsPGroup.iff_card.mpr
      ⟨n, by simpa only [index_eq_card] using hi⟩
    rw [hb.twoPerfect N hn hp]
  rw [Stellmacher.twoResidualAmbient, hi, ← MonoidHom.range_eq_map, range_subtype]

/-- Once the conjugate join is invariant and has index two, its centralizer
factorization follows from the two conjugate index-two centralizers. -/
theorem alternatingCoreJoin_factorization_of_invariant_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) {d : G} (hd : d ∈ normalizer (T : Set G))
    (hinv : d ∈ normalizer (alternatingCoreJoin T L d : Set G))
    (hi : ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (alternatingCoreJoin T L d) = 2) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = blockOmegaModule T L ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
        ((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom : Set G)) := by
  have hmove : ¬ (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    intro he
    have hs : alternatingCoreJoin T L d = (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      sup_eq_left.mpr he
    rw [hs, relIndex_self] at hi
    omega
  exact eq_sup_inf_centralizer_of_invariant_index_two (alternatingCoreJoin T L d)
    ((L ⊔ (T : Subgroup G)).pCoreIn 2) (blockOmegaModule T L) (MulAut.conj d⁻¹)
    (alternatingCoreJoin_centralizer h D hescape hb hd) (blockOmegaModule_le_core h)
    (mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hinv)) hi hmove

/-- The source cubic subgroup supplies all invariant-core clauses once its
centralizer containment and the order-two moved image have been established. -/
theorem alternatingInvariantCoreGeometry_of_cubic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) {d : G} (hd : d ∈ normalizer (T : Set G))
    (B : Subgroup G) (hBX : B ≤ blockLocalResidual T L) (hB3 : Nat.card B = 3)
    (hdB : d ∈ normalizer (B : Set G))
    (hi : ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (alternatingCoreJoin T L d) = 2)
    (hC : (T : Subgroup G) ⊓ centralizer (B : Set G) ≤ alternatingCoreJoin T L d) :
    AlternatingInvariantCoreGeometry T L d := by
  have hBL : B ≤ L := hBX.trans ((map_subtype_le _).trans inf_le_left)
  have hBW : B ≤ normalizer (blockOmegaModule T L : Set G) :=
    (hBL.trans le_sup_left).trans join_normalizes_blockOmegaModule
  have hBQ : B ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (hBL.trans le_sup_left).trans join_normalizes_core
  have hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, B⁆ ≤ blockOmegaModule T L := by
    apply (commutator_mono le_rfl hBL).trans
    rw [commutator_comm]
    apply (ChapterC.c6_3_commutator_core_bound L (T : Subgroup G)
      D.sylow_normalizes_component (short_residual hb)).1.trans
    change ⁅L.pCoreIn 2, L⁆ ≤ blockOmegaModule T L
    rw [← block_module_eq_commutator]
    exact blockU_le_blockOmegaModule h D hescape hb
  let : Group.IsNilpotent ((L ⊔ (T : Subgroup G)).pCoreIn 2) :=
    (isPGroup_pCoreIn 2 _).isNilpotent
  have hcop : Nat.Coprime (Nat.card B) (Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2)) := by
    obtain ⟨n, hn⟩ := (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).exists_card_eq
    rw [hB3, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hm := map_join_eq_of_coprime_centralizer_cover (T : Subgroup G)
    ((L ⊔ (T : Subgroup G)).pCoreIn 2) (blockOmegaModule T L) B (MulAut.conj d⁻¹)
    core_le_sylow (blockOmegaModule_le_core h)
    (le_sup_right.trans join_normalizes_blockOmegaModule) hBQ hBW
    (mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hd))
    (mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hdB))
    inferInstance hcop hcomm hi hC
  have hinv : d ∈ normalizer (alternatingCoreJoin T L d : Set G) := by
    have hi' : d⁻¹ ∈ normalizer (alternatingCoreJoin T L d : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr hm
    simpa only [inv_inv] using (normalizer _).inv_mem hi'
  exact ⟨hinv, alternatingCoreJoin_centralizer h D hescape hb hd,
    alternatingCoreJoin_factorization_of_invariant_index h D hescape hb hd hinv hi, hi⟩

/-- The literal six-letter quotient data needed at the first step of 3.3.31.
The kernel is the actual two-core; all subgroup images use the inclusion in LT.
This is an input contract, not an asserted construction of the marking. -/
structure AlternatingSixLocalMarking (T : Sylow 2 G) (L : Subgroup G) (d : G) where
  quotient : ↥(L ⊔ (T : Subgroup G)) →* Equiv.Perm (Fin 6)
  kernel : quotient.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))
  local_image : ((blockLocalResidual T L).subgroupOf (L ⊔ (T : Subgroup G))).map quotient =
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.K
  sylow_image : ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map quotient ≤
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1
  moved_image : (((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom).subgroupOf
    (L ⊔ (T : Subgroup G))).map quotient =
      zpowers Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap45

/-- The marked complementary transposition has precisely the source relative
index. No quotient map or kernel is changed in this transport. -/
theorem AlternatingSixLocalMarking.coreJoin_index {d : G}
    (m : AlternatingSixLocalMarking T L d)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : d ∈ normalizer (T : Set G)) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (alternatingCoreJoin T L d) = 2 := by
  have hWdT : (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom ≤ (T : Subgroup G) := by
    rw [← mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hd)]
    exact map_mono ((blockOmegaModule_le_core h).trans core_le_sylow)
  have hSH : alternatingCoreJoin T L d ≤ L ⊔ (T : Subgroup G) :=
    sup_le (pCoreIn_le 2 _) (hWdT.trans le_sup_right)
  rw [← relIndex_subgroupOf hSH, ← m.kernel, relIndex_ker]
  rw [alternatingCoreJoin, subgroupOf_sup (pCoreIn_le 2 _) (hWdT.trans le_sup_right),
    Subgroup.map_sup, ← m.kernel, map_ker_self, bot_sup_eq, m.moved_image,
    Nat.card_zpowers]
  exact (show Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap45.IsSwap from
    ⟨4, 5, by decide, rfl⟩).orderOf



/-- The actual cubic centralizer lies in QWᵈ. The proof uses the marked
quotient, its literal two-core kernel, and the order of B; it does not assume
the desired containment or invariance of the conjugate join. -/
theorem AlternatingSixLocalMarking.sylow_centralizer_cubic_le {d : G}
    (m : AlternatingSixLocalMarking T L d)
    (B : Subgroup G) (hBX : B ≤ blockLocalResidual T L) (hB3 : Nat.card B = 3) :
    (T : Subgroup G) ⊓ centralizer (B : Set G) ≤ alternatingCoreJoin T L d := by
  let H := L ⊔ (T : Subgroup G)
  let q := m.quotient
  have hBL : B ≤ L := hBX.trans ((map_subtype_le _).trans inf_le_left)
  obtain ⟨b, hb3⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hB3])
  let bH : H := ⟨b, (show L ≤ H from le_sup_left) (hBL b.property)⟩
  have hbH : orderOf bH = 3 := by
    rw [← Subgroup.orderOf_coe bH]
    exact (Subgroup.orderOf_coe b).trans hb3
  have hk : IsPGroup 2 q.ker := by
    rw [show q.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf H from m.kernel]
    exact (isPGroup_pCoreIn 2 _).comap_subtype
  have hc3 : orderOf (q bH) = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk bH (by rw [hbH]; decide)).trans hbH
  have hcK : q bH ∈ Theory.SpecificGroups.SymmetricSix.BinaryFlags.K := by
    rw [← m.local_image]
    exact mem_map_of_mem q (hBX b.property)
  let P := ((T : Subgroup G).subgroupOf H).map q
  have hp : IsPGroup 2 P := T.isPGroup'.comap_subtype.map q
  have hPc := Theory.SpecificGroups.SymmetricSix.BinaryFlags.twoGroup_inf_cubic_centralizer_le
    P hp m.sylow_image hcK (hc3 ▸ pow_orderOf_eq_one (q bH))
    (fun he => by rw [he, orderOf_one] at hc3; omega)
  rintro t ⟨htT, htB⟩
  let tH : H := ⟨t, (show (T : Subgroup G) ≤ H from le_sup_right) htT⟩
  have htC : q tH ∈ centralizer ({q bH} : Set (Equiv.Perm (Fin 6))) := by
    intro c hc
    have he : c = q bH := Set.mem_singleton_iff.mp hc
    subst c
    have hbt : bH * tH = tH * bH := Subtype.ext (htB b b.property)
    simpa only [map_mul] using congrArg q hbt
  have htimage := hPc ⟨mem_map_of_mem q htT, htC⟩
  rw [← m.moved_image] at htimage
  obtain ⟨w, hw, he⟩ := htimage
  have hker : tH * w⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hcore : t * (w : G)⁻¹ ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [m.kernel] at hker
    exact hker
  have htS : t * (w : G)⁻¹ * w ∈ alternatingCoreJoin T L d :=
    mul_mem (mem_sup_left hcore) (mem_sup_right hw)
  simpa only [inv_mul_cancel_right] using htS

/-- The source terminal contradiction from an actual marked quotient and an
invariant cubic. Both geometric clauses are proved, rather than requested
as callbacks. Constructing the marking and choosing the cubic remain upstream. -/
theorem false_of_alternating_six_marking_cubic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hb : ChapterC.IsAlternatingBlock L 6) {d : G} (ho : Odd (orderOf d))
    (hd : d ∈ normalizer (T : Set G)) (hout : d ∉ normalizer (L : Set G))
    (m : AlternatingSixLocalMarking T L d)
    (B : Subgroup G) (hBX : B ≤ blockLocalResidual T L) (hB3 : Nat.card B = 3)
    (hdB : d ∈ normalizer (B : Set G)) : False := by
  have hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) :=
    fun hn => hout (hn hd)
  exact false_of_alternating_invariant_core_geometry h D hb.2.1 ho hd hout
    (alternatingInvariantCoreGeometry_of_cubic h D hescape hb.2.1 hd B hBX hB3 hdB
      (m.coreJoin_index h hd) (m.sylow_centralizer_cubic_le B hBX hB3))

/-- The marked local residual is solvable of order 2^n·3. The proof uses the
literal A₄ image and two-group kernel, not an ambient normality assumption. -/
theorem AlternatingSixLocalMarking.local_residual_structure {d : G}
    (m : AlternatingSixLocalMarking T L d) :
    Group.IsSolvable (blockLocalResidual T L) ∧
      ∃ n : ℕ, Nat.card (blockLocalResidual T L) = 2 ^ n * 3 := by
  let X := blockLocalResidual T L
  let H := L ⊔ (T : Subgroup G)
  have hXH : X ≤ H := ((map_subtype_le _).trans inf_le_left).trans le_sup_left
  let f := m.quotient.comp (inclusion hXH)
  have hk : IsPGroup 2 m.quotient.ker := by
    rw [m.kernel]
    exact (isPGroup_pCoreIn 2 _).comap_subtype
  have hf : IsPGroup 2 f.ker := hk.comap_of_injective _ (Set.inclusion_injective hXH)
  have hr : f.range = Theory.SpecificGroups.SymmetricSix.BinaryFlags.K := by
    rw [MonoidHom.range_comp, inclusion_range]
    exact m.local_image
  let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
  let : Group.IsSolvable Theory.SpecificGroups.SymmetricSix.BinaryFlags.K :=
    Group.isSolvable_of_isSolvable_injective
      (f := Theory.SpecificGroups.SymmetricSix.BinaryFlags.fourLetterEquiv.toMonoidHom)
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.fourLetterEquiv.injective
  let : Group.IsSolvable f.range := Group.isSolvable_of_isSolvable_injective
    (f := (MulEquiv.subgroupCongr hr).toMonoidHom) (MulEquiv.subgroupCongr hr).injective
  let : Group.IsNilpotent f.ker := hf.isNilpotent
  refine ⟨Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by simp), ?_⟩
  obtain ⟨n, hn⟩ := hf.exists_card_eq
  refine ⟨n + 2, ?_⟩
  calc
    Nat.card X = Nat.card f.ker * f.ker.index := f.ker.card_mul_index.symm
    _ = 2 ^ n * 12 := by rw [hn, index_ker, hr, Theory.SpecificGroups.SymmetricSix.BinaryFlags.card_K]
    _ = 2 ^ (n + 2) * 3 := by ring

/-- The odd actor fixes a genuine cubic subgroup in the marked local residual.
This discharges the Sylow-choice step in source 3.3.31. -/
theorem AlternatingSixLocalMarking.exists_invariant_cubic {d : G}
    (m : AlternatingSixLocalMarking T L d) (ho : Odd (orderOf d))
    (hdX : d ∈ normalizer (blockLocalResidual T L : Set G)) :
    ∃ B : Subgroup G, B ≤ blockLocalResidual T L ∧ Nat.card B = 3 ∧
      d ∈ normalizer (B : Set G) := by
  obtain ⟨hsolv, n, hn⟩ := m.local_residual_structure
  exact Subgroup.OddHall.exists_invariant_cubic_of_odd_actor _ hsolv hn ho hdX

/-- The alternating terminal contradiction with the cubic chosen internally. -/
theorem false_of_alternating_six_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hb : ChapterC.IsAlternatingBlock L 6) {d : G} (ho : Odd (orderOf d))
    (hd : d ∈ normalizer (T : Set G)) (hout : d ∉ normalizer (L : Set G))
    (m : AlternatingSixLocalMarking T L d)
    (hdX : d ∈ normalizer (blockLocalResidual T L : Set G)) : False := by
  obtain ⟨B, hBX, hB3, hdB⟩ := m.exists_invariant_cubic ho hdX
  exact false_of_alternating_six_marking_cubic h D hb ho hd hout m B hBX hB3 hdB

/-- Remaining model construction in the A₆ branch. This asks for the literal
quotient marking only after the C.6 actor and local normality have been
constructed. The final owner `qt-d-12216-normalizer-block-centralizer` must
construct this marking and discharge local invariance before source assembly. -/
@[expose] def AlternatingSixLocalMarkingSource
    (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
    BlockLocalInvariance T L → ChapterC.IsAlternatingBlock L 6 →
    ∀ d : G, Odd (orderOf d) → d ∈ normalizer (T : Set G) →
      d ∉ normalizer (L : Set G) →
      ¬ (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 →
      blockLocalResidual T L ⊔ (T : Subgroup G) ≤ normalizer
        ((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom : Set G) →
      Nonempty (AlternatingSixLocalMarking T L d)

/-- Construct the full invariant-core geometry from actual quotient markings.
The movement, cubic choice, centralizer bound and factorization are internal. -/
theorem alternatingInvariantCoreGeometrySource_of_six_markings
    (markings : AlternatingSixLocalMarkingSource T L V) :
    AlternatingInvariantCoreGeometrySource T L V := by
  intro h D structural hnone hfixed hescape hi hb
  obtain ⟨d, ho, hd, hout, hmove, hnormal, _⟩ :=
    exists_odd_alternating_omega_movement h D hescape hi hb
  obtain ⟨m⟩ := markings h D structural hnone hfixed hescape hi hb d ho hd hout hmove hnormal
  obtain ⟨B, hBX, hB3, hdB⟩ := m.exists_invariant_cubic ho ((hi.1 (Or.inl hb)).1 hd)
  exact ⟨d, ho, hd, hout,
    alternatingInvariantCoreGeometry_of_cubic h D hescape hb.2.1 hd B hBX hB3 hdB
      (m.coreJoin_index h hd) (m.sylow_centralizer_cubic_le B hBX hB3)⟩

/-- The unchanged alternating block-centralizer contract with only the literal
model marking outstanding. This is not yet an unconditional source theorem. -/
theorem alternatingBlockCentralizerSource_of_six_markings
    (markings : AlternatingSixLocalMarkingSource T L V) :
    AlternatingBlockCentralizerSource T L V :=
  alternatingBlockCentralizerSource_of_invariant_core_geometry
    (alternatingInvariantCoreGeometrySource_of_six_markings markings)

/-- Actual original normalizer consumer. Block reduction, local invariance,
the nonalternating branch and construction of the marking retain their owners. -/
theorem sylow_normalizer_le_of_alternating_six_markings
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (reduction : BlockReductionSource T L V)
    (localSource : BlockLocalInvarianceSource T L V)
    (nonalternating : NonalternatingBlockCentralizerSource T L V)
    (markings : AlternatingSixLocalMarkingSource T L V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_local_block_branches h D structural hnone hfixed reduction
    localSource nonalternating (alternatingBlockCentralizerSource_of_six_markings markings)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
