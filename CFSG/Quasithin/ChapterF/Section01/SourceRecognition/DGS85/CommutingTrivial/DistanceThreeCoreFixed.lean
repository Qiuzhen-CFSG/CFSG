module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCoreSection
public import Theory.GroupAction.RankTwoCosetGeometry.SecondBallKernel
public import Theory.Representation.BinaryConjugationSection.SL2OddCentralizers
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct

/-!
# Odd centralizers in the distance-three core intersection

Full-stabilizer normality identifies `N = Q_alpha ∩ Q_x` with
`Q_beta ∩ G_beta^(2)` and places N in every neighboring two-core.
The nonbinary natural quotient Q_beta/N then puts every nontrivial odd
local actor's centralizer inside N. This radius-two bound transports to
the whole beta vertex orbit, including alpha-minus-one.

For an odd torus T, the bound `[N,O²(L_beta)] ≤ V_beta` and coprime action
give `N = [V_beta,T] × C_(Q_beta)(T)`. The factors commute because N
centralizes V_beta. This is a decomposition of N; the larger two-natural
splitting of Q/Z is a subsequent step. The original reduced-graph application
is `DistanceThreeCoreTorus`.

Source: DGS, *Groups and Graphs* (1985), §9.10(1a)--(1b), (3), and the
coprime decompositions used in (4), printed pp.147--148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A full-stabilizer-normal intersection of the two neighboring cores is
exactly the beta core inside the radius-two kernel. -/
theorem core_intersection_eq_second_kernel
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta x : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) (hbx : (graph (family P)).Adj beta x)
    (hNQ : Q (family P) a ⊓ Q (family P) x ≤ Q (family P) beta)
    (hNn : stabilizer (family P) beta ≤ normalizer
      ((Q (family P) a ⊓ Q (family P) x : Subgroup G) : Set G)) :
    Q (family P) a ⊓ Q (family P) x = Q (family P) beta ⊓ ballKernel (family P) beta 2 := by
  let Γ := family P
  let := finite_endpoints h
  let N := Q Γ a ⊓ Q Γ x
  have hNK : N ≤ ballKernel Γ beta 2 := by
    let : (N.subgroupOf (stabilizer Γ beta)).Normal := normal_subgroupOf_of_le_normalizer hNn
    have hc : N.subgroupOf (stabilizer Γ beta) ≤
        ((ballKernel Γ beta 1 ⊓ ballKernel Γ a 1).subgroupOf (stabilizer Γ beta)).normalCore :=
      normal_le_normalCore.mpr (fun _ hz =>
        ⟨(source_Z_Q_U h beta).2 (hNQ hz),(source_Z_Q_U h a).2 hz.1⟩)
    rw [←ballKernel_two_eq_normalCore Γ hab.symm] at hc
    intro z hz
    exact hc (show (⟨z,Q_le_stabilizer Γ beta (hNQ hz)⟩ : stabilizer Γ beta) ∈
      N.subgroupOf (stabilizer Γ beta) from hz)
  apply le_antisymm (le_inf hNQ hNK)
  let C := Q Γ beta ⊓ ballKernel Γ beta 2
  have hp : IsPGroup 2 C := (isPGroup_pCoreIn 2 _).to_le inf_le_left
  exact le_inf
    (two_subgroup_le_Q Γ a (source_kernel_sylow h hB hS a) hp
      (inf_le_right.trans (ballKernel_succ_le Γ hab.symm 1)))
    (two_subgroup_le_Q Γ x (source_kernel_sylow h hB hS x) hp
      (inf_le_right.trans (ballKernel_succ_le Γ hbx 1)))


/-- The same intersection lies in every neighboring two-core. -/
theorem core_intersection_le_neighbor_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta x : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) (hbx : (graph (family P)).Adj beta x)
    (hNQ : Q (family P) a ⊓ Q (family P) x ≤ Q (family P) beta)
    (hNn : stabilizer (family P) beta ≤ normalizer
      ((Q (family P) a ⊓ Q (family P) x : Subgroup G) : Set G))
    {z : Vertex (family P)} (hz : (graph (family P)).Adj beta z) :
    Q (family P) a ⊓ Q (family P) x ≤ Q (family P) z := by
  let := finite_endpoints h
  have hN := core_intersection_eq_second_kernel h hB hS hab hbx hNQ hNn
  exact two_subgroup_le_Q (family P) z (source_kernel_sylow h hB hS z)
    ((isPGroup_pCoreIn 2 _).to_le inf_le_left)
    ((hN.le.trans inf_le_right).trans (ballKernel_succ_le (family P) hz 1))

/-- Naturality of the literal core quotient places each odd centralizer
inside the two-core intersection, retaining the fixed part of that kernel. -/
theorem core_section_odd_centralizer
    {a beta x : Vertex (family P)}
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hsec : CoreQuotientSection (family P) a beta x F eβ)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (D : Subgroup G) (hDH : D ≤ graphLocalGroup (family P) beta)
    (ho : Odd (Nat.card D)) (hne : D ≠ ⊥) :
    Q (family P) beta ⊓ centralizer (D : Set G) =
      (Q (family P) a ⊓ Q (family P) x) ⊓ centralizer (D : Set G) := by
  obtain ⟨hN,hcard,hElem,σ,d,hd,hnat⟩ := hsec
  let := hN
  let := hElem
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨E,hE⟩ := hnat n hn hF
  let H := graphLocalGroup (family P) beta
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective,QuotientGroup.ker_mk']
  exact BinaryConjugationSection.natural_odd_centralizer_eq_kernel_centralizer
    (F := F) (W := Additive (Q (family P) beta ⧸
      (Q (family P) a ⊓ Q (family P) x).subgroupOf (Q (family P) beta))) H _ _ q
    (hk ▸ pCore_isPGroup) σ d E hE D hDH ho hne

private theorem finite_coprime_decomposition (N T : Subgroup G) [Finite N] [Finite T]
    (hn : T ≤ normalizer (N : Set G)) (hs : Group.IsSolvable N)
    (hc : Nat.Coprime (Nat.card T) (Nat.card N)) :
    N = ⁅N,T⁆ ⊔ (N ⊓ centralizer (T : Set G)) := by
  let : Normalizes T N := ⟨hn⟩
  have he := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := N) (A := T) hs hc
  have hm := congrArg (fun U : Subgroup N => U.map N.subtype) he
  rw [Subgroup.map_sup,commutatorAction_subgroup_conj_map_eq_commutator N T hn,
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn N T hn,
    map_subgroupOf_eq_of_le (show subgroupCentralizerIn N T ≤ N from inf_le_left),
    ←MonoidHom.range_eq_map,range_subtype,sup_comm] at hm
  exact hm.symm

/-- The actual core-intersection splits into the torus displacement of V and
its fixed subgroup. This uses (1a), not an assumed splitting of Q/Z. -/
theorem middle_core_torus_decomposition
    (h : LocallyRankOneTriple P B)
    {a beta x : Vertex (family P)}
    (hN : Q (family P) a ⊓ Q (family P) x =
      Q (family P) beta ⊓ centralizer (V (family P) beta 1 : Set G))
    (hVN : V (family P) beta 1 ≤ Q (family P) a ⊓ Q (family P) x)
    (hNn : stabilizer (family P) beta ≤ normalizer
      ((Q (family P) a ⊓ Q (family P) x : Subgroup G) : Set G))
    (hres : ⁅Q (family P) a ⊓ Q (family P) x,
      (pResidual 2 (graphLocalGroup (family P) beta)).map
        (graphLocalGroup (family P) beta).subtype⁆ ≤ V (family P) beta 1)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hsec : CoreQuotientSection (family P) a beta x F eβ)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (T : Subgroup G) (hTH : T ≤ graphLocalGroup (family P) beta)
    (ho : Odd (Nat.card T)) (hne : T ≠ ⊥) :
    let N := Q (family P) a ⊓ Q (family P) x
    let V₀ := V (family P) beta 1
    let D := Q (family P) beta ⊓ centralizer (T : Set G)
    N = V₀ ⊔ D ∧ ⁅N,T⁆ = ⁅V₀,T⁆ ∧
      N = ⁅V₀,T⁆ ⊔ D ∧ Disjoint ⁅V₀,T⁆ D ∧ ⁅⁅V₀,T⁆,D⁆ = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  let N := Q Γ a ⊓ Q Γ x
  let V₀ := V Γ beta 1
  let D := Q Γ beta ⊓ centralizer (T : Set G)
  let H := graphLocalGroup Γ beta
  have hNQ : N ≤ Q Γ beta := hN.le.trans inf_le_left
  have hNC : N ≤ centralizer (V₀ : Set G) := hN.le.trans inf_le_right
  let : Finite (Q Γ beta) := Finite.of_injective
    (inclusion (Q_le_stabilizer Γ beta)) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion hNQ) (inclusion_injective _)
  let : Finite V₀ := Finite.of_injective (inclusion hVN) (inclusion_injective _)
  let : Finite T := Finite.of_injective
    (inclusion (hTH.trans (sylowGenerated_le _))) (inclusion_injective _)
  have hp : IsPGroup 2 N := (isPGroup_pCoreIn 2 _).to_le hNQ
  have hcop : Nat.Coprime (Nat.card T) (Nat.card N) :=
    by
      obtain ⟨k,hk⟩ := hp.exists_card_eq
      rw [hk]
      exact ho.coprime_two_right.pow_right k
  have hTN : T ≤ normalizer (N : Set G) := (hTH.trans (sylowGenerated_le _)).trans hNn
  have hTV : T ≤ normalizer (V₀ : Set G) :=
    (hTH.trans (sylowGenerated_le _)).trans (stabilizer_normalizes_V Γ beta 1)
  have hTR : T ≤ (pResidual 2 H).map H.subtype := by
    intro t ht
    let l : H := ⟨t,hTH ht⟩
    change H.subtype l ∈ (pResidual 2 H).map H.subtype
    apply mem_map_of_mem H.subtype
    apply mem_pResidual_of_orderOf_coprime
    have htodd : Odd (orderOf l) := by
      rw [Subgroup.orderOf_mk]
      simpa only [Subgroup.orderOf_mk] using
        ho.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨t,ht⟩ : T))
    exact htodd.coprime_two_left
  have hfix : D = N ⊓ centralizer (T : Set G) :=
    core_section_odd_centralizer eβ hsec hn hF T hTH ho hne
  have hDN : D ≤ N := hfix.le.trans inf_le_left
  have hdecomp := finite_coprime_decomposition N T hTN (@IsNilpotent.to_isSolvable N _ hp.isNilpotent) hcop
  rw [←hfix] at hdecomp
  have hdisp : ⁅N,T⁆ ≤ V₀ := (commutator_mono le_rfl hTR).trans hres
  have hNV : N = V₀ ⊔ D := by
    apply le_antisymm
    · rw [hdecomp]
      exact sup_le (hdisp.trans le_sup_left) le_sup_right
    · exact sup_le hVN hDN
  have hUV : ⁅V₀,T⁆ ≤ V₀ := le_normalizer_iff_commutator_le_left.mp hTV
  have hUVnorm : N ≤ normalizer ((⁅V₀,T⁆ : Subgroup G) : Set G) :=
    (hNC.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  have hcomm : ⁅N,T⁆ = ⁅V₀,T⁆ := by
    apply le_antisymm ?_ (commutator_mono hVN le_rfl)
    change ⁅N,T⁆ ≤ ⁅V₀,T⁆
    rw [hNV]
    exact commutator_sup_le_of_relative_normal N V₀ D T ⁅V₀,T⁆ hUVnorm hVN hDN le_rfl
      ((commutator_eq_bot_iff_le_centralizer.mpr
        (show D ≤ centralizer (T : Set G) from inf_le_right)).le.trans bot_le)
  have hVV : IsMulCommutative V₀ := by
    refine ⟨⟨fun z w => ?_⟩⟩
    apply Subtype.ext
    exact (hNC (hVN z.property) w w.property).symm
  let := hVV
  have hcopV : Nat.Coprime (Nat.card T) (Nat.card V₀) :=
    hcop.of_dvd_right (card_dvd_of_le hVN)
  let : Normalizes T V₀ := ⟨hTV⟩
  have hd := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V₀) (A := T) (Group.isSolvable_of_comm fun z w => mul_comm z w) hcopV inferInstance
  have hdis := Subgroup.disjoint_map V₀.subtype_injective hd.symm.disjoint
  rw [commutatorAction_subgroup_conj_map_eq_commutator V₀ T hTV,
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn V₀ T hTV,
    map_subgroupOf_eq_of_le (show subgroupCentralizerIn V₀ T ≤ V₀ from inf_le_left)] at hdis
  refine ⟨hNV,hcomm,by simpa only [hcomm] using hdecomp,?_,?_⟩
  · apply disjoint_def.mpr
    intro z hz hzD
    exact disjoint_def.mp hdis hz ⟨hUV hz,hzD.2⟩
  · rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      ((hDN.trans hNC).trans (centralizer_le hUV))

/-- The odd-centralizer bound holds on the entire original vertex orbit.
This is the reorientation needed when §9.10 applies (1b) at alpha-minus-one. -/
theorem odd_core_centralizer_radius_transport
    (h : LocallyRankOneTriple P B) {beta : Vertex (family P)}
    (hfixed : ∀ D : Subgroup G, D ≤ graphLocalGroup (family P) beta →
      Odd (Nat.card D) → D ≠ ⊥ →
      Q (family P) beta ⊓ centralizer (D : Set G) ≤ ballKernel (family P) beta 2) :
    ∀ v : Vertex (family P), beta.type = v.type →
      ∀ D : Subgroup G, D ≤ graphLocalGroup (family P) v →
        Odd (Nat.card D) → D ≠ ⊥ →
        Q (family P) v ⊓ centralizer (D : Set G) ≤ ballKernel (family P) v 2 := by
  intro v hv D hDH ho hne
  let Γ := family P
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ v beta).mpr hv.symm
  let f := (MulAut.conj g).toMonoidHom
  let T := D.map f
  have hTH : T ≤ graphLocalGroup Γ beta := by
    have hh := map_mono (f := f) hDH
    rw [←graphLocalGroup_conjugate h g v,hg] at hh
    exact hh
  have hTo : Odd (Nat.card T) := by
    rwa [card_map_of_injective (MulAut.conj g).injective]
  have hTne : T ≠ ⊥ := by
    intro he
    apply hne
    apply Subgroup.map_injective (f := f) (MulAut.conj g).injective
    rw [Subgroup.map_bot]
    exact he
  intro z hz
  have hzQ : g*z*g⁻¹ ∈ Q Γ beta := by
    rw [←hg,Q_translate]
    exact mem_map_of_mem f hz.1
  have hzC : g*z*g⁻¹ ∈ centralizer (T : Set G) :=
    map_centralizer_le_centralizer_image (D : Set G) f (mem_map_of_mem f hz.2)
  have hzK := hfixed T hTH hTo hTne ⟨hzQ,hzC⟩
  rw [←hg] at hzK
  exact (conj_mem_ballKernel_iff Γ g z v 2).mp hzK


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
