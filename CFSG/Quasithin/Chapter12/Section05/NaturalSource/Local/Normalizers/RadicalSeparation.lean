module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Projection

/-!
# Separating the point radical from the two local normalizers

In the nonquasisimple point row, X = Ξ₇(K₁) is a genuine member of Ξ(G,T)
with elementary quotient of order 49. If Lᵢ normalized X for i = 3,6,
L₁ ∨ Lᵢ = L and maximal two-local uniqueness over LT would force K₁
inside N_G(L), contradicting strict radical enlargement.

If X lay in Gᵢ, the normal-or-component-orbit theorem 1.3.4 would therefore
detect a quasisimple component orbit containing X. Its seven-rank is at
least two. The normal original Lᵢ has seven-rank one, so the SQTK rank
bound identifies that orbit with Lᵢ and gives a contradiction. Thus X is
not contained in either local normalizer. Irreducibility under the whole
original T now gives X ∩ Gᵢ = O₂(X), including the entire two-core kernel.

The final application uses the actual G₁/O₂(G₁) projection and proves that
X* is disjoint from (Gᵢ ∩ G₁)*. The kernel lies in T and is retained in the
intersection calculation. This is the radical separation step in 12.5.4;
normalization of the original L₁* from this separation still requires the
complement action argument. That step, the J₄ normalizer case and final
local assembly remain with qt-d-1251-local. Earlier structural source
discharge is qt-d-1222-source; exterior assembly is qt-d-1251-source.
No generation-one exclusion is used here.

Source: Aschbacher--Smith, 12.5.3--4, pp.818--819, using 1.3.3--4,
pp.509--510, and the genuine SQTK seven-rank bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

omit [Finite G] in
/-- Relative normality of K₁ gives the actual G₁ action on its radical. -/
theorem point_radical_normalized {K : Subgroup G}
    (hKG : K ≤ s.marking.Gi 1) (hn : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    s.marking.Gi 1 ≤ normalizer (Chapter1.XiP 7 K : Set G) :=
  Chapter1.XiP_invariant 7 ((normal_subgroupOf_iff_le_normalizer hKG).mp hn)

/-- The radical is nontrivial in the nonquasisimple point row. -/
theorem point_radical_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    Chapter1.XiP 7 K ≠ ⊥ := by
  intro he
  have hk := s.local_component_nonquasisimple_product h 1 (.inl rfl) hK hLK hn
  rw [he,bot_sup_eq] at hk
  subst K
  exact hn (s.marking.Li_core_quasisimple 1 (.inl rfl))

/-- Ambient even characteristic gives a nontrivial intrinsic two-core of the radical. -/
theorem point_radical_core_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    (Chapter1.XiP 7 K).pCoreIn 2 ≠ ⊥ := by
  let X := Chapter1.XiP 7 K
  have hX : X ≠ ⊥ := s.point_radical_ne_bot h hK hLK hn
  have hXG : X ≤ s.marking.Gi 1 := (Chapter1.XiP_le 7 K).trans hK.1
  have hXN : (X.subgroupOf (s.marking.Gi 1)).Normal :=
    normal_subgroupOf_of_le_normalizer (s.point_radical_normalized hK.1 hN)
  have hHe := Chapter1.lemma_1_1_3_1
    (Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
      (s.marking.Gi_twoLocal 1 (.inl rfl))
      (s.sylow_le_Gi 1 (.inl rfl))) hX hXG hXN.isSubnormal
  change X ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ X.pCoreIn 2 at hHe
  intro he
  change X.pCoreIn 2 = ⊥ at he
  apply hX
  apply bot_unique
  intro x hx
  apply he ▸ hHe
  refine ⟨hx,?_⟩
  intro y hy
  have hy1 : y = 1 := hy
  simp [hy1]

/-- The point radical has genuine Ξ-family membership and its odd quotient. -/
theorem point_radical_mem_Xi
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    Chapter1.XiP 7 K ∈ Chapter1.Xi G (T : Subgroup G) ∧
      Chapter1.XiOddQuotient 7 (Chapter1.XiQuotient (Chapter1.XiP 7 K)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hT := s.sylow_le_Gi 1 (.inl rfl)
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent
      (Chapter1.mem_H_of_isTwoLocal (s.marking.Gi_twoLocal 1 (.inl rfl)))
      ⟨T.subtype hT,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT]⟩ hK.1 hK.2
  let J := K ⊔ (T : Subgroup G)
  have hJG : J ≤ s.marking.Gi 1 := sup_le hK.1 hT
  have hJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJG)).mp
      ((h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl))).subgroup
        (J.subgroupOf (s.marking.Gi 1)))
  have hQ := ChapterE.Structure.sqtk_two_quotient hJ (pCore 2 J) pCore_isPGroup
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hT.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hN)
  obtain ⟨hm,_⟩ := s.local_component_nonquasisimple_seven_core h 1 (.inl rfl) hK hLK hn
  have hc : Nat.card (pCore 7 (K ⧸ pCore 2 K)) = 49 := by
    rw [Nat.card_congr hm.some.toEquiv]
    simp
  have hd : 7 ∣ Nat.card (fittingSubgroup (K ⧸ pCore 2 K)) :=
    dvd_trans (by rw [hc]; decide)
      (card_dvd_of_le (pCore_le_fitting (K ⧸ pCore 2 K) 7))
  have hq := (Chapter1.XiP_oddQuotient_of_A36 hA36 hlocal hQ hn (by decide : Odd 7) hd).2
  refine ⟨⟨Chapter1.XiP_isPPerfect 7 K,Chapter1.XiP_invariant 7 hTK,
    Chapter1.XiP_join_mem_H 7 hlocal,⟨7,by decide,by decide,hq⟩,?_⟩,hq⟩
  exact Chapter1.RadicalActions.XiP_irreducible_of_A36 hA36 hlocal hQ hn hTK (by decide) hd

/-- The noncyclic seven-quotient gives rank at least two before quotienting. -/
theorem point_radical_seven_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    2 ≤ primeRank 7 (Chapter1.XiP 7 K) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨hx,hq⟩ := s.point_radical_mem_Xi h hK hLK hN hn
  let P : Sylow 7 (Chapter1.XiP 7 K) := Classical.choice inferInstance
  by_contra hr
  have hc := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)
  exact hq.not_isCyclic ((hx.sylowQuotientEquiv (by decide) hq P).isCyclic.mp hc)


/-- Uniqueness over LT forbids the other local residual from normalizing the point radical. -/
theorem point_radical_not_normalized_by_local_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    ¬ s.marking.Li i ≤ normalizer (Chapter1.XiP 7 K : Set G) := by
  intro hni
  let X := Chapter1.XiP 7 K
  have h1 := s.point_radical_normalized hK.1 hN
  have hL : L ≤ normalizer (X : Set G) := by
    rw [←s.point_residual_sup_local_eq h i hi]
    exact sup_le ((s.marking.Li_le_Gi 1).trans h1) hni
  have hT : (T : Subgroup G) ≤ normalizer (X : Set G) := s.sylow_le_G₁.trans h1
  have hc : normalizer (X : Set G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  have hu := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hM : normalizer (X.pCoreIn 2 : Set G) ≤ s.marking.M :=
    normalizer_le_of_unique_maximalTwoLocal hu.2 (isPGroup_pCoreIn 2 X)
      (s.point_radical_core_ne_bot h hK hLK hN hn) ((sup_le hL hT).trans hc)
  have he := s.local_component_eq_of_le_M 1 (.inl rfl) hK hLK
    (hK.1.trans (h1.trans (hc.trans hM)))
  subst K
  exact hn (s.marking.Li_core_quasisimple 1 (.inl rfl))

/-- A hypothetical placement of the point radical gives an actual component orbit. -/
theorem point_radical_local_component_orbit
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (i : ℕ) (hi : i = 3 ∨ i = 6) (hXi : Chapter1.XiP 7 K ≤ s.marking.Gi i) :
    ∃ Q : Subgroup G, Q ∈ Chapter1.cComponentsIn (s.marking.Gi i) ∧
      IsQuasisimple (Q ⧸ pCore 2 Q) ∧
      Chapter1.XiP 7 K ≤ componentOrbit Q (T : Subgroup G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 K
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  obtain ⟨hX,hq⟩ := s.point_radical_mem_Xi h hK hLK hN hn
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) (s.marking.Gi i) :=
    ⟨T.subtype (s.sylow_le_Gi i hidx),by simp only [Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (s.sylow_le_Gi i hidx)]⟩
  let P : Sylow 7 X := Classical.choice inferInstance
  have d := Chapter1.XiEmbedding.localInput_of_mem_Xi hX hT
    (sup_le hXi (s.sylow_le_Gi i hidx)) (by decide : Odd 7) hq P
  rcases d.normal_or_detected_containment
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal i hidx)) hT with
    hx | ⟨Q,hQ,_,_,_,hXQ⟩
  · exact (s.point_radical_not_normalized_by_local_residual h hK hLK hN hn i hi
      ((s.marking.Li_le_Gi i).trans ((normal_subgroupOf_iff_le_normalizer hXi).mp hx))).elim
  · exact ⟨Q,hQ.mem,hQ.quasisimple,hXQ⟩

private theorem local_residual_seven_rank (i : ℕ) (hi : i = 3 ∨ i = 6) :
    primeRank 7 (s.marking.Li i) = 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  rw [←primeRank_quotient_eq_of_isTwoGroup 7 (by decide) (pCore 2 (s.marking.Li i)) pCore_isPGroup]
  have hc : Nat.card (s.marking.Li i ⧸ pCore 2 (s.marking.Li i)) = 168 ∨
      Nat.card (s.marking.Li i ⧸ pCore 2 (s.marking.Li i)) = 20160 := by
    rw [Nat.card_congr (s.marking.LiCoreEquiv i hidx).toEquiv]
    rcases hi with rfl | rfl
    · exact .inl Atlas.Comparisons.Exceptional.sl3Two_card
    · exact .inr Atlas.Order20160A8.sl4Two_card
  have hb : primeRank 7 (s.marking.Li i ⧸ pCore 2 (s.marking.Li i)) ≤ 1 := by
    apply primeRank_le_of_prime_pow_not_dvd
    rcases hc with hc | hc <;> rw [hc] <;> decide
  have hp : primeRank 7 (s.marking.Li i ⧸ pCore 2 (s.marking.Li i)) ≠ 0 := by
    intro hz
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    apply hh
    rcases hc with hc | hc <;> rw [hc] <;> decide
  omega

private theorem local_residual_core_simple (i : ℕ) (hi : i = 3 ∨ i = 6) :
    IsSimpleGroup (s.marking.Li i ⧸ pCore 2 (s.marking.Li i)) := by
  rcases hi with rfl | rfl
  · let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
    let e : (s.marking.Li 3 ⧸ pCore 2 (s.marking.Li 3)) ≃* SL(3,ZMod 2) :=
      s.marking.LiCoreEquiv 3 (.inr (.inl rfl))
    exact e.isSimpleGroup
  · let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((s.marking.LiCoreEquiv 6 (.inr (.inr (.inr rfl)))).trans
      (Atlas.Order20160A8.sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)).isSimpleGroup

/-- The point radical cannot lie in either of the two other local normalizers.
An orbit detected by source 1.3.4 would have seven-rank two, whereas the
normal original local residual has seven-rank one. -/
theorem point_radical_not_le_local_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (i : ℕ) (hi : i = 3 ∨ i = 6) : ¬ Chapter1.XiP 7 K ≤ s.marking.Gi i := by
  intro hXi
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  let C := s.marking.Li i
  have hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi i) := by
    rcases hi with rfl | rfl
    · exact (s.local_three_component_from_source h).1
    · exact (s.local_six_component_source h).1
  have hNC : (C.subgroupOf (s.marking.Gi i)).Normal := by
    rcases hi with rfl | rfl
    · exact (s.local_three_component_from_source h).2
    · exact (s.local_six_component_source h).2
  have hLC : s.marking.Li i ≤ C := le_rfl
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨Q,hQ,hqQ,hXQ⟩ := s.point_radical_local_component_orbit h hK hLK hN hn i hi hXi
  let H := s.marking.Gi i
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (s.marking.Li i).subgroupOf H
  let C₀ := C.subgroupOf H
  let Q₀ := Q.subgroupOf H
  let X := Chapter1.XiP 7 K
  let X₀ := X.subgroupOf H
  have hXH : X ≤ H := hXi
  let a : Q₀ ≃* Q := subgroupOfEquivOfLe hQ.1
  let e : (Q ⧸ pCore 2 Q) ≃* Q₀.map q :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hQ.2)
  let := hqQ
  let : IsQuasisimple (Q₀.map q) := IsQuasisimple.of_mulEquiv e
  have hQo : IsComponent (H ⧸ pCore 2 H) (Q₀.map q) :=
    ⟨(hQ.2.map_quotient _).subnormal,inferInstance⟩
  let : C₀.Normal := hNC
  let : (C₀.map q).Normal := Normal.map hNC q (QuotientGroup.mk'_surjective _)
  let b : B ≃* s.marking.Li i := subgroupOfEquivOfLe (s.marking.Li_le_Gi i)
  let : Group.IsPerfect (s.marking.Li i) := s.marking.Li_perfect i
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  let : IsSimpleGroup (s.marking.Li i ⧸ pCore 2 (s.marking.Li i)) := s.local_residual_core_simple i hi
  let : IsSimpleGroup (B ⧸ pCore 2 B) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).isSimpleGroup
  let f := q.subgroupMap B
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsPerfect (B.map q) := Group.IsPerfect.ofSurjective (f := f) (q.subgroupMap_surjective B)
  let eb := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f (q.subgroupMap_surjective B)
  let : IsSimpleGroup ((B.map q) ⧸ pCore 2 (B.map q)) := eb.symm.isSimpleGroup
  have hzle : center (B.map q) ≤ pCore 2 (B.map q) := by
    rw [←PerfectCoreTwoExtension.radical_eq_core (G := B.map q)]
    exact le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm fun x y => Subtype.ext (mem_center_iff.mp x.property y).symm)
  have hz : Nat.Coprime 7 (Nat.card (center (B.map q))) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup.to_le hzle).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 7 2).pow_right n
  have hqker : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hrB : 1 ≤ primeRank 7 (B.map q) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hqker,
      primeRank_congr 7 b,s.local_residual_seven_rank i hi]
  have hrX : 2 ≤ primeRank 7 (X₀.map q) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hqker,
      primeRank_congr 7 (subgroupOfEquivOfLe hXH)]
    exact s.point_radical_seven_rank h hK hLK hN hn
  have hXorb : X₀.map q ≤ componentOrbit (Q₀.map q) (((T : Subgroup G).subgroupOf H).map q) := by
    have hh := map_mono (f := q) (comap_mono (f := H.subtype) hXQ)
    exact hh.trans_eq (Chapter1.XiEmbedding.quotientImage_componentOrbit_source
      H Q (T : Subgroup G) hQ.1 (s.sylow_le_Gi i hidx))
  have hrH : primeRank 7 (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 7 (by decide) _ pCore_isPGroup).trans
      ((h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal i hidx)).stronglyQuasithin
        7 (by decide) (by decide))
  have he : Q₀.map q = C₀.map q := hQo.eq_normal_cComponent_of_orbit_rank
    (B := B.map q) (hC.2.map_quotient _) (map_mono (comap_mono hLC)) hXorb hz (by omega)
  have he₀ : Q₀ = C₀ := hQ.2.eq_of_map_quotient_eq hC.2 _ he
  have heQ : Q = C := by
    have hh := congrArg (map H.subtype) he₀
    exact (map_subgroupOf_eq_of_le hQ.1).symm.trans
      (hh.trans (map_subgroupOf_eq_of_le hC.1))
  subst Q
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (s.sylow_le_Gi i hidx).trans ((normal_subgroupOf_iff_le_normalizer hC.1).mp hNC)
  have hXC : X ≤ C := hXQ.trans (iSup_conjugates_le_of_le_normalizer C (T : Subgroup G) C le_rfl hTC)
  have hr := (s.point_radical_seven_rank h hK hLK hN hn).trans (primeRank_mono 7 hXC)
  change 2 ≤ primeRank 7 (s.marking.Li i) at hr
  rw [s.local_residual_seven_rank i hi] at hr
  omega

private theorem xi_intersection_le_core_or_le {X H : Subgroup G}
    (hX : Chapter1.XiMember (T : Subgroup G) X) (hTH : (T : Subgroup G) ≤ H)
    [IsElementaryAbelian 7 (Chapter1.XiQuotient X)] :
    X ⊓ H ≤ X.pCoreIn 2 ∨ X ≤ H := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (IsPGroup 7 (Chapter1.XiQuotient X)) :=
    ⟨IsElementaryAbelian.isPGroup 7 _⟩
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := QuotientGroup.mk' (frattini (Chapter1.XiQuotient X))
  let f := r.comp q
  let B := H.subgroupOf X
  let _ := conjMulDistribMulActionOfLeNormalizer (T : Subgroup G) X hX.invariant
  have hf (t : T) (x : X) :
      Chapter1.xiFrattiniAction (T : Subgroup G) X hX.invariant t (f x) = f (t • x) := by
    simp only [Chapter1.xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk,f,q,r]
    rfl
  have hi : ∀ t : T, ∀ a ∈ B.map f,
      Chapter1.xiFrattiniAction (T : Subgroup G) X hX.invariant t a ∈ B.map f := by
    rintro t a ⟨x,hx,rfl⟩
    rw [hf]
    apply mem_map_of_mem
    exact H.mul_mem (H.mul_mem (hTH t.property) hx) (H.inv_mem (hTH t.property))
  rcases hX.irreducible (B.map f) hi with hb | ht
  · left
    intro x hx
    have hz : f ⟨x,hx.1⟩ = 1 := mem_bot.mp (hb ▸ mem_map_of_mem f hx.2)
    have hq : q ⟨x,hx.1⟩ ∈ frattini (Chapter1.XiQuotient X) :=
      (QuotientGroup.eq_one_iff _).mp hz
    rw [frattini_eq_bot_of_isElementaryAbelian (R := Chapter1.XiQuotient X) (p := 7)] at hq
    exact mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff _).mp (mem_bot.mp hq))
  · right
    have hq : B.map q = ⊤ := by
      apply frattini_nongenerating
      have hh := congrArg (comap r) ht
      change (B.map (r.comp q)).comap r = (⊤ : Subgroup _).comap r at hh
      rw [←map_map] at hh
      simpa only [comap_map_eq,r,QuotientGroup.ker_mk',comap_top] using hh
    have hcore : X.pCoreIn 2 ≤ (T : Subgroup G) :=
      hX.pCoreIn_le_of_isSylowIn
        ⟨T.subtype le_sup_right,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]⟩
    have hker : q.ker ≤ B := by
      rw [QuotientGroup.ker_mk']
      intro x hx
      exact hTH (hcore (mem_map_of_mem X.subtype hx))
    have hbtop : B = ⊤ := by
      have hh := congrArg (comap q) hq
      simpa only [comap_map_eq,sup_eq_left.mpr hker,comap_top] using hh
    intro x hx
    exact (show (⟨x,hx⟩ : X) ∈ B from hbtop.symm ▸ mem_top _)

/-- The actual point radical has elementary quotient of order 49, so no
extra Frattini kernel is introduced when its Sylow irreducibility is used. -/
theorem point_radical_quotient_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    IsElementaryAbelian 7 (Chapter1.XiQuotient (Chapter1.XiP 7 K)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨hm,_⟩ := s.local_component_nonquasisimple_seven_core h 1 (.inl rfl) hK hLK hn
  let N := pCore 7 (K ⧸ pCore 2 K)
  let v := hm.some
  let : IsElementaryAbelian 7 N := {
    toIsMulCommutative := IsMulCommutative.of_comm (fun x y =>
      v.injective (by simp only [map_mul,mul_comm]))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply v.injective
      rw [map_pow,map_one]
      apply congrArg Multiplicative.ofAdd
      funext j
      change (7 : ℕ) • (v x).toAdd j = 0
      have hz : Nat.card (ZMod 7) • (v x).toAdd j = 0 := card_nsmul_eq_zero'
      simpa only [Nat.card_zmod] using hz) }
  let e := Chapter1.xiPQuotientEquivOmega (by decide : Odd 7) K
  exact IsElementaryAbelian.of_injective
    ((omega N (p := 7) 1).subtype.comp e.toMonoidHom)
    ((omega N (p := 7) 1).subtype_injective.comp e.injective)

/-- In both original local normalizers, the intersection with the point
radical is contained in its two-core. The full original Sylow supplies
irreducibility and contains the entire kernel. -/
theorem point_radical_inf_local_le_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    Chapter1.XiP 7 K ⊓ s.marking.Gi i ≤ (Chapter1.XiP 7 K).pCoreIn 2 := by
  let := s.point_radical_quotient_elementary h hK hLK hn
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  exact (xi_intersection_le_core_or_le (s.point_radical_mem_Xi h hK hLK hN hn).1
    (s.sylow_le_Gi i hidx)).resolve_right
      (s.point_radical_not_le_local_normalizer h hK hLK hN hn i hi)

/-- The intersection is exactly the whole two-core, which is already in
T; thus this equality loses none of the source kernel. -/
theorem point_radical_inf_local_eq_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    Chapter1.XiP 7 K ⊓ s.marking.Gi i = (Chapter1.XiP 7 K).pCoreIn 2 := by
  apply le_antisymm (s.point_radical_inf_local_le_core h hK hLK hN hn i hi)
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have hc : (Chapter1.XiP 7 K).pCoreIn 2 ≤ (T : Subgroup G) :=
    (s.point_radical_mem_Xi h hK hLK hN hn).1.pCoreIn_le_of_isSylowIn
      ⟨T.subtype le_sup_right,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]⟩
  exact le_inf (pCoreIn_le 2 _) (hc.trans (s.sylow_le_Gi i hidx))

/-- The literal local intersection has trivial intersection with the point
radical after quotienting by O₂(G₁). This is the radical separation input
to normalizer control, with the original quotient map retained. -/
theorem point_radical_image_disjoint_local_intersection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    Disjoint (s.pointCoreImage (Chapter1.XiP 7 K))
      (s.pointCoreImage (s.marking.Gi i ⊓ s.marking.Gi 1)) := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  let X := Chapter1.XiP 7 K
  have hXH : X ≤ H := (Chapter1.XiP_le 7 K).trans hK.1
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have hcoreT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,H,map_subgroupOf_eq_of_le s.sylow_le_G₁] using
      pCoreIn_le_sylow H (T.subtype s.sylow_le_G₁)
  have hk : q.ker ≤ (s.marking.Gi i ⊓ H).subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact ⟨s.sylow_le_Gi i hidx (hcoreT (mem_map_of_mem H.subtype hx)),x.property⟩
  have hxc : X.pCoreIn 2 ≤ H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hXH (s.point_radical_normalized hK.1 hN)
  apply disjoint_iff.mpr
  change (X.subgroupOf H).map q ⊓ ((s.marking.Gi i ⊓ H).subgroupOf H).map q = ⊥
  rw [←map_inf_of_ker_le q (X.subgroupOf H) ((s.marking.Gi i ⊓ H).subgroupOf H) hk]
  rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  intro x hx
  have hxc' := hxc (s.point_radical_inf_local_le_core h hK hLK hN hn i hi
    (show (x : G) ∈ X ⊓ s.marking.Gi i from ⟨hx.1,hx.2.1⟩))
  obtain ⟨y,hy,he⟩ := hxc'
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
