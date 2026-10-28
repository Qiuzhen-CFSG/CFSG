module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.RadicalEscape
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Generation
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Parabolic
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Assembly
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceSwapped.Detection

/-!
# The three-space radical in the original point centralizer

The full natural action on V₃ kills the solvable characteristic Ξ₇(K₃).
Thus X = Ξ₇(K₃) lies in G₁. Its nontrivial two-core is obtained from
relative normality in G₃ and genuine ambient even characteristic. If L₁
normalized X, the original generation identity L₁ ∨ L₃ = L and maximal
two-local uniqueness over LT would put K₃ inside M, forcing K₃ = L₃.
Consequently X is not normal in G₁.

The A.3.6 radical action constructs X as an actual member of Ξ(G,T).
The proved normal-or-component-orbit part of 1.3.4, with the original full
Sylow in G₁, then supplies its quasisimple containing orbit. The comparison
subgroup is literally O²(C_{K₃}(V₁)); it contains both X and the original
Y = O²(P), lies in G₁ ∩ G₃, and is normalized by T. These statements are
applied to a constructed component whenever L₃ fails relative normality.

The solvable subgroup XT also escapes M. Minimal descent inside it gives
an actual H-star in G₁ ∩ G₃ with generation parameter one. Hence the genuine
generation-one exclusion proves the three-space component and normality
clauses. This is a conditional application: the existing source proof of
that exclusion uses the still-pending ambient normalizer containments.
No LocalComponents construction or unconditional three-space exclusion is
claimed here. The point-component comparison and general normalizer proofs
remain with qt-d-1251-local; final exterior assembly is qt-d-1251-source.

Source: Aschbacher--Smith, 12.5.3, printed pp.818--819, and the escape
argument of 12.5.11(2), printed p.821; 1.3.3--4, pp.509--510.
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

/-- The solvable characteristic radical acts trivially on the full natural three-space. -/
theorem three_radical_centralizes {K : Subgroup G}
    (hKG : K ≤ s.marking.Gi 3) (hLK : s.marking.Li 3 ≤ K) :
    Chapter1.XiP 7 K ≤ centralizer (s.marking.Vi 3 : Set G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 K
  let A := X.subgroupOf K
  let f := (s.marking.Vi 3).normalizerMonoidHom.comp (inclusion hKG)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨l,hl⟩ := s.marking.Li₃Action_surjective a
    exact ⟨inclusion hLK l,hl⟩
  let e : SL(3,ZMod 2) ≃* MulAut (s.marking.Vi 3) :=
    (MulEquiv.ofBijective (Representation.binaryNaturalAut 3)
      (Representation.binaryNaturalAut_bijective 3)).trans
      (MulAut.congr s.marking.V₃Coordinates).symm
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Group.IsPerfect SL(3,ZMod 2) := Atlas.sl_perfect 3 (by decide)
  let : IsSimpleGroup (MulAut (s.marking.Vi 3)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (MulAut (s.marking.Vi 3)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : A.Normal := inferInstance
  let : Group.IsSolvable X := Chapter1.RadicalNormalizers.XiP_solvable 7 (by decide) K
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (Chapter1.XiP_le 7 K)).toMonoidHom)
    (subgroupOfEquivOfLe (Chapter1.XiP_le 7 K)).injective
  let : (A.map f).Normal := Normal.map inferInstance f hf
  let : Group.IsSolvable (A.map f) :=
    Group.isSolvable_of_surjective (f := f.subgroupMap A) (f.subgroupMap_surjective A)
  have he : A.map f = ⊥ := by
    rcases (inferInstance : (A.map f).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · let : Group.IsSolvable (⊤ : Subgroup (MulAut (s.marking.Vi 3))) :=
        he ▸ (inferInstance : Group.IsSolvable (A.map f))
      exact (Group.IsPerfect.not_isSolvable (MulAut (s.marking.Vi 3))
        (Group.isSolvable_of_surjective (f := (topEquiv (G := MulAut (s.marking.Vi 3))).toMonoidHom)
          topEquiv.surjective)).elim
  have hk : A ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp he
  intro x hx
  have hxk := hk (show (⟨x,Chapter1.XiP_le 7 K hx⟩ : K) ∈ A from hx)
  change (s.marking.Vi 3).normalizerMonoidHom
    ⟨x,hKG (Chapter1.XiP_le 7 K hx)⟩ = 1 at hxk
  have hxk' : (⟨x,hKG (Chapter1.XiP_le 7 K hx)⟩ : s.marking.Gi 3) ∈
      (s.marking.Vi 3).normalizerMonoidHom.ker := hxk
  rw [normalizerMonoidHom_ker] at hxk'
  exact hxk'

/-- The original radical is contained in the original point normalizer. -/
theorem three_radical_le_point {K : Subgroup G}
    (hKG : K ≤ s.marking.Gi 3) (hLK : s.marking.Li 3 ≤ K) :
    Chapter1.XiP 7 K ≤ s.marking.Gi 1 :=
  (s.three_radical_centralizes hKG hLK).trans
    ((centralizer_le (s.marking.V₁_le_Vi 3 (.inr (.inl rfl)))).trans
      (Subgroup.centralizer_le_normalizer _))

omit [Finite G] in
/-- Relative normality of K₃ makes its characteristic radical invariant under G₃. -/
theorem three_radical_normalized {K : Subgroup G}
    (hKG : K ≤ s.marking.Gi 3) (hn : (K.subgroupOf (s.marking.Gi 3)).Normal) :
    s.marking.Gi 3 ≤ normalizer (Chapter1.XiP 7 K : Set G) :=
  Chapter1.XiP_invariant 7 ((normal_subgroupOf_iff_le_normalizer hKG).mp hn)

/-- The radical is nontrivial in the nonquasisimple three-space row. -/
theorem three_radical_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    Chapter1.XiP 7 K ≠ ⊥ := by
  intro he
  have hk := s.local_component_nonquasisimple_product h 3 (.inr rfl) hK hLK hn
  rw [he,bot_sup_eq] at hk
  subst K
  exact hn (s.marking.Li_core_quasisimple 3 (.inr (.inl rfl)))

/-- Ambient even characteristic gives a nontrivial intrinsic two-core of the radical. -/
theorem three_radical_core_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    (Chapter1.XiP 7 K).pCoreIn 2 ≠ ⊥ := by
  let X := Chapter1.XiP 7 K
  have hX : X ≠ ⊥ := s.three_radical_ne_bot h hK hLK hn
  have hXG : X ≤ s.marking.Gi 3 := (Chapter1.XiP_le 7 K).trans hK.1
  have hXN : (X.subgroupOf (s.marking.Gi 3)).Normal :=
    normal_subgroupOf_of_le_normalizer (s.three_radical_normalized hK.1 hN)
  have hHe := Chapter1.lemma_1_1_3_1
    (Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
      (s.marking.Gi_twoLocal 3 (.inr (.inl rfl)))
      (s.sylow_le_Gi 3 (.inr (.inl rfl)))) hX hXG hXN.isSubnormal
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

/-- The actual L₁ cannot normalize the strict three-space radical: uniqueness over LT would collapse K₃. -/
theorem three_radical_not_normalized_by_point_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ s.marking.Li 1 ≤ normalizer (Chapter1.XiP 7 K : Set G) := by
  intro h1
  let X := Chapter1.XiP 7 K
  have h3 := s.three_radical_normalized hK.1 hN
  have hL : L ≤ normalizer (X : Set G) := by
    rw [←s.point_residual_sup_local_eq h 3 (.inl rfl)]
    exact sup_le h1 ((s.marking.Li_le_Gi 3).trans h3)
  have hT : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    (s.sylow_le_Gi 3 (.inr (.inl rfl))).trans h3
  have hc : normalizer (X : Set G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  have hu := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hM : normalizer (X.pCoreIn 2 : Set G) ≤ s.marking.M :=
    normalizer_le_of_unique_maximalTwoLocal hu.2 (isPGroup_pCoreIn 2 X)
      (s.three_radical_core_ne_bot h hK hLK hN hn) ((sup_le hL hT).trans hc)
  have he := s.local_component_eq_of_le_M 3 (.inr (.inl rfl)) hK hLK
    (hK.1.trans (h3.trans (hc.trans hM)))
  subst K
  exact hn (s.marking.Li_core_quasisimple 3 (.inr (.inl rfl)))

/-- The normal branch of source 1.3.4 is impossible for the actual radical inside G₁. -/
theorem three_radical_not_normal_in_point
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ ((Chapter1.XiP 7 K).subgroupOf (s.marking.Gi 1)).Normal := by
  intro hx
  exact s.three_radical_not_normalized_by_point_residual h hK hLK hN hn
    ((s.marking.Li_le_Gi 1).trans
      ((normal_subgroupOf_iff_le_normalizer (s.three_radical_le_point hK.1 hLK)).mp hx))

/-- Construct the source Ξ-family membership, including its actual quotient and irreducible Sylow action. -/
theorem three_radical_mem_Xi
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    Chapter1.XiP 7 K ∈ Chapter1.Xi G (T : Subgroup G) ∧
      Chapter1.XiOddQuotient 7 (Chapter1.XiQuotient (Chapter1.XiP 7 K)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hT := s.sylow_le_Gi 3 (.inr (.inl rfl))
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent
      (Chapter1.mem_H_of_isTwoLocal (s.marking.Gi_twoLocal 3 (.inr (.inl rfl))))
      ⟨T.subtype hT,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT]⟩ hK.1 hK.2
  let J := K ⊔ (T : Subgroup G)
  have hJG : J ≤ s.marking.Gi 3 := sup_le hK.1 hT
  have hJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJG)).mp
      ((h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 3 (.inr (.inl rfl)))).subgroup
        (J.subgroupOf (s.marking.Gi 3)))
  have hQ := ChapterE.Structure.sqtk_two_quotient hJ (pCore 2 J) pCore_isPGroup
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hT.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hN)
  obtain ⟨hm,_⟩ := s.local_component_nonquasisimple_seven_core h 3 (.inr rfl) hK hLK hn
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

/-- Apply the proved source detection theorem to the actual radical inside G₁. -/
theorem three_radical_point_component_orbit
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    ∃ Q : Subgroup G, Q ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      IsQuasisimple (Q ⧸ pCore 2 Q) ∧
      Chapter1.XiP 7 K ≤ componentOrbit Q (T : Subgroup G) ∧
      ((componentOrbit Q (T : Subgroup G)).subgroupOf (s.marking.Gi 1)).Normal := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 K
  obtain ⟨hX,hq⟩ := s.three_radical_mem_Xi h hK hLK hN hn
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) (s.marking.Gi 1) :=
    ⟨T.subtype s.sylow_le_G₁,by simp only [Sylow.coe_subtype,
      map_subgroupOf_eq_of_le s.sylow_le_G₁]⟩
  let P : Sylow 7 X := Classical.choice inferInstance
  have d := Chapter1.XiEmbedding.localInput_of_mem_Xi hX hT
    (sup_le (s.three_radical_le_point hK.1 hLK) s.sylow_le_G₁) (by decide : Odd 7) hq P
  rcases d.normal_or_detected_containment
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl))) hT with
    hx | ⟨Q,hQ,hNQ,_,_,hXQ⟩
  · exact (s.three_radical_not_normal_in_point h hK hLK hN hn hx).elim
  · exact ⟨Q,hQ.mem,hQ.quasisimple,hXQ,hNQ⟩

/-- The source K₁,₃ = O²(C_K(V₁)), embedded in the original ambient group. -/
@[expose] def threePointResidual (K : Subgroup G) : Subgroup G :=
  (pResidual 2 (K ⊓ centralizer (s.marking.Vi 1 : Set G) : Subgroup G)).map
    (K ⊓ centralizer (s.marking.Vi 1 : Set G)).subtype

omit [Finite G] in
/-- The literal comparison residual lies in both original local normalizers. -/
theorem threePointResidual_le {K : Subgroup G} (hKG : K ≤ s.marking.Gi 3) :
    s.threePointResidual K ≤ s.marking.Gi 1 ⊓ s.marking.Gi 3 :=
  (map_subtype_le _).trans (le_inf
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)) (inf_le_left.trans hKG))

/-- Two-perfectness places the radical in the actual point-centralizer residual. -/
theorem three_radical_le_threePointResidual {K : Subgroup G}
    (hKG : K ≤ s.marking.Gi 3) (hLK : s.marking.Li 3 ≤ K) :
    Chapter1.XiP 7 K ≤ s.threePointResidual K := by
  let X := Chapter1.XiP 7 K
  let C := K ⊓ centralizer (s.marking.Vi 1 : Set G)
  have hXC : X ≤ C := le_inf (Chapter1.XiP_le 7 K)
    ((s.three_radical_centralizes hKG hLK).trans
      (centralizer_le (s.marking.V₁_le_Vi 3 (.inr (.inl rfl)))))
  have hp : IsPPerfect 2 (X.subgroupOf C) := (Chapter1.XiP_isPPerfect 7 K).of_surjective
    (subgroupOfEquivOfLe hXC).symm.toMonoidHom (subgroupOfEquivOfLe hXC).symm.surjective
  have hh := map_mono (f := C.subtype) (le_pResidual_of_isPPerfect (X.subgroupOf C) hp)
  simpa only [threePointResidual,map_subgroupOf_eq_of_le hXC] using hh

/-- The original first-node residual lies in the same comparison subgroup. -/
theorem Y_le_threePointResidual {K : Subgroup G} (hLK : s.marking.Li 3 ≤ K) :
    s.Y ≤ s.threePointResidual K := by
  let C := K ⊓ centralizer (s.marking.Vi 1 : Set G)
  have hYC : s.Y ≤ C := le_inf ((s.Y_le_local_residual 3 (.inl rfl)).trans hLK) (by
    intro y hy x hx
    have hyP : y ∈ s.P := map_subtype_le _ hy
    have hyG : y ∈ s.marking.Gi 1 :=
      (s.P_le_M₁ hyP).2
    rcases (s.marking.mem_V₁ x).mp hx with rfl | rfl
    · simp
    · rw [s.marking.Gi_one_eq_centralizer] at hyG
      exact (mem_centralizer_singleton_iff.mp hyG).symm)
  have hp : IsPPerfect 2 (s.Y.subgroupOf C) :=
    (isPPerfect_embedded_pResidual 2 s.P).of_surjective
      (subgroupOfEquivOfLe hYC).symm.toMonoidHom (subgroupOfEquivOfLe hYC).symm.surjective
  have hh := map_mono (f := C.subtype) (le_pResidual_of_isPPerfect (s.Y.subgroupOf C) hp)
  simpa only [threePointResidual,map_subgroupOf_eq_of_le hYC] using hh

omit [Finite G] in
/-- The original Sylow normalizes the comparison subgroup. -/
theorem sylow_normalizes_threePointResidual {K : Subgroup G}
    (hKG : K ≤ s.marking.Gi 3) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal) :
    (T : Subgroup G) ≤ normalizer (s.threePointResidual K : Set G) := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (s.sylow_le_Gi 3 (.inr (.inl rfl))).trans
      ((normal_subgroupOf_iff_le_normalizer hKG).mp hN)
  have hTC : (T : Subgroup G) ≤ normalizer (centralizer (s.marking.Vi 1 : Set G) : Set G) :=
    s.sylow_le_G₁.trans (normalizer_le_normalizer_centralizer _)
  exact ((le_inf hTK hTC).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

/-- Failure of relative normality at L₃ constructs the actual radical, comparison residual and point-component orbit. -/
theorem exists_three_radical_point_comparison_of_not_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : ¬ ((s.marking.Li 3).subgroupOf (s.marking.Gi 3)).Normal) :
    ∃ K Q : Subgroup G,
      K ∈ Chapter1.cComponentsIn (s.marking.Gi 3) ∧
      s.marking.Li 3 ≤ K ∧ (K.subgroupOf (s.marking.Gi 3)).Normal ∧
      ¬ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K = Chapter1.XiP 7 K ⊔ s.marking.Li 3 ∧
      Chapter1.XiP 7 K ⊔ s.Y ≤ s.threePointResidual K ∧
      s.threePointResidual K ≤ s.marking.Gi 1 ⊓ s.marking.Gi 3 ∧
      (T : Subgroup G) ≤ normalizer (s.threePointResidual K : Set G) ∧
      Q ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      IsQuasisimple (Q ⧸ pCore 2 Q) ∧
      Chapter1.XiP 7 K ≤ componentOrbit Q (T : Subgroup G) ∧
      ((componentOrbit Q (T : Subgroup G)).subgroupOf (s.marking.Gi 1)).Normal := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 3 (.inr (.inl rfl))
  have hq : ¬ IsQuasisimple (K ⧸ pCore 2 K) := by
    intro hq
    let := hq
    exact hn ((s.local_component_eq_of_quasisimple 3 (.inl rfl) hK hLK).symm ▸ hN)
  obtain ⟨Q,hQ,hqQ,hXQ,hNQ⟩ := s.three_radical_point_component_orbit h hK hLK hN hq
  exact ⟨K,Q,hK,hLK,hN,hq,
    s.local_component_nonquasisimple_product h 3 (.inr rfl) hK hLK hq,
    sup_le (s.three_radical_le_threePointResidual hK.1 hLK) (s.Y_le_threePointResidual hLK),
    s.threePointResidual_le hK.1,s.sylow_normalizes_threePointResidual hK.1 hN,
    hQ,hqQ,hXQ,hNQ⟩

/-- A solvable escaping point overgroup supplies an actual generation-one H-star by finite minimal descent. -/
theorem exists_generation_one_of_solvable_point_overgroup
    {J : Subgroup G} [Group.IsSolvable J]
    (hTJ : (T : Subgroup G) ≤ J) (hJ1 : J ≤ s.marking.Gi 1)
    (hJM : ¬ J ≤ s.marking.M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ J ∧ ChapterE.generationParameter H = 1 := by
  classical
  have hV1T : s.marking.Vi 1 ≤ (T : Subgroup G) :=
    (s.marking.subspace_le _).trans D.le_sylow
  let := D.elementary
  have hcore : s.marking.Vi 1 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le (s.marking.subspace_le _))
    (hV1T.trans hTJ) hJ1
  have hJH : J ∈ Chapter1.HOver G (T : Set G) :=
    ⟨fun he => s.marking.Vi_ne_bot 1 (.inl rfl) (bot_unique (he ▸ hcore)),hTJ⟩
  let P := fun H : Subgroup G => H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ s.marking.M
  obtain ⟨H,hHJ,hH,hmin⟩ := exists_minimal_le_of_wellFoundedLT P J
    (show P J from ⟨hJH,hJM⟩)
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective (inclusion_injective hHJ)
  have heven : ¬ Odd (Nat.card H) := by
    have hdiv := card_dvd_of_le (hV1T.trans hH.1.2)
    rw [s.marking.card_V₁] at hdiv
    exact fun ho => ho.not_two_dvd_nat hdiv
  exact ⟨H,⟨hH,hmin⟩,hHJ,ChapterE.generationParameter_eq_one_of_solvable heven⟩

/-- Strict radical enlargement at the three-space supplies a generation-one escape inside both G₁ and G₃. -/
theorem exists_generation_one_of_three_radical
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ Chapter1.XiP 7 K ⊔ (T : Subgroup G) ∧
      H ≤ s.marking.Gi 1 ⊓ s.marking.Gi 3 ∧ ChapterE.generationParameter H = 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 K
  let J := X ⊔ (T : Subgroup G)
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    (s.sylow_le_Gi 3 (.inr (.inl rfl))).trans (s.three_radical_normalized hK.1 hN)
  let : Group.IsSolvable X := Chapter1.RadicalNormalizers.XiP_solvable 7 (by decide) K
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : (X.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le X.le_normalizer hTX)
  let : Group.IsSolvable (X.subgroupOf J) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show X ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show X ≤ J from le_sup_left)).injective
  let : Group.IsSolvable ((T : Subgroup G).subgroupOf J) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ J from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ J from le_sup_right)).injective
  let : Group.IsSolvable J := Group.isSolvable_of_normal_sup_eq_top
    (X.subgroupOf J) ((T : Subgroup G).subgroupOf J) (by
      rw [←subgroupOf_sup le_sup_left le_sup_right]
      exact subgroupOf_self J)
  have hJ1 : J ≤ s.marking.Gi 1 := sup_le
    (s.three_radical_le_point hK.1 hLK) s.sylow_le_G₁
  have hJ3 : J ≤ s.marking.Gi 3 := sup_le
    ((Chapter1.XiP_le 7 K).trans hK.1) (s.sylow_le_Gi 3 (.inr (.inl rfl)))
  have hJM : ¬ J ≤ s.marking.M := by
    intro hj
    have hKM : K ≤ s.marking.M := by
      rw [s.local_component_nonquasisimple_product h 3 (.inr rfl) hK hLK hn]
      exact sup_le (le_sup_left.trans hj) ((s.marking.Li_le_L 3).trans L.le_normalizer)
    have he := s.local_component_eq_of_le_M 3 (.inr (.inl rfl)) hK hLK hKM
    subst K
    exact hn (s.marking.Li_core_quasisimple 3 (.inr (.inl rfl)))
  obtain ⟨H,hH,hHJ,hgen⟩ := s.exists_generation_one_of_solvable_point_overgroup le_sup_right hJ1 hJM
  exact ⟨H,hH,hHJ,hHJ.trans (le_inf hJ1 hJ3),hgen⟩

/-- The genuine generation-one exclusion settles the three-space component and relative normality clauses. -/
theorem local_three_component_source_of_generation_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hex : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
      ChapterE.generationParameter H ≠ 1) :
    s.marking.Li 3 ∈ Chapter1.cComponentsIn (s.marking.Gi 3) ∧
      ((s.marking.Li 3).subgroupOf (s.marking.Gi 3)).Normal := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 3 (.inr (.inl rfl))
  have hq : IsQuasisimple (K ⧸ pCore 2 K) := by
    by_contra hn
    obtain ⟨H,hH,_,_,hgen⟩ := s.exists_generation_one_of_three_radical h hK hLK hN hn
    exact hex H hH hgen
  let := hq
  exact (s.local_component_eq_of_quasisimple 3 (.inl rfl) hK hLK).symm ▸ ⟨hK,hN⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
