module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreLayer
public import Theory.SpecificGroups.SL3.ParabolicFixer
public import Theory.ElementaryAbelian.Join
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSDoubledCrossing

/-!
# The crossed natural center inside the original nonblock core

The full module identity survives the original crossing, so Uᵗ fixes the
L-image in K/O₂(K). Pointwise rigidity of the marked line-parabolic residual
kills its full SL₃ action. The exact elementary-action kernel then puts Uᵗ
inside Q, including over field four. The original center-normalizer identity
excludes Uᵗ≤U, and UUᵗ is an elementary subgroup of E∩Q properly containing U.

The quadratic orbit bound [O₂(N_G(Z_S)),E]≤Z_S and the small-central-quotient
calculation force Q outside O₂(N_G(Z_S)). Applied to the selected original
normal component, this gives U<E∩Q≤O₂(K_Z)∩Q<Q, retaining both component
embeddings. The final consumer constructs this component from the exact
whole-core alternatives and the already checked doubled-row exclusion.

These intersection bounds do not assert K₂<O₂(K_Z)K₂. Strict secondary-core
enlargement and the final nonblock contradiction remain with this source
owner. Full quotient recognition and whole-core classification retain
qt-c134-nonbinary-linear-three-source and their final discharge obligation.
Source: Aschbacher--Smith, original 4.3.9--14, printed pp.616--618;
C.1.34(3), pp.136--137, and the parabolic rigidity used in 4.3.7.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private theorem center_le_sylow : U c ≤ S c := (map_subtype_le _).trans (core_le_sylow c)

private theorem crossed_center_le_sylow :
    (U c).map (MulAut.conj c.t⁻¹).toMonoidHom ≤ S c := by
  have hs := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (S c : Set G)).inv_mem c.crossing_normalizes)
  exact (map_mono center_le_sylow).trans_eq hs

omit [Finite G] in
/-- Crossing preserves the full original commutator module on the natural center. -/
theorem MSData.crossed_center_fullModule (d : MSData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ⁅(U c).map (MulAut.conj c.t⁻¹).toMonoidHom,L⁆ = W c := by
  have htL : L.map (MulAut.conj c.t⁻¹).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp
    (D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem))
  have hh := congrArg (map (MulAut.conj c.t⁻¹).toMonoidHom) d.fullModule
  rw [map_commutator,htL,c.crossing_fullModule D] at hh
  exact hh

/-- The actual crossed natural center lies in Q, by its literal full quotient action. -/
theorem MSData.crossed_center_le_core (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier) :
    (U c).map (MulAut.conj c.t⁻¹).toMonoidHom ≤ Q c := by
  let A := (U c).map (MulAut.conj c.t⁻¹).toMonoidHom
  have hAJ : A ≤ K c ⊔ S c := crossed_center_le_sylow.trans le_sup_right
  have hU : IsElementaryAbelian 2 (U c) := by
    obtain ⟨B,C,hB,_,_,_,_,_,hi,_⟩ := d.exists_elementary_core_decomposition
    let := hB
    exact IsElementaryAbelian.of_injective (inclusion (hi.ge.trans inf_le_left))
      (inclusion_injective _)
  let := hU
  let : IsElementaryAbelian 2 A := hU.map _
  have hWU : W c ≤ U c := by
    rw [←d.fullModule]
    exact le_normalizer_iff_commutator_le_left.mp (c.le_component.trans d.natural.2.1)
  have hlocal : ⁅A,L⁆ ≤ Q c :=
    (d.crossed_center_fullModule D).le.trans (hWU.trans (map_subtype_le _))
  intro a ha
  let aJ : (K c ⊔ S c : Subgroup G) := ⟨a,hAJ ha⟩
  have hfix : joinLinearThreeAction d aJ = 1 := by
    apply lineLocalSL_fixer_eq_one (by omega : 0<n)
      (d.field.card_eq.trans (congrArg (2^·) d.degree_eq))
    intro x hx
    obtain ⟨l,hl,rfl⟩ := hL.ge hx
    let l' : K c := (K c).normalizerMonoidHom
      (inclusion (sup_le (K c).le_normalizer
        (inf_le_right.trans c.normalizer_component.le)) aJ) l
    have hact : joinLinearThreeAction d aJ (linearThreeActor d.model l) =
        linearThreeActor d.model l' := by
      change d.model (pCoreJoinAction 2 _ aJ
        (d.model.symm (d.model (QuotientGroup.mk' _ l)))) = _
      rw [d.model.symm_apply_apply,pCoreJoinAction_mk]
      rfl
    rw [hact]
    apply congrArg d.model
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hz : ((l' / l : K c) : G) ∈ Q c := by
      change a * (l : G) * a⁻¹ / (l : G) ∈ Q c
      simpa only [div_eq_mul_inv,commutatorElement_def,Subgroup.subtype_apply] using
        hlocal (commutator_mem_commutator ha hl)
    have hQ : Q c ≤ (K c).pCoreIn 2 :=
      le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))
    exact (mem_map_iff_mem (K c).subtype_injective).mp (hQ hz)
  have hk : (⟨a,ha⟩ : A) ∈ ((joinLinearThreeAction d).comp (inclusion hAJ)).ker := hfix
  rw [d.elementary_joinLinearThreeAction_ker A hAJ] at hk
  exact (d.joinCore_eq hn).le hk

/-- The original crossing cannot preserve the natural center, whose normalizer is H. -/
theorem MSData.crossed_center_not_le_center (d : MSData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ¬ (U c).map (MulAut.conj c.t⁻¹).toMonoidHom ≤ U c := by
  intro hh
  have hc : Nat.card ((U c).map (MulAut.conj c.t⁻¹).toMonoidHom) = Nat.card (U c) :=
    card_map_of_injective (MulAut.conj c.t⁻¹).injective
  have he : (U c).map (MulAut.conj c.t⁻¹).toMonoidHom = U c :=
    eq_of_le_of_card_ge hh hc.ge
  have hi : c.t⁻¹ ∈ normalizer (U c : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
  have ht : c.t ∈ normalizer (U c : Set G) := by
    simpa only [inv_inv] using (normalizer (U c : Set G)).inv_mem hi
  rw [RootCoordinates.center_normalizer_eq d D] at ht
  exact c.crossing_outside ⟨c.crossing_mem,ht⟩

/-- The two original centers generate a larger elementary subgroup inside E∩Q. -/
theorem MSData.crossed_center_elementary_growth (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier) :
    let A := U c ⊔ (U c).map (MulAut.conj c.t⁻¹).toMonoidHom
    IsElementaryAbelian 2 A ∧ U c < A ∧ A ≤ rootCoreLayer c ⊓ Q c := by
  let A := (U c).map (MulAut.conj c.t⁻¹).toMonoidHom
  have hAQ := d.crossed_center_le_core hn D hL
  have hU : IsElementaryAbelian 2 (U c) := by
    obtain ⟨B,C,hB,_,_,_,_,_,hi,_⟩ := d.exists_elementary_core_decomposition
    let := hB
    exact IsElementaryAbelian.of_injective (inclusion (hi.ge.trans inf_le_left))
      (inclusion_injective _)
  let := hU
  let : IsElementaryAbelian 2 A := hU.map _
  have hcent : A ≤ Subgroup.centralizer (U c : Set G) := by
    intro a ha u hu
    obtain ⟨u,hu,rfl⟩ := hu
    exact (congrArg Subtype.val (mem_center_iff.mp hu ⟨a,hAQ ha⟩)).symm
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hcent,?_,?_⟩
  · exact lt_of_le_of_ne le_sup_left (fun he => d.crossed_center_not_le_center D
      (le_sup_right.trans he.ge))
  · apply sup_le
    · exact le_inf (RootCoordinates.rootCoreLayer_contains_center d) (map_subtype_le _)
    · exact le_inf (RootCoordinates.crossed_center_le_rootCoreLayer d D c.t⁻¹
        ((T : Subgroup G).inv_mem c.crossing_mem)) hAQ

/-- The original Q acts nontrivially on the crossed center modulo the source root. -/
theorem RootCoordinates.crossed_center_commutator_not_le_root
    {d : MSData c n} (m : RootCoordinates d) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier) :
    ¬ ⁅(U c).map (MulAut.conj c.t⁻¹).toMonoidHom,Q c⁆ ≤ root c := by
  intro hh
  apply d.crossed_center_not_le_center D
  intro a ha
  exact m.core_central_mod_root hn ⟨a,d.crossed_center_le_core hn D hL ha⟩
    (fun q => hh (commutator_mem_commutator ha q.property))

/-- Q cannot be swallowed by the root-normalizer two-core: its action on E is too large. -/
theorem RootCoordinates.core_not_le_rootNormalizer_core
    {d : MSData c n} (m : RootCoordinates d) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier) :
    ¬ Q c ≤ (rootNormalizer c).pCoreIn 2 := by
  intro hQ
  apply m.crossed_center_commutator_not_le_root hn D hL
  rw [commutator_comm]
  exact (commutator_mono hQ (RootCoordinates.crossed_center_le_rootCoreLayer d D c.t⁻¹
    ((T : Subgroup G).inv_mem c.crossing_mem))).trans
      (m.rootCoreLayer_core_commutator hn D)

/-- The selected component has a proper core intersection with Q containing E∩Q>U. -/
theorem MSData.sourceComponent_core_intersection (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    let B := d.sourceComponent hn D h hL hSL
    let P := (B.map (rootNormalizer c).subtype).pCoreIn 2
    U c < rootCoreLayer c ⊓ Q c ∧ rootCoreLayer c ⊓ Q c ≤ P ⊓ Q c ∧
      P ⊓ Q c < Q c := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  let B := d.sourceComponent hn D h hL hSL
  obtain ⟨_,hBn,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  have hE := m.rootCoreLayer_le_component_core hn D h B hBn hsec.le
  have hN : rootNormalizer c ≤ normalizer (B.map (rootNormalizer c).subtype : Set G) := by
    let := hBn
    have hh := B.le_normalizer_map (rootNormalizer c).subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  obtain ⟨_,hUA,hAE⟩ := d.crossed_center_elementary_growth hn D hL
  refine ⟨hUA.trans_le hAE,inf_le_inf_right _ hE,lt_of_le_of_ne inf_le_right ?_⟩
  intro he
  apply m.core_not_le_rootNormalizer_core hn D hL
  exact (he.ge.trans inf_le_left).trans
    (pCoreIn_mono_of_normalizes (map_subtype_le _) hN)

open scoped MatrixGroups
/-- Apply the crossing and intersection bounds to the original whole-core alternatives.
Their quotient recognition and classification remain genuine earlier premises. -/
theorem source_component_intersection_of_alternatives
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e) :
    ∃ B : Subgroup (rootNormalizer c), B.IsCComponent ∧ B.Normal ∧
      IsQuasisimple (B ⧸ pCore 2 B) ∧ secondary c < B.map (rootNormalizer c).subtype ∧
      U c < rootCoreLayer c ⊓ Q c ∧
      rootCoreLayer c ⊓ Q c ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊓ Q c ∧
      (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊓ Q c < Q c := by
  obtain ⟨d,_,hL,hSL⟩ := DoubledMarking.source_msData_of_alternatives D hf hb n hn
    F hdegree e P hP hm
  obtain ⟨hB,hBn,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  exact ⟨d.sourceComponent hn D h hL hSL,hB,hBn,
    d.sourceComponent_quasisimple hn D h hL hSL,hsec,
    d.sourceComponent_core_intersection hn D h hL hSL⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
