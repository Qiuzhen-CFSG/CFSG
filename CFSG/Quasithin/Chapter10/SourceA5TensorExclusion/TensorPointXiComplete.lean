module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Assembly
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointActionImage
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointCentralGeometry
public import Theory.GroupTheory.CComponent.QuasisimpleImageRigidity
public import Theory.GroupTheory.PPerfectHom
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointXiKernel
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointXiCommutator
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointXiGeometry

/-!
# The final Xi contradiction at the original tensor point

If a strict point overcomponent and its diagonal residual have the same
nontrivial action image, two-core rigidity rules out a quasisimple core
quotient. The genuine A.3.6 conclusion then supplies an odd radical factor
Xi_p(I), with p > 3. The diagonal A5 image forces this solvable two-perfect
factor into the action kernel. It centralizes the original plane V1 V_N.

The proved point translation and full Xi fusion make L0 normalize the
factor. The actual factor-swapping element in C_T(v), together with the
degree-two action obstruction, contradicts its commutator generation by
L_N. Every quotient and subgroup is the literal one used by the source.

Source: Aschbacher--Smith 9.4.1, printed pp.735--736, using A.3.6,
1.3.3 and the original Xi fusion argument.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter1 Chapter1.Section02 Chapter3.Section02 ChapterB.InternalThompsonAction
universe u

private theorem a36_knownSimple : A36Input.{u} KnownSimple.IsKnownSimple :=
  ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem fitting_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm (fitting_map_le e)
  have h := map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  simpa [map_map] using h

private theorem fitting_card {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (fittingSubgroup A) = Nat.card (fittingSubgroup B) :=
  Nat.card_congr ((e.subgroupMap _).trans (MulEquiv.subgroupCongr (fitting_map e))).toEquiv

private theorem exists_XiP_of_nonquasisimple
    {G : Type u} [Group G] [Finite G] {I R : Subgroup G}
    (hI : I ∈ Chapter1.L G R)
    (hQ : IsSQTK KnownSimple.IsKnownSimple ((I ⊔ R : Subgroup G) ⧸ pCore 2 (I ⊔ R : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient I))
    (hRI : R ≤ normalizer (I : Set G)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
      p ∣ Nat.card (fittingSubgroup (XiQuotient I)) ∧ XiMember R (XiP p I) := by
  let C := radicalLocalImage R I
  let j := radicalLocalQuotientEquiv hI
  have hC : A36Conclusion C := proposition_1_2_1_four_earlier_conclusion a36_knownSimple hQ hI.1
  have hnC : ¬ IsQuasisimple C := fun hc => hn (IsQuasisimple.of_mulEquiv j.symm)
  have hFit : fittingSubgroup C ≠ ⊥ := by
    intro he
    have hd : ⁅solvableRadical C,solvableRadical C⁆ = ⊥ := by
      rw [hC.2.2.2.2.1,he,commutator_bot_left]
    let : IsQuasisimple (C ⧸ ⁅solvableRadical C,solvableRadical C⁆) := hC.2.2.2.2.2
    exact hnC (IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hd).trans QuotientGroup.quotientBot))
  have hcard : Nat.card (fittingSubgroup C) ≠ 1 := by
    let : Nontrivial (fittingSubgroup C) := (Subgroup.nontrivial_iff_ne_bot _).mpr hFit
    exact (Finite.one_lt_card : 1 < Nat.card (fittingSubgroup C)).ne'
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hcard
  let : Fact p.Prime := ⟨hp⟩
  have hp3 := (RadicalStructure.radical_core (RadicalStructure.nonsimple_radical hC hnC) hd).2.1
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hdI : p ∣ Nat.card (fittingSubgroup (XiQuotient I)) := by
    rwa [fitting_card j]
  refine ⟨p,hp,ho,hp3,hdI,XiP_isPPerfect p I,XiP_invariant p hRI,XiP_join_mem_H p hI,?_,?_⟩
  · exact ⟨p,hp,ho,(XiP_oddQuotient_of_A36 a36_knownSimple hI hQ hn ho hdI).2⟩
  · exact RadicalActions.XiP_irreducible_of_A36 a36_knownSimple hI hQ hn hRI ho hdI

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original point and its literal Sylow centralizer supply the local
C-component and SQTK quotient required by A.3.6. -/
theorem tensorPoint_containing_local_data (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    let R := (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)
    I ∈ Chapter1.L G R ∧
      IsSQTK KnownSimple.IsKnownSimple ((I ⊔ R : Subgroup G) ⧸ pCore 2 (I ⊔ R : Subgroup G)) := by
  let R := (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)
  let H := I ⊔ R
  have hHX : H ≤ centralizer ({(v : G)} : Set G) := sup_le hIX inf_le_right
  have hSyl := (m.tensor_centralizer_sylow v.property hs).restrict
    (show R ≤ H from le_sup_right) hHX
  have hp : IsPGroup 2 (zpowers (v : G)) :=
    T.isPGroup'.to_le (zpowers_le.mpr (m.fullModule_le_sylow v.property))
  have hvH : (v : G) ∈ H :=
    mem_sup_right ⟨m.fullModule_le_sylow v.property,mem_centralizer_singleton_iff.mpr rfl⟩
  have hn : H ≤ normalizer (zpowers (v : G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    exact hHX
  have hvQ : (v : G) ∈ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp (zpowers_le.mpr hvH) hn (mem_zpowers _)
  have hH : H ∈ Chapter1.H G := by
    intro he
    exact m.tensorPoint_ne_one v hv (mem_bot.mp (he ▸ hvQ))
  exact ⟨⟨hI.subgroupOf_of_le le_sup_left hHX,hSyl,hH⟩,
    uniqueness_local_quotient_sqtk D.simpleQTKE hH⟩

/-- The literal diagonal image is nontrivial because its moved subgroup
is fully moved and contains the original nonidentity point. -/
theorem tensorPointResidual_image_ne_bot_of_moved_le (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hBI : m.tensorPointResidual v ≤ I)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (W : Subgroup (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) : Subgroup G))
    [W.Normal]
    (hMoved : ⁅D.fullModule,m.tensorPointResidual v⁆ ≤ W.map
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))).subtype) :
    ((m.tensorPointResidual v).subgroupOf
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W) ≠ ⊥ := by
  let R := (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)
  let H := I ⊔ R
  let B := (m.tensorPointResidual v).subgroupOf H
  have hBH : m.tensorPointResidual v ≤ H := hBI.trans le_sup_left
  intro he
  have hc : m.tensorPointResidual v ≤ centralizer (W.map H.subtype : Set G) := by
    have hc' : B ≤ centralizer (W : Set H) := by
      simpa only [actionMk,QuotientGroup.ker_mk'] using (map_eq_bot_iff B).mp he
    intro b hb w hw
    obtain ⟨a,ha,rfl⟩ := hw
    exact congrArg H.subtype (hc' (show (⟨b,hBH hb⟩ : H) ∈ B from hb) a ha)
  have hzero : ⁅⁅D.fullModule,m.tensorPointResidual v⁆,m.tensorPointResidual v⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hMoved.trans (le_centralizer_iff.mp hc))
  rw [m.tensorPoint_moved_idempotent v] at hzero
  exact m.tensorPoint_ne_one v hv (mem_bot.mp (hzero ▸ m.tensorPoint_mem_moved v hv hs))

/-- Equality of the action images excludes a quasisimple two-core quotient
of a strict overcomponent by actual Sylow-core normalization. -/
theorem tensorPoint_not_quasisimple_quotient_of_image_eq (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hBI : m.tensorPointResidual v < I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (W : Subgroup (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) : Subgroup G))
    [W.Normal]
    (hMoved : ⁅D.fullModule,m.tensorPointResidual v⁆ ≤ W.map
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))).subtype)
    (heq : (I.subgroupOf (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W) =
      ((m.tensorPointResidual v).subgroupOf
        (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W)) :
    ¬ IsQuasisimple (XiQuotient I) := by
  let R := (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)
  let H := I ⊔ R
  let K := I.subgroupOf H
  let B := (m.tensorPointResidual v).subgroupOf H
  have hBH : m.tensorPointResidual v ≤ H := hBI.le.trans le_sup_left
  have hHX : H ≤ centralizer ({(v : G)} : Set G) := sup_le hIX inf_le_right
  have hK : K.IsCComponent := hI.subgroupOf_of_le le_sup_left hHX
  obtain ⟨hlocal,hQ⟩ := m.tensorPoint_containing_local_data v hv hIX hI hs
  obtain ⟨P,hP⟩ := hlocal.2.1
  have hcoreH : I.pCoreIn 2 ≤ H.pCoreIn 2 := by
    have hh := map_mono (f := H.subtype) (pCoreIn_le_of_subnormal 2 hK.subnormal)
    change (K.pCoreIn 2).map H.subtype ≤ H.pCoreIn 2 at hh
    rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le (show I ≤ H from le_sup_left)] at hh
    exact hh
  have hcoreR : I.pCoreIn 2 ≤ R := hcoreH.trans ((pCoreIn_le_sylow H P).trans_eq hP)
  intro hquasi
  let := hquasi
  let j : K ≃* I := subgroupOfEquivOfLe le_sup_left
  let jq := QuotientGroup.congr (pCore 2 K) (pCore 2 I) j (pCore_map_iso 2 j)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv jq.symm
  have hcoreB : pCore 2 K ≤ normalizer (B.subgroupOf K : Set K) := by
    rw [← subgroupOf_normalizer_eq (show B ≤ K from comap_mono hBI.le)]
    intro k hk
    have hg : (k : G) ∈ I.pCoreIn 2 := by
      have hmk := mem_map_of_mem K.subtype hk
      have hmm := mem_map_of_mem H.subtype hmk
      change (k : G) ∈ (K.pCoreIn 2).map H.subtype at hmm
      rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
        map_subgroupOf_eq_of_le (show I ≤ H from le_sup_left)] at hmm
      exact hmm
    show (k : H) ∈ normalizer (B : Set H)
    rw [←subgroupOf_normalizer_eq hBH]
    exact m.tensorPointResidual_sylow_normalized v (hcoreR hg)
  have hEq : B = K := Theory.GroupTheory.IsCComponent.eq_of_image_eq_of_twoCore_normalizes
    (actionMk W) hK
    (comap_mono hBI.le) heq.symm
    (heq ▸ m.tensorPointResidual_image_ne_bot_of_moved_le v hv hBI.le hs W hMoved) hcoreB
  have hh := congrArg (map H.subtype) hEq
  rw [map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le (show I ≤ H from le_sup_left)] at hh
  exact hBI.ne hh

/-- The exact source Xi branch excludes a strict point overcomponent once
its action image equals the literal diagonal image. -/
theorem tensorPoint_Xi_contradiction_of_image_eq (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hBI : m.tensorPointResidual v < I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (W : Subgroup (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) : Subgroup G))
    [W.Normal]
    (hMoved : ⁅D.fullModule,m.tensorPointResidual v⁆ ≤ W.map
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))).subtype)
    (hLine : m.tensorLine ≤ W.map
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))).subtype)
    (heq : (I.subgroupOf (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W) =
      ((m.tensorPointResidual v).subgroupOf
        (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W))
    (t : G) (ht : t ∈ (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
    (htL : t ∉ normalizer (L : Set G)) : False := by
  have hRI : (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) ≤
      normalizer (I : Set G) := inf_le_right.trans hIN
  obtain ⟨hlocal,hQ⟩ := m.tensorPoint_containing_local_data v hv hIX hI hs
  have hn := m.tensorPoint_not_quasisimple_quotient_of_image_eq v hv hBI hIX hI hs W hMoved heq
  have hnonzero := m.tensorPointResidual_image_ne_bot_of_moved_le v hv hBI.le hs W hMoved
  obtain ⟨p,hp,ho,_hp3,hd,hX⟩ := exists_XiP_of_nonquasisimple hlocal hQ hn hRI
  let : Fact p.Prime := ⟨hp⟩
  have hXU := m.tensorPoint_XiP_le_centralizer_of_image_eq v hv hBI.le hIX hI W heq hnonzero ho
  have hXplane := hXU.trans (centralizer_le
    (m.tensorPointXiPlane_le_of_line_and_moved v hv hs hLine hMoved))
  exact m.tensorPoint_Xi_contradiction_of_plane v hv hs hX hXplane (XiP_invariant p hIN)
    t ht htL (m.tensorPoint_XiP_commutator_eq v hv hlocal hQ hn hRI hBI.le ho hd)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
