module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearReturn
public import Theory.SpecificGroups.SymmetricSix.NormalGeneration
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.NormalSectionTwoResidual
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.Representation.BinaryPermutation.ProperInvariant

/-!
# The two core commutators in the original mixed linear pair

After the original conjugator returns to L₂T, it stabilizes H₀ and V₀.
The established containments [O₂(LT),V₀] ≤ V and [O₂(H₀),V] ≤ V₀
therefore refer to the original two modules.

Normal generation through the literal LT permutation action shows that
L fixes O₂(LT)/V. Full commutator generation of the chosen V gives
[O₂(LT),L]=V. The invariant-subgroup lattice of the augmentation core
then proves shortness of L and identifies its intrinsic block layer with V,
retaining the nontrivial fixed line. On H₀ the actual simple L₃(2) quotient
forces its two-residual to fix O₂(H₀)/V₀. Full movement of V₀ gives
[O₂(H₀),O²(H₀)]=V₀. The final theorem applies both arguments to the
same original mixed conjugator and discharges both commutator bounds.

Source: Aschbacher--Smith 13.4.15, printed p.912, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- An actor moving the original augmentation core and fixing the rest of
O₂(LT) forces the full component commutator to be exactly that core. -/
theorem original_augmentation_core_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (U : Subgroup G) (hUX : U ≤ L ⊔ (T : Subgroup G))
    (hm : ⁅V,U⁆ ≠ ⊥)
    (hc : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,U⁆ ≤ V) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = V := by
  let X := L ⊔ (T : Subgroup G)
  let Li := L.subgroupOf X
  let Vi := V.subgroupOf X
  let Ui := U.subgroupOf X
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hXV : X ≤ normalizer (V : Set G) := sup_le D.normalizes
    ((structural G T L h).2.2 V D).1
  let : Vi.Normal := normal_subgroupOf_of_le_normalizer hXV
  have hcmp : Li.IsCComponent := h.maximal_faithful.1.1.1
  let : Group.IsPerfect Li := hcmp.perfect
  have hpL : IsPPerfect 2 Li := (pResidual_eq_top_iff 2 Li).mp
    (pResidual_eq_top_of_isPerfect 2)
  obtain ⟨q,hq,_,hLq,hker⟩ := exists_core_product_permutation D m h structural eL
  have hUi : Ui.map q ≠ ⊥ := by
    intro hz
    have hUQ : Ui ≤ pCore 2 X := hker ▸ (map_eq_bot_iff Ui).mp hz
    have hUC : U ≤ centralizer (V : Set G) := by
      intro a ha
      exact D.core_centralizes (mem_map_of_mem X.subtype
        (hUQ (show (⟨a,hUX ha⟩ : X) ∈ Ui from ha)))
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hUC))
  have hgen : Li ≤ normalClosure (Ui : Set X) :=
    Theory.SpecificGroups.SymmetricSix.perfect_le_normalClosure_of_nontrivial_image
      q (hker ▸ pCore_isPGroup) (hLq ▸ map_le_range q Li) Li Ui hpL hLq.le hUi
  have hci : ⁅pCore 2 X,Ui⁆ ≤ Vi := by
    apply commutator_le.mpr
    intro a ha b hb
    exact hc (commutator_mem_commutator (mem_map_of_mem X.subtype ha) hb)
  have hi : ⁅pCore 2 X,Li⁆ ≤ Vi := (commutator_mono le_rfl hgen).trans
    (commutator_normalClosure_le_of_normal (pCore 2 X) Ui Vi hci)
  have hb := map_mono (f := X.subtype) hi
  rw [map_commutator,map_subgroupOf_eq_of_le (show L ≤ X from le_sup_left),
    map_subgroupOf_eq_of_le hVX] at hb
  apply le_antisymm hb
  exact D.eq_commutator.le.trans (commutator_mono D.le_core le_rfl)

omit [Finite G] in
private theorem core_invariant_dichotomy (D : ChosenModule T L V) (m : CoreMarking D)
    (N : Subgroup G) (hNV : N ≤ V) (hLN : L ≤ normalizer (N : Set G)) :
    N ≤ centralizer (L : Set G) ∨ N = V := by
  let S := AddSubgroup.toZModSubmodule 2
    ((N.subgroupOf V).map m.coordinate.toMonoidHom).toAddSubgroup'
  have hmem (v : V) : (m.coordinate v).toAdd ∈ S ↔ v.val ∈ N :=
    mem_map_iff_mem m.coordinate.injective
  have hs : ∀ a : alternatingGroup (Fin 6), ∀ v ∈ S,
      coreRepresentation (Fin 6) a.val v ∈ S := by
    intro a v hv
    obtain ⟨x,hx⟩ := m.coordinate.surjective (Multiplicative.ofAdd v)
    have hx' : (m.coordinate x).toAdd = v := congrArg Multiplicative.toAdd hx
    rw [←hx'] at hv ⊢
    obtain ⟨b,rfl⟩ := m.quotient.surjective a
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) b
    rw [←m.equivariant]
    apply (hmem _).mpr
    exact (mem_normalizer_iff.mp (hLN l.property) x.val).mp ((hmem x).mp hv)
  by_cases ht : S = ⊤
  · right
    apply le_antisymm hNV
    intro v hv
    apply (hmem ⟨v,hv⟩).mp
    rw [ht]
    trivial
  · left
    intro v hv
    apply (m.mem_fixed_iff ⟨v,hNV hv⟩).mpr
    apply (core_fixed_iff_constant (by simp) _).mp
    intro a
    exact core_proper_invariant_fixed (by decide) S hs ht a.val
      (m.coordinate ⟨v,hNV hv⟩).toAdd ((hmem _).mpr hv)

/-- The literal commutator identity makes the original component short.
The full five-space and its fixed line are retained in the invariant interval. -/
theorem original_augmentation_short_of_core_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = V) :
    ChapterC.IsShort L ∧ (ChapterC.blockU L).map L.subtype = V := by
  have hcore : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hcomm : ⁅L.pCoreIn 2,L⁆ = V := le_antisymm
    ((commutator_mono hcore le_rfl).trans hc.le)
    (D.eq_commutator.le.trans (commutator_mono D.le_componentCore le_rfl))
  have hU : (ChapterC.blockU L).map L.subtype = V := by
    rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact hcomm
  let b : ChapterC.blockU L ≃* V :=
    ((ChapterC.blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hU)
  have hi : ChapterC.BlockModuleIrreducible L := by
    constructor
    · apply lt_of_le_of_ne inf_le_left
      intro he
      have hv : V ≤ centralizer (L : Set G) := by
        rw [←hU]
        rintro v ⟨u,hu,rfl⟩ l hl
        have huz : u ∈ center L := (he ▸ hu).2
        exact congrArg Subtype.val ((mem_center_iff.mp huz) ⟨l,hl⟩)
      exact D.ne_bot (D.eq_commutator.trans (commutator_eq_bot_iff_le_centralizer.mpr hv))
    · intro N hn hfixed hNU
      let := hn
      have hNV : N.map L.subtype ≤ V := (map_mono hNU).trans_eq hU
      have hLN : L ≤ normalizer (N.map L.subtype : Set G) := by
        simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
          N.le_normalizer_map L.subtype
      rcases core_invariant_dichotomy D m (N.map L.subtype) hNV hLN with hz | ht
      · left
        apply le_antisymm (le_inf hNU ?_) hfixed
        intro n hn
        apply mem_center_iff.mpr
        intro l
        exact Subtype.ext (hz (mem_map_of_mem L.subtype hn) l.val l.property)
      · right
        exact map_injective L.subtype_injective (ht.trans hU.symm)
  refine ⟨{ finite := inferInstance
            twoPerfect := h.maximal_faithful.2.1.2.1
            fitting := h.maximal_faithful.2.1.2.2
            elementary := ?_
            central := ?_
            quotient := Or.inl h.quasisimple
            irreducible := hi },hU⟩
  · let := D.elementary
    exact IsElementaryAbelian.of_surjective b.symm.toMonoidHom b.symm.surjective
  · intro v hv q hq
    apply Subtype.ext
    exact ((D.core_centralizes (hcore (mem_map_of_mem L.subtype hq))) v.val
      (hU ▸ mem_map_of_mem L.subtype hv)).symm

open Chapter14.Section03.FaithfulSource Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

/-- A moving actor fixing the rest of the original linear two-core forces
its commutator with the literal two-residual to be exactly V₀. -/
theorem original_linear_core_commutator
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (hc : ⁅(A ⊔ B).pCoreIn 2,V⁆ ≤
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B))
    (hm : ⁅V,conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)⁆ ≠ ⊥) :
    ⁅(A ⊔ B).pCoreIn 2,(pResidual 2 (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype⁆ =
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) := by
  let X := A ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hVX : V ≤ X := D.le_sylow.trans hTX
  have hUX : U ≤ X := conjugateSpanBy_le_self (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hk := Amalgam.original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB
  let : (U.subgroupOf X).Normal := hk.1.normal
  obtain ⟨C,hC,_,_,_,_,⟨eC⟩⟩ := hlin.1
  let K := C.subgroupOf X
  have hmap : K.map X.subtype = C := map_subgroupOf_eq_of_le hC.1
  have eK : ((K.map X.subtype) ⧸ pCore 2 (K.map X.subtype)) ≃* Matrix.PSL3Two.PSL :=
    hmap.symm ▸ eC
  obtain ⟨eX⟩ := Amalgam.original_pair_linear_full_quotient h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hC.2 eK
  let q := eX.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hqker : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ eX.injective,QuotientGroup.ker_mk']
  have hescape : ¬ V.subgroupOf X ≤ q.ker := by
    intro hv
    have hVC : V ≤ centralizer (U : Set G) := by
      intro v hvV
      have hvQ := mem_map_of_mem X.subtype
        (hqker ▸ (hv (show (⟨v,hVX hvV⟩ : X) ∈ V.subgroupOf X from hvV)))
      exact (hk.2.1.symm.le.trans inf_le_right) hvQ
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr hVC)
  have hci : ⁅pCore 2 X,V.subgroupOf X⁆ ≤ U.subgroupOf X := by
    apply commutator_le.mpr
    intro a ha v hv
    exact hc (commutator_mem_commutator (mem_map_of_mem X.subtype ha) hv)
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  have hi := commutator_pResidual_le_of_simple_kernel_escape 2 q
    (eX.surjective.comp (QuotientGroup.mk'_surjective _)) (hqker ▸ pCore_isPGroup)
    (pCore 2 X) (U.subgroupOf X) (V.subgroupOf X) hescape hci
  have hb := map_mono (f := X.subtype) hi
  rw [map_commutator,map_subgroupOf_eq_of_le hUX] at hb
  apply le_antisymm hb
  have hmoved := Amalgam.original_pair_linear_whole_moved h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hC.2 eK
  have hr := (Amalgam.original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hC.2).1
  change ⁅U,K.map X.subtype⁆ = U at hmoved
  rw [←hr] at hmoved
  have hUQ : U ≤ X.pCoreIn 2 := by
    have hh := map_mono (f := X.subtype) hk.1.le_pCore
    rwa [map_subgroupOf_eq_of_le hUX] at hh
  exact hmoved.symm.le.trans (commutator_mono hUQ le_rfl)
/-- The original mixed conjugator fixes H₀ and V₀. Both literal core
commutators are the original modules, and the A₆ component is short. -/
theorem original_linear_pair_mixed_blocks
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ →
      g ∈ B ∧ X.conjBy g = X ∧ U.conjBy g = U ∧
        ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = V ∧
        ChapterC.IsShort L ∧ (ChapterC.blockU L).map L.subtype = V ∧
        ⁅X.pCoreIn 2,(pResidual 2 X).map X.subtype⁆ = U := by
  let X := A ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  dsimp only
  intro g h₁ h₂ hm
  obtain ⟨_,hgB,hUg,_,_,hcL,hcX⟩ := original_linear_pair_mixed_return
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 hlin eL hM hZV W hW hTW hB hfusion g h₁ h₂ hm
  change U.conjBy g = U at hUg
  have hmove : ⁅V,U⁆ ≠ ⊥ := by rwa [hUg] at hm
  have hUM : U ≤ L ⊔ (T : Subgroup G) := by
    have hUR : U ≤ B.pCoreIn 2 := hUg ▸ h₁
    apply hUR.trans ((pCoreIn_le 2 B).trans ?_)
    rw [hB]
    exact inf_le_left
  have hCL := original_augmentation_core_commutator h structural D m eL U hUM hmove hcL
  have hshort := original_augmentation_short_of_core_commutator h D m hCL
  have hCX := original_linear_core_commutator h₀ h structural D m hTA hTB eA eB hne
    hout hindexL hindexA hindexB hres h1332 hlin hcX hmove
  exact ⟨hgB,mem_normalizer_iff_map_conj_eq.mp (X.le_normalizer (mem_sup_right hgB)),
    hUg,hCL,hshort.1,hshort.2,hCX⟩
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
