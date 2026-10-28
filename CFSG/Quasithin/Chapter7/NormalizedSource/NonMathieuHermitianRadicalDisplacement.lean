module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianRadicalKernel
public import Theory.Representation.PSL3Four.SmallTwoGroupAction
public import Theory.GroupTheory.SmallTwoSectionActions
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.RadicalNormalizerModule
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadicalNormalizer
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadical

/-!
# Radical displacement on the original Hermitian nine-space

The actual native intersection residual has full two-core quotient PSL₃(4),
by the preceding central-kernel calculation. It therefore acts trivially
on U/E, whose order is at most 64. Its commutator on the full native radical
is exactly E. Lift this equality through the entire central cover: perfect
coprime commutators remove the central term, and the complementary central
factor contributes nothing. Thus [O₂(J),F] is the original module V.

The original pushing-up module W has the same order as V and is moved by F,
so W = V. Characteristic-two normalizer control now makes the full native
residual normalizer preserve E; the moved-module lifting theorem gives the
same conclusion inside the full covering component, retaining its center.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612, used by 4.4.3 and
8.2.7, printed pp.623,718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

theorem sourceOrbit_hermitian_ordinary_radical_displacement_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    ⁅U,B⁆ = E := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Fk := F.comap j
  let Ek := V.comap j
  let U := ((J.pCoreIn 2).comap j).map q
  let E := Ek.map q
  let B := Fk.map q
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hc.ordinary_component_contains_original K hK
  let b : Fk ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFH)
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : Group.IsPerfect Fk := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective Fk)
  have hEV : Ek.map j = V := map_comap_eq_self
    ((D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans
      inf_le_right |>.trans_eq hjr.symm)
  have hBF : Fk.map j = F := by
    apply map_comap_eq_self
    rw [hjr]
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hFK hf,rfl⟩
  have hmove : ⁅E,B⁆ = E := by
    have hk : ⁅Ek,Fk⁆ = Ek := map_injective hj (by
      rw [map_commutator,hEV,hBF]
      exact hw.2.2.2.2.2.2.2.2.2.1.symm)
    rw [←map_commutator,hk]
  have hn := @sourceOrbit_pushingUp_native_radical G instG finG T L V D hfix A J H W hw K hK e
  dsimp only at hn
  have hBU : B ≤ normalizer (U : Set Janko4.Model) := hn.2.2.2.1
  have hBE : B ≤ normalizer (E : Set Janko4.Model) := hn.2.2.2.2.1
  have hEU : E ≤ U := hn.2.2.2.2.2.1
  have hb := D.sourceOrbit_hermitian_ordinary_radical_image_of_card
    h hfix hcardV eQ hfield hw K hK e
  have hcent : U ≤ centralizer (E : Set Janko4.Model) := hb.2.2.2.2.2.2.1
  let : (E.subgroupOf U).Normal := normal_subgroupOf_of_le_normalizer
    (hcent.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨em⟩ := (D.sourceOrbit_hermitian_ordinary_center_kernel_of_card
    h hfix hcardV eQ hfield hw K hK e).2.2.2
  have hupper : ⁅U,B⁆ ≤ E := commutator_le_of_section_hom_trivial B U E hBU hBE
    (fun f => Representation.PSL3Four.action_eq_one_of_card_lt_512 em hfield
      (hn.2.1.isPGroup.to_quotient _) (by
        change E.relIndex U < 512
        exact lt_of_le_of_lt hb.2.2.2.2.2.1 (by decide : 64 < 512)) f)
  exact le_antisymm hupper (hmove.symm.le.trans (commutator_mono hEU le_rfl))

theorem sourceOrbit_hermitian_ordinary_radical_commutator_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    ⁅J.pCoreIn 2,(solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype⁆ = V := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let Kg := K.map H.subtype
  let Z := (center K).map j
  let C := R ⊓ centralizer (Kg : Set G)
  have hjr : j.range = Kg := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK' := hc.ordinary_component_contains_original K hK
  have hFK : F ≤ Kg := by
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hFK' hf,rfl⟩
  have hVK := (D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans inf_le_right
  have hFmap : (F.comap j).map j = F := map_comap_eq_self (hFK.trans_eq hjr.symm)
  have hVmap : (V.comap j).map j = V := map_comap_eq_self (hVK.trans_eq hjr.symm)
  have hRmap : (R.comap j).map j = R ⊓ Kg := by rw [map_comap_eq,hjr,inf_comm]
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have he := @sourceOrbit_hermitian_ordinary_radical_displacement_of_card G instG finG T L V D
    h hfix hcardV k _ _ eQ hfield A J H W hw K hK e
  have hpre : ⁅R ⊓ Kg,F⁆ ≤ V ⊔ Z := by
    have hh : ⁅R.comap j,F.comap j⁆ ≤ (V.comap j) ⊔ center K := by
      have hm : (⁅R.comap j,F.comap j⁆).map q ≤ (V.comap j).map q := by
        rw [map_commutator]
        exact he.le
      have hh := (map_le_iff_le_comap).mp hm
      rwa [comap_map_eq,hk] at hh
    have hh := map_mono (f := j) hh
    rwa [map_commutator,hRmap,hFmap,Subgroup.map_sup,hVmap] at hh
  have hZcentral (X : Subgroup G) (hX : X ≤ Kg) : Z ≤ centralizer (X : Set G) := by
    rintro z ⟨z,hz,rfl⟩ x hx
    obtain ⟨k,hk,rfl⟩ := hX hx
    exact congrArg j (mem_center_iff.mp hz ⟨k,hk⟩)
  have hFR : F ≤ normalizer (R : Set G) :=
    (le_conjugateSpanBy F (H ⊓ normalizer (L : Set G))).trans hc.span_normalizes_radical
  have hFV : F ≤ normalizer (V : Set G) := ((map_subtype_le _).trans inf_le_left).trans D.normalizes
  let : Group.IsPerfect F := Group.IsPerfect.map _
  have hpF : IsPPerfect 2 F := by
    intro N hN hp
    let := hN
    have hs : Subsingleton (F ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (F ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro f _
    exact (QuotientGroup.eq_one_iff f).mp (hs.elim _ _)
  have hfirst : ⁅R ⊓ Kg,F⁆ ≤ V := by
    rw [←commutator_isPPerfect_idempotent F (R ⊓ Kg) hpF
      ((isPGroup_pCoreIn 2 J).to_le inf_le_left)
      ((le_inf hFR (hFK.trans Kg.le_normalizer)).trans inf_normalizer_le_normalizer_inf)]
    exact commutator_le_of_le_sup_centralizing _ F V Z
      (hpre.trans (by rw [sup_comm])) (hZcentral V hVK) (hZcentral F hFK) hFV
  have hf := sourceOrbit_pushingUp_core_central_product hw K hK e
  have hRC : R ⊓ Kg ≤ centralizer (C : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hf.2.1
  have hCF : C ≤ centralizer (F : Set G) := inf_le_right.trans (centralizer_le hFK)
  have hupper : ⁅R,F⁆ ≤ V := by
    apply commutator_le.mpr
    intro r hr f hf'
    have hr' : r ∈ ((R ⊓ Kg : Subgroup G) : Set G) * (C : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ (hRC.trans (Subgroup.centralizer_le_normalizer _))]
      exact hf.1 ▸ hr
    obtain ⟨a,ha,c,hc,rfl⟩ := hr'
    have hcf : ⁅c,f⁆ = 1 := (show Commute c f from (hCF hc f hf').symm).commutator_eq
    rw [commutatorElement_mul_left_eq_conj_mul,hcf,mul_one,mul_inv_cancel,one_mul]
    exact hfirst (commutator_mem_commutator ha hf')
  exact le_antisymm hupper (hw.2.2.2.2.2.2.2.2.2.1.le.trans
    (commutator_mono hw.2.2.2.2.2.1 le_rfl))

theorem sourceOrbit_hermitian_ordinary_auxiliary_module_eq_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) : W = V := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let M := H ⊓ normalizer (L : Set G)
  have hc := hw.2.2.2.2.2.2.1
  have hFM : F ≤ M := hc.component_le
  have hMF : M ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hFM).mp hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy F M = F :=
    le_antisymm (conjugateSpanBy_le le_rfl hMF) (le_conjugateSpanBy F M)
  have hW := hc.module_commutator
  rw [hspan] at hW
  have hWR := hc.module_le_center_radical.trans (map_subtype_le _)
  have hcomm := D.sourceOrbit_hermitian_ordinary_radical_commutator_of_card h hfix hcardV eQ hfield hw K hK e
  apply eq_of_le_of_card_ge
  · exact hW.le.trans ((commutator_mono hWR le_rfl).trans_eq hcomm)
  · exact hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sourceOrbit_hermitian_ordinary_normalizer_core_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    let Q := (normalizer (B : Set Janko4.Model)).pCoreIn 2
    E ≤ Q ∧ Q ≤ U ∧ ⁅Q,B⁆ = E ∧
      normalizer (B : Set Janko4.Model) ≤ normalizer (E : Set Janko4.Model) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Ek := V.comap j
  let Bk := F.comap j
  let U := ((J.pCoreIn 2).comap j).map q
  let E := Ek.map q
  let B := Bk.map q
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hc.ordinary_component_contains_original K hK
  have hEV : Ek.map j = V := map_comap_eq_self
    ((D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans
      inf_le_right |>.trans_eq hjr.symm)
  have hBF : Bk.map j = F := by
    apply map_comap_eq_self
    rw [hjr]
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hFK hf,rfl⟩
  have hmove : ⁅E,B⁆ = E := by
    have hk : ⁅Ek,Bk⁆ = Ek := map_injective hj (by
      rw [map_commutator,hEV,hBF]
      exact hw.2.2.2.2.2.2.2.2.2.1.symm)
    rw [←map_commutator,hk]
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  have hN := sourceOrbit_pushingUp_native_normalizer hw K hK e
  have hchar : centralizer (pCore 2 (normalizer (B : Set Janko4.Model)) :
      Set (normalizer (B : Set Janko4.Model))) ≤ pCore 2 (normalizer (B : Set Janko4.Model)) := by
    rw [hN.1]
    exact hN.2
  exact Subgroup.radical_normalizer_core_displacement U E B hn.2.1 hn.2.2.1 hchar
    hn.2.2.2.2.2.1
    (D.sourceOrbit_hermitian_ordinary_radical_image_of_card h hfix hcardV eQ hfield hw K hK e).2.2.2.2.2.2.1
    (D.sourceOrbit_hermitian_ordinary_radical_displacement_of_card h hfix hcardV eQ hfield hw K hK e) hmove

theorem sourceOrbit_hermitian_ordinary_cover_module_normalizer_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    normalizer (F.comap j : Set K) ≤ normalizer (V.comap j : Set K) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Ek := V.comap j
  let Bk := F.comap j
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hc.ordinary_component_contains_original K hK
  have hEV : Ek.map j = V := map_comap_eq_self
    ((D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans
      inf_le_right |>.trans_eq hjr.symm)
  have hBF : Bk.map j = F := by
    apply map_comap_eq_self
    rw [hjr]
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hFK hf,rfl⟩
  have hmove : ⁅Ek,Bk⁆ = Ek := map_injective hj (by
    rw [map_commutator,hEV,hBF]
    exact hw.2.2.2.2.2.2.2.2.2.1.symm)
  have hker : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact Subgroup.normalizer_le_of_moved_map_normalizer_le q hker.le Ek Bk
    (comap_mono hw.2.2.2.2.2.2.2.2.2.2.1) hmove
    (D.sourceOrbit_hermitian_ordinary_normalizer_core_of_card h hfix hcardV eQ hfield hw K hK e).2.2.2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
