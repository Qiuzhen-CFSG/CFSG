module
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSource
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Configurations
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadical

/-!
# Radical control in the ordinary Hermitian J₄ configuration

The original PSL₃(4) section contributes 2⁶ to the index of the native
radical image. Since J₄ has two-part 2²¹, that image has order at most
2¹⁵, less than the square of the original nine-space's order. Irreducibility
and the literal radical-normalizer placement force the radical to centralize
the module image, and its full normalizer to preserve that image.

Lift through the same inclusion and central quotient. The original residual
fully moves the module and centralizes the covering center, so normalizing
their product preserves the module itself. Disjointness from the covering
center removes central displacement. Finally the original radical's central
product decomposition gives centralization by all of O₂(J).

The Chapter 12 consumer supplies the exact order from the Hermitian marking
and fixed-point vanishing from its original non-FF hypotheses. The proof-only
Mathieu import reuses generic transports while keeping the unrelated,
homonymous chapter exports out of the public scope. No Mathieu hypothesis,
normality in N_G(A), or containment of T in H is used.
Source: Aschbacher--Smith C.2.8 and C.3.2--4, printed pp.147,149--150,
with 4.2.13 and 4.4.3, pp.611--612,623, as used in 8.2.7, p.718,
refs/quasithin.pdf. Native carrier facts retain their imported attribution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem normalizer_le_of_large_irreducible
    {X : Type*} [Group X] [Finite X] (E F U : Subgroup X)
    (hEU : E ≤ U) (hFE : F ≤ normalizer (E : Set X))
    (hNF : normalizer (U : Set X) ≤ normalizer (F : Set X))
    (hirr : ∀ A : Subgroup X, A ≤ E → F ≤ normalizer (A : Set X) → A = ⊥ ∨ A = E)
    (hlarge : Nat.card U < Nat.card E * Nat.card E) :
    normalizer (U : Set X) ≤ normalizer (E : Set X) := by
  intro u hu
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply (ti_under_actor_normalizer E F hFE hirr (hNF hu)).resolve_left
  intro hdis
  let Eg := E.map (MulAut.conj u).toMonoidHom
  have hEgU : Eg ≤ U := (map_mono (f := (MulAut.conj u).toMonoidHom) hEU).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp hu)
  have hprod : (E : Set X) * (Eg : Set X) ⊆ U := by
    rintro _ ⟨a,ha,b,hb,rfl⟩
    exact U.mul_mem (hEU ha) (hEgU hb)
  have hcount := card_set_mul_mul_card_inf E Eg
  rw [hdis,card_bot,mul_one,card_map_of_injective (MulAut.conj u).injective] at hcount
  have hle : Nat.card ((E : Set X) * (Eg : Set X)) ≤ Nat.card U :=
    Nat.card_le_card_of_injective (Set.inclusion hprod) (Set.inclusion_injective hprod)
  exact (not_lt_of_ge (hcount ▸ hle)) hlarge

/-- The actual radical and nine-space images retain their kernels, order bounds,
centralization and full radical-normalizer invariance. -/
theorem sourceOrbit_hermitian_ordinary_radical_image_of_card
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
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    IsPRadical 2 U ∧ IsElementaryAbelian 2 E ∧ E ≤ U ∧
      Nat.card E = 512 ∧ Nat.card U ≤ 32768 ∧ E.relIndex U ≤ 64 ∧
      U ≤ centralizer (E : Set Janko4.Model) ∧
      normalizer (U : Set Janko4.Model) ≤ normalizer (E : Set Janko4.Model) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let Fm := (F.comap j).map q
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  have hUr : IsPRadical 2 U := hn.2.1
  have hFU : Fm ≤ normalizer (U : Set Janko4.Model) := hn.2.2.2.1
  have hFE : Fm ≤ normalizer (E : Set Janko4.Model) := hn.2.2.2.2.1
  have hEU : E ≤ U := hn.2.2.2.2.2.1
  have hEe : IsElementaryAbelian 2 E := hn.2.2.2.2.2.2.1
  have hcard : Nat.card E = 512 := hn.2.2.2.2.2.2.2.1.trans hcardV
  let a : (Fm ⧸ pCore 2 Fm) ≃* (L ⧸ pCore 2 L) := hn.2.2.2.2.2.2.2.2.some
  let z := ((centerQuotientCongr a).trans (D.orbitCentralQuotientEquiv h)).trans eQ
  have hd : 2^6 ∣ Nat.card (Fm ⧸ pCore 2 Fm) := by
    apply (show 2^6 ∣ Nat.card ((Fm ⧸ pCore 2 Fm) ⧸ center (Fm ⧸ pCore 2 Fm)) from ?_).trans
      (card_quotient_dvd_card _)
    rw [Nat.card_congr z.toEquiv,Matrix.PSL3.LinearThree.card_projective,hfield]
    decide
  have hk : IsPGroup 2 Fm.subtype.ker := by
    rw [(MonoidHom.ker_eq_bot_iff Fm.subtype).mpr Fm.subtype_injective]
    exact IsPGroup.of_subsingleton 2 _
  obtain ⟨n,hnc,hnb⟩ := Janko4.normalized_twoGroup_card_le_of_core_index
    Fm.subtype hk 6 hd U hUr.isPGroup (by rwa [range_subtype])
  have hu : Nat.card U ≤ 32768 := by
    rw [hnc]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 15)
  have hcount := (E.subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv] at hcount
  change Nat.card E * E.relIndex U = Nat.card U at hcount
  have hindex : E.relIndex U ≤ 64 := by rw [hcard] at hcount; omega
  have hirr := D.sourceOrbit_pushingUp_native_irreducible hfix hw K hK e
  have hlarge : Nat.card U < Nat.card E * Nat.card E := by rw [hcard]; omega
  refine ⟨hUr,hEe,hEU,hcard,hu,hindex,?_,?_⟩
  · exact le_centralizer_of_large_irreducible E Fm U hUr.isPGroup hEU hFE hFU
      (U.le_normalizer.trans hn.2.2.1) hirr hlarge
  · exact normalizer_le_of_large_irreducible E Fm U hEU hFE hn.2.2.1 hirr hlarge

private theorem centralizes_moved_of_central_quotient
    {X : Type*} [Group X] (U E F : Subgroup X)
    (hUF : U ≤ normalizer (F : Set X))
    (hFE : F ≤ normalizer (E : Set X))
    (hmove : ⁅E,F⁆ = E) (hc : ⁅U,E⁆ ≤ center X)
    (hdis : E ⊓ center X = ⊥) : U ≤ centralizer (E : Set X) := by
  let Z := center X
  have hZC (B : Subgroup X) : Z ≤ centralizer (B : Set X) := by
    intro z hz b _
    exact mem_center_iff.mp hz b
  have hEF : ⁅E ⊔ Z,F⁆ = E := le_antisymm
    (commutator_le_of_le_sup_centralizing (E ⊔ Z) F E Z
      (by rw [sup_comm]) (hZC E) (hZC F) hFE)
    (hmove.symm.le.trans (commutator_mono le_sup_left le_rfl))
  have hUEZ : U ≤ normalizer (E ⊔ Z : Subgroup X) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal (E ⊔ Z) E Z U (E ⊔ Z)
      (E ⊔ Z).le_normalizer le_sup_left le_sup_right
    · exact (commutator_comm E U).le.trans (hc.trans le_sup_right)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr (hZC U)).le.trans bot_le
  have hUE : U ≤ normalizer (E : Set X) := by
    intro u hu
    rw [←hEF,mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hUEZ hu),
      mem_normalizer_iff_map_conj_eq.mp (hUF hu)]
  exact commutator_eq_bot_iff_le_centralizer.mp
    (bot_unique ((le_inf (le_normalizer_iff_commutator_le_right.mp hUE) hc).trans_eq hdis))

/-- The whole original radical centralizes V; the full normalizer of its
component intersection preserves V before removing any central kernel. -/
theorem sourceOrbit_hermitian_ordinary_radical_control_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    J.pCoreIn 2 ≤ centralizer (V : Set G) ∧
      (normalizer ((J.pCoreIn 2).comap (H.subtype.comp K.subtype) : Set K)).map
        (H.subtype.comp K.subtype) ≤ normalizer (V : Set G) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let Kg := K.map H.subtype
  let Uk := R.comap j
  let Ek := V.comap j
  let Fk := F.comap j
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = Kg := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hv := D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK
  have hVK : V ≤ Kg := hv.1.trans inf_le_right
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ Kg := by
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hc.ordinary_component_contains_original K hK hf,rfl⟩
  have hFm : Fk.map j = F := map_comap_eq_self (hFK.trans_eq hjr.symm)
  have hEm : Ek.map j = V := map_comap_eq_self (hVK.trans_eq hjr.symm)
  have hUm : Uk.map j = R ⊓ Kg := by rw [map_comap_eq,hjr,inf_comm]
  have hmove : ⁅Ek,Fk⁆ = Ek := map_injective hj (by
    rw [map_commutator,hFm,hEm]
    exact hw.2.2.2.2.2.2.2.2.2.1.symm)
  have hFE : Fk ≤ normalizer (Ek : Set K) :=
    (comap_mono (((map_subtype_le _).trans inf_le_left).trans D.normalizes)).trans
      (V.le_normalizer_comap j)
  have hFM : F ≤ H ⊓ normalizer (L : Set G) :=
    le_inf hFH (((map_subtype_le _).trans inf_le_left).trans L.le_normalizer)
  have hMF : H ⊓ normalizer (L : Set G) ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hFM).mp hw.2.2.2.2.2.2.2.2.1
  have hUF : Uk ≤ normalizer (Fk : Set K) :=
    (comap_mono (hc.radical_le.trans hMF)).trans (F.le_normalizer_comap j)
  have hb := D.sourceOrbit_hermitian_ordinary_radical_image_of_card
    h hfix hcardV eQ hfield hw K hK e
  have hcent : Uk.map q ≤ centralizer (Ek.map q : Set Janko4.Model) := hb.2.2.2.2.2.2.1
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hcomm : ⁅Uk,Ek⁆ ≤ center K := by
    rw [←hk,←Subgroup.map_eq_bot_iff,map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcent
  have hdis : Ek ⊓ center K = ⊥ := by
    apply bot_unique
    intro z hz
    apply hj
    have hzC : j z ∈ centralizer (Kg : Set G) := by
      rintro _ ⟨a,ha,rfl⟩
      exact congrArg j (mem_center_iff.mp hz.2 ⟨a,ha⟩)
    have he : j z ∈ (⊥ : Subgroup G) := hv.2 ▸
      ⟨hz.1,hv.1 hz.1 |>.1,hzC⟩
    exact (mem_bot.mp he).trans (map_one j).symm
  have hUk := centralizes_moved_of_central_quotient Uk Ek Fk hUF hFE hmove hcomm hdis
  have hRC : R ⊓ Kg ≤ centralizer (V : Set G) := by
    rw [←hUm]
    rintro _ ⟨u,hu,rfl⟩ v hv
    obtain ⟨a,ha,rfl⟩ := hEm.symm ▸ hv
    exact congrArg j (hUk hu a ha)
  have hf := sourceOrbit_pushingUp_core_central_product hw K hK e
  refine ⟨hf.1.le.trans (sup_le hRC (inf_le_right.trans (centralizer_le hVK))),?_⟩
  let := hK.2
  have hNu : normalizer (Uk : Set K) ≤ (H ⊓ normalizer (L : Set G)).comap j := by
    apply hc.ordinary_radical_normalizer_le_local_of_inner K hK
    intro a
    exact Janko4.perfect_cover_conj_surjective e a
  have hNF : normalizer (Uk : Set K) ≤ normalizer (Fk : Set K) :=
    (hNu.trans (comap_mono hMF)).trans (F.le_normalizer_comap j)
  have hnE : (normalizer (Uk : Set K)).map q ≤
      normalizer (Ek.map q : Set Janko4.Model) :=
    (Uk.le_normalizer_map q).trans hb.2.2.2.2.2.2.2
  have hNEZ : normalizer (Uk : Set K) ≤ normalizer (Ek ⊔ center K : Subgroup K) := by
    have hh := (map_le_iff_le_comap.mp hnE).trans ((Ek.map q).le_normalizer_comap q)
    rwa [comap_map_eq,hk] at hh
  have hZC (B : Subgroup K) : center K ≤ centralizer (B : Set K) := by
    intro z hz b _
    exact mem_center_iff.mp hz b
  have hEF : ⁅Ek ⊔ center K,Fk⁆ = Ek := le_antisymm
    (commutator_le_of_le_sup_centralizing (Ek ⊔ center K) Fk Ek (center K)
      (by rw [sup_comm]) (hZC Ek) (hZC Fk) hFE)
    (hmove.symm.le.trans (commutator_mono le_sup_left le_rfl))
  have hNE : normalizer (Uk : Set K) ≤ normalizer (Ek : Set K) := by
    intro u hu
    rw [←hEF,mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hNEZ hu),
      mem_normalizer_iff_map_conj_eq.mp (hNF hu)]
  have hh := (map_mono (f := j) hNE).trans (Ek.le_normalizer_map j)
  rwa [hEm] at hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
