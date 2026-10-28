module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.LocalSylow
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# The elementary Thompson subgroup on the original M24 branch

Write W for the original cocode subgroup `D.sourceOrbit`. Its exact kernel
and M24 marking give |L| = 2^11 |M24|. Comparing Sylow orders with the genuine
type-J4 centralizer puts the original T inside L. The non-FF centralization
result and maximum elementary order then prove J(T) = W. Characteristic two
and the same full automizer give C_G(W) = W and N_G(W) = L.

For the common Sylow U of C_G(z) and N_G(Z), conjugacy inside C_G(z)
transports W, L and the original cocode action. Thus J(U) is the unique
maximum elementary subgroup, of rank eleven, with its actual normalizer
and transported M24 marking; the conjugation fixes the original z.

These are consequences of the original Mathieu inputs. General type-J4
local-data existence, containment of Z in J(U), centralization of Z by
J(U), Todd splitting and the exact overlaps remain source obligations.

Source: Aschbacher--Smith, 8.2.12--14, printed pp.722--723;
Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent. Math.
105 (1991), (4.6)--(4.8), pp.598--599, DOI 10.1007/BF01232280.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))

include D h hmany hV hq hnon a E hE

/-- The original component has the order of the cocode extension of M24. -/
theorem sourceOrbit_m24_component_card : Nat.card L = 501397585920 := by
  have hcore := (D.sourceOrbit_m24_cocode_block_core h hmany hV hq hnon a E hE).2.2
  have hc : Nat.card (pCore 2 L) = 2048 := by
    rw [←card_map_of_injective L.subtype_injective]
    change Nat.card (L.pCoreIn 2) = _
    rw [←hcore]
    change Nat.card (Additive D.sourceOrbit) = _
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  let f := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have hf : Function.Surjective f := a.surjective.comp
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq))
  have hk : f.ker = pCore 2 L :=
    (MonoidHom.ker_comp_of_injective _ _ a.injective).trans
      (D.sourceOrbit_largeMathieu_component_kernel h.toHypothesis1221 (.inr hq))
  have hh := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,m24_order,hk,hc] at hh
  exact hh.symm

include z hz hne hquot

/-- The original ambient Sylow subgroup is contained in the original component. -/
theorem sourceOrbit_m24_sylow_le_component : (T : Subgroup G) ≤ L := by
  have ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  have hTC : (T : Subgroup G) ≤ Recognition.JankoFour.centralizer (z : G) :=
    fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  have hcT := ThreeSpaceData.common_sylow_card ht T hTC
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)
    from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le
    (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] at hP
  have hcP : Nat.card P = 2^21 := by
    have hh := P.card_eq_multiplicity
    rw [D.sourceOrbit_m24_component_card h hmany hV hq hnon a E hE,
      show (501397585920 : ℕ) = 2^21 * 239085 from by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_pow,Finsupp.add_apply,Finsupp.smul_apply,
      Nat.Prime.factorization_self (by decide : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 239085)] at hh
    simpa using hh
  have he : (P : Subgroup L).map L.subtype = (T : Subgroup G) := by
    apply eq_of_le_of_card_ge (hP ▸ inf_le_left)
    rw [card_map_of_injective L.subtype_injective,hcP,hcT]
  exact he ▸ map_subtype_le _

/-- The original cocode subgroup is self-centralizing in T. -/
theorem sourceOrbit_m24_sylow_centralizer : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = D.sourceOrbit := by
  have hTL := sourceOrbit_m24_sylow_le_component D h hmany hV hq hnon a E hE z hz hne hquot
  have hh := D.orbit_centralizer h.toHypothesis1221
  rw [←D.sourceOrbit_eq,sup_eq_left.mpr hTL] at hh
  exact hh.trans (D.sourceOrbit_m24_cocode_block_core h hmany hV hq hnon a E hE).2.2.symm

/-- The original cocode subgroup is the elementary Thompson subgroup of T. -/
theorem sourceOrbit_m24_thompson_eq : elementaryAbelianMaxJ (T : Subgroup G) = D.sourceOrbit := by
  have hj : elementaryAbelianMaxJ (T : Subgroup G) ≤ D.sourceOrbit := by
    rw [←sourceOrbit_m24_sylow_centralizer D h hmany hV hq hnon a E hE z hz hne hquot]
    exact le_inf (sSup_le fun _ hA => hA.1)
      (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
  have ha : A ≤ D.sourceOrbit := (le_sSup hA).trans hj
  have he : A = D.sourceOrbit := eq_of_le_of_card_ge ha
    (hA.2.2 D.sourceOrbit D.sourceOrbit_weakClosure_setup.le_sylow inferInstance)
  exact le_antisymm hj (he ▸ le_sSup hA)

/-- Conjugacy inside C_G(z) transports the original Thompson subgroup. -/
theorem sourceOrbit_m24_thompson_conjugate (U : Sylow 2 G)
    (hUC : (U : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    ∃ g : centralizer ({(z : G)} : Set G),
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (U : Subgroup G) ∧
      D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom =
        elementaryAbelianMaxJ (U : Subgroup G) := by
  have hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) :=
    fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (centralizer ({(z : G)} : Set G))
    (T.subtype hTC) (U.subtype hUC)
  rw [Sylow.smul_subtype] at hg
  have he := congrArg Sylow.toSubgroup (Sylow.subtype_injective hg)
  refine ⟨g,he,?_⟩
  calc
    _ = (elementaryAbelianMaxJ (T : Subgroup G)).map
        (MulAut.conj (g : G)).toMonoidHom :=
      congrArg (fun A : Subgroup G => A.map (MulAut.conj (g : G)).toMonoidHom)
        (sourceOrbit_m24_thompson_eq D h hmany hV hq hnon a E hE z hz hne hquot).symm
    _ = elementaryAbelianMaxJ (U : Subgroup G) :=
      (elementaryAbelianMaxJ_map_equiv _ _).symm.trans (congrArg elementaryAbelianMaxJ he)

/-- The transported Thompson subgroup is elementary of order 2048 and is the unique maximum. -/
theorem sourceOrbit_m24_common_sylow_thompson (U : Sylow 2 G)
    (hUC : (U : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    IsElementaryAbelian 2 (elementaryAbelianMaxJ (U : Subgroup G)) ∧
      Nat.card (elementaryAbelianMaxJ (U : Subgroup G)) = 2048 ∧
      ∀ A : Subgroup G, A ∈ elementaryAbelianMaxSubgroups (U : Subgroup G) ↔
        A = elementaryAbelianMaxJ (U : Subgroup G) := by
  obtain ⟨g,hT,hJ⟩ := sourceOrbit_m24_thompson_conjugate D h hmany hV hq hnon a E hE z hz hne hquot U hUC
  have helem : IsElementaryAbelian 2 (elementaryAbelianMaxJ (U : Subgroup G)) :=
    hJ ▸ IsElementaryAbelian.map (MulAut.conj (g : G)).toMonoidHom
  have hle : elementaryAbelianMaxJ (U : Subgroup G) ≤ (U : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  refine ⟨helem,?_,?_⟩
  · rw [←hJ,card_map_of_injective (MulAut.conj (g : G)).injective]
    change Nat.card (Additive D.sourceOrbit) = _
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  · intro A
    constructor
    · intro hA
      exact eq_of_le_of_card_ge (le_sSup hA)
        (hA.2.2 _ hle helem)
    · rintro rfl
      obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty (U : Subgroup G)
      exact ⟨hle,helem,fun A hA he => (hB.2.2 A hA he).trans (card_le_of_le (le_sSup hB))⟩

/-- The full ambient normalizer has the original cocode subgroup as its two-core. -/
theorem sourceOrbit_m24_normalizer_twoCore :
    (normalizer (D.sourceOrbit : Set G)).pCoreIn 2 = D.sourceOrbit := by
  let N := normalizer (D.sourceOrbit : Set G)
  have hTN : (T : Subgroup G) ≤ N := D.sourceOrbit_weakClosure_setup.normalizes
  have hTL := sourceOrbit_m24_sylow_le_component D h hmany hV hq hnon a E hE z hz hne hquot
  have hcore := (D.sourceOrbit_m24_cocode_block_core h hmany hV hq hnon a E hE).2.2
  have hNT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow N (T.subtype hTN)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] using hh
  apply le_antisymm
  · have hn : L ≤ normalizer (N.pCoreIn 2 : Set G) :=
      D.sourceOrbit_component_normalizes.trans (N.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
    exact (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 N) (hNT.trans hTL) hn).trans_eq hcore.symm
  · exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
      D.sourceOrbit.le_normalizer le_rfl

/-- The original cocode subgroup is self-centralizing in the ambient group. -/
theorem sourceOrbit_m24_selfCentralizing : centralizer (D.sourceOrbit : Set G) = D.sourceOrbit := by
  let N := normalizer (D.sourceOrbit : Set G)
  have hc : centralizer (pCore 2 N : Set N) ≤ pCore 2 N :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T)
      ⟨D.sourceOrbit,D.sourceOrbit_weakClosure_setup.nontrivial,
        IsElementaryAbelian.isPGroup 2 D.sourceOrbit,rfl⟩
      D.sourceOrbit_weakClosure_setup.normalizes)
  have he := sourceOrbit_m24_normalizer_twoCore D h hmany hV hq hnon a E hE z hz hne hquot
  apply le_antisymm
  · intro x hx
    have hxN : x ∈ N := Subgroup.centralizer_le_normalizer _ hx
    have hxQ : (⟨x,hxN⟩ : N) ∈ pCore 2 N := hc (by
      intro y hy
      apply Subtype.ext
      exact hx y.val (he ▸ mem_map_of_mem N.subtype hy))
    exact he ▸ mem_map_of_mem N.subtype hxQ
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance

/-- The original component is the full ambient normalizer of the cocode subgroup. -/
theorem sourceOrbit_m24_normalizer_eq_component : normalizer (D.sourceOrbit : Set G) = L := by
  let N := normalizer (D.sourceOrbit : Set G)
  let f := a.toMonoidHom.comp D.sourceOrbit.normalizerMonoidHom.rangeRestrict
  have hf : Function.Surjective f := a.surjective.comp
    D.sourceOrbit.normalizerMonoidHom.rangeRestrict_surjective
  have hc := sourceOrbit_m24_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot
  have hk : f.ker = D.sourceOrbit.subgroupOf N := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,hc]
  have hcard : Nat.card f.ker = 2048 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe D.sourceOrbit.le_normalizer).toEquiv]
    change Nat.card (Additive D.sourceOrbit) = _
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  have hh := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,m24_order,hcard] at hh
  apply (eq_of_le_of_card_ge D.sourceOrbit_component_normalizes _).symm
  rw [←hh,sourceOrbit_m24_component_card D h hmany hV hq hnon a E hE]

omit [Finite G] h hmany hV hq hnon z hz hne hquot in
/-- Conjugation transports the original automizer marking and cocode coordinates together. -/
theorem sourceOrbit_m24_conjugate_cocode (g : G) :
    let f := MulAut.conj g
    letI : IsElementaryAbelian 2 (D.sourceOrbit.map f.toMonoidHom) :=
      IsElementaryAbelian.map f.toMonoidHom
    let a' := (automizerMapEquiv D.sourceOrbit f).symm.trans a
    let E' := (automizerModuleEquiv D.sourceOrbit f).symm.trans E
    ∀ b v, E' (automizerRepresentation (D.sourceOrbit.map f.toMonoidHom) b v) =
      cocodeRepresentation (a' b) (E' v) := by
  let f := MulAut.conj g
  let : IsElementaryAbelian 2 (D.sourceOrbit.map f.toMonoidHom) :=
    IsElementaryAbelian.map f.toMonoidHom
  dsimp only
  intro b v
  obtain ⟨b,rfl⟩ := (automizerMapEquiv D.sourceOrbit f).surjective b
  obtain ⟨v,rfl⟩ := (automizerModuleEquiv D.sourceOrbit f).surjective v
  rw [←automizerRepresentation_equivariant]
  simpa only [f,LinearEquiv.trans_apply,MulEquiv.trans_apply,
    LinearEquiv.symm_apply_apply,MulEquiv.symm_apply_apply] using hE b v

/-- The same marker-fixing conjugation identifies the full Thompson normalizer. -/
theorem sourceOrbit_m24_common_thompson_normalizer (U : Sylow 2 G)
    (hUC : (U : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    ∃ g : centralizer ({(z : G)} : Set G),
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (U : Subgroup G) ∧
      D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom =
        elementaryAbelianMaxJ (U : Subgroup G) ∧
      normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) =
        L.map (MulAut.conj (g : G)).toMonoidHom ∧
      (z : G) ∈ elementaryAbelianMaxJ (U : Subgroup G) := by
  obtain ⟨g,hT,hJ⟩ := sourceOrbit_m24_thompson_conjugate D h hmany hV hq hnon a E hE z hz hne hquot U hUC
  refine ⟨g,hT,hJ,?_,?_⟩
  · rw [←hJ,←map_equiv_normalizer_eq,
      sourceOrbit_m24_normalizer_eq_component D h hmany hV hq hnon a E hE z hz hne hquot]
  · rw [←hJ]
    exact mem_map.mpr ⟨z,z.property,
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property)⟩

/-- The elementary Thompson subgroup of each Sylow in C_G(z) has rank eleven. -/
theorem sourceOrbit_m24_common_thompson_rank (U : Sylow 2 G)
    (hUC : (U : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    primeRank 2 (elementaryAbelianMaxJ (U : Subgroup G)) = 11 := by
  obtain ⟨he,hc,_⟩ := sourceOrbit_m24_common_sylow_thompson D h hmany hV hq hnon a E hE z hz hne hquot U hUC
  let := he
  rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2),hc]
  norm_num

/-- The original three-space and its common Sylow carry the constructed elementary Thompson subgroup,
its full normalizer and the transported original cocode action, without an additional premise. -/
theorem sourceOrbit_m24_three_space_thompson :
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X)
      (U : Sylow 2 G) (g : centralizer ({(z : G)} : Set G)),
      (U : Subgroup G) ≤ centralizer ({(z : G)} : Set G) ⊓ normalizer (d.space : Set G) ∧
      d.R ≤ (U : Subgroup G) ∧ d.space ≤ (U : Subgroup G) ∧
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (U : Subgroup G) ∧
      D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom =
        elementaryAbelianMaxJ (U : Subgroup G) ∧
      IsElementaryAbelian 2 (elementaryAbelianMaxJ (U : Subgroup G)) ∧
      Nat.card (elementaryAbelianMaxJ (U : Subgroup G)) = 2048 ∧
      primeRank 2 (elementaryAbelianMaxJ (U : Subgroup G)) = 11 ∧
      (∀ A : Subgroup G, A ∈ elementaryAbelianMaxSubgroups (U : Subgroup G) ↔
        A = elementaryAbelianMaxJ (U : Subgroup G)) ∧
      normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) =
        L.map (MulAut.conj (g : G)).toMonoidHom ∧
      (z : G) ∈ elementaryAbelianMaxJ (U : Subgroup G) ∧
      let f := MulAut.conj (g : G)
      letI : IsElementaryAbelian 2 (D.sourceOrbit.map f.toMonoidHom) :=
        IsElementaryAbelian.map f.toMonoidHom
      let a' := (automizerMapEquiv D.sourceOrbit f).symm.trans a
      let E' := (automizerModuleEquiv D.sourceOrbit f).symm.trans E
      ∀ b v, E' (automizerRepresentation (D.sourceOrbit.map f.toMonoidHom) b v) =
        cocodeRepresentation (a' b) (E' v) := by
  have ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  obtain ⟨U,hU,_,hR,hZ,_⟩ := d.exists_common_sylow_structure ht
  obtain ⟨g,hT,hJ,hN,hzJ⟩ := sourceOrbit_m24_common_thompson_normalizer D h hmany hV hq hnon a E hE z hz hne hquot
    U (hU.trans inf_le_left)
  obtain ⟨he,hc,hu⟩ := sourceOrbit_m24_common_sylow_thompson D h hmany hV hq hnon a E hE z hz hne hquot
    U (hU.trans inf_le_left)
  have hr := sourceOrbit_m24_common_thompson_rank D h hmany hV hq hnon a E hE z hz hne hquot U (hU.trans inf_le_left)
  exact ⟨cubic,X,d,U,g,hU,hR,hZ,hT,hJ,he,hc,hr,hu,hN,hzJ,
    sourceOrbit_m24_conjugate_cocode D a E hE (g : G)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
