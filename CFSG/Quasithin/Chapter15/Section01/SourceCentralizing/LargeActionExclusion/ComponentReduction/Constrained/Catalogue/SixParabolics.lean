module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreePlacement
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoKernel
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
public import Theory.GroupTheory.SubgroupCoverTransport
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreePlacement

/-!
# The two ordinary A₆ source parabolics

Every original local-family member with literal A₆ two-core quotient has
a four-element Sylow interval. Its maximal members have index fifteen,
characteristic two and S₃ two-core quotients. Their two-residuals are larger
than the order-twelve model images, excluding products of A₃ blocks.

For an actual ordinary A₆ block, the marked intersection is already a
maximal member by SixGeometry. Its normalizer fixes both interval members.
They consequently satisfy all source-family clauses, and original (*)
places them in the two original intersections. Generation forces opposite
positions and literal O^{3′} escape. The faithful omega-center then gives
the source residual-centralizer identity and the A₆ catalogue alternative.
Both parabolics are also marked simultaneously under any prescribed
isomorphism of the original two-core quotient. The FF comparison and later
exchanged-source exclusion retain that same component and original prime.

Whole-core A₆ reconstruction and cubic-cover exclusion remain genuine
source obligations; they are not replaced by the block hypothesis of these
conditional geometry theorems. The S₄ local calculations reuse the existing
binary-three S₄ model through actual group isomorphisms.

Source: Aschbacher--Smith 15.1.20(2b), 15.1.22(*),(**),(2), pp.1094--1100;
the A₆ Sylow interval is I.5.4, printed p.420.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin ChapterC Representation Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Theory.SpecificGroups.SymmetricSix
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem maximal_six_model {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 A) (P : Subgroup A) (hSP : (S : Subgroup A) ≤ P)
    (hP : IsCoatom P) :
    ∃ f : P →* Matrix.PSL3Two.lineParabolicSL, Function.Surjective f ∧
      f.ker = (pCore 2 A).subgroupOf P ∧ P.index = 15 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkP : q.ker ≤ P := hk ▸ (pCore_isPGroup.le_sylow_of_normal S).trans hSP
  let B := P.map q
  have hB : IsCoatom B := isCoatom_map_of_surjective_of_ker_le q hq P hkP hP
  obtain ⟨g,_,hg⟩ := a6_coatoms_over_sylow (S.mapSurjective hq)
  have hb : Nonempty (B ≃* Equiv.Perm (Fin 4)) := by
    rcases (hg B).mp ⟨hB,map_mono hSP⟩ with he | he
    · exact ⟨(MulEquiv.subgroupCongr he).trans
        (((MulAut.conj g).subgroupMap a6DuadStabilizer).symm.trans a6DuadModelEquiv.symm)⟩
    · exact ⟨(MulEquiv.subgroupCongr he).trans
        (((MulAut.conj g).subgroupMap a6SynthemeStabilizer).symm.trans
          ResidualPairRecognition.ComponentLocals.edgeEquiv.symm)⟩
  obtain ⟨b⟩ := hb
  let c := b.trans Matrix.PSL3Two.MarkedAutomorphisms.lineEquivSymmetric.symm
  let f := c.toMonoidHom.comp (q.subgroupMap P)
  have hsurj : Function.Surjective f := c.surjective.comp (q.subgroupMap_surjective P)
  have hker : f.ker = (pCore 2 A).subgroupOf P := by
    rw [MonoidHom.ker_comp_of_injective _ _ c.injective]
    ext x
    change (⟨q x,_⟩ : B) = 1 ↔ (x : A) ∈ pCore 2 A
    rw [←hk]
    exact Subtype.ext_iff
  have hc : Nat.card B = 24 := by
    rw [Nat.card_congr b.toEquiv,Nat.card_perm]
    norm_num
  have hi : B.index = 15 := by
    have hh := B.index_mul_card
    rw [hc,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega
  exact ⟨f,hsurj,hker,(P.index_map_eq hq hkP).symm.trans hi⟩

private theorem maximal_six_quotient {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 A) (P : Subgroup A) (hSP : (S : Subgroup A) ≤ P)
    (hP : IsCoatom P) :
    P.index = 15 ∧ Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨f,hf,hk,hi⟩ := maximal_six_model e S P hSP hP
  exact ⟨hi,⟨(f.pCoreQuotientEquiv hf (hk ▸ pCore_isPGroup.comap_subtype)).trans
    (Matrix.PSL3Two.ParabolicCoreModel.coreQuotientEquiv
      Matrix.PSL3Two.MarkedAutomorphisms.lineEquivSymmetric)⟩⟩
/-- The two maximal overgroups in the full A₆ Sylow interval, together
with their literal two-core quotients and generation properties. -/
structure SixParabolicInterval (K S : Subgroup G) where
  sylow : Chapter1.IsSylowIn 2 S K
  left : Subgroup G
  right : Subgroup G
  left_le : left ≤ K
  right_le : right ≤ K
  sylow_left : S < left
  sylow_right : S < right
  left_maximal : IsCoatom (left.subgroupOf K)
  right_maximal : IsCoatom (right.subgroupOf K)
  intersection : left ⊓ right = S
  generated : left ⊔ right = K
  left_fitting : generalizedFitting left = pCore 2 left
  right_fitting : generalizedFitting right = pCore 2 right
  left_index : (left.subgroupOf K).index = 15
  right_index : (right.subgroupOf K).index = 15
  left_quotient : Nonempty ((left ⧸ pCore 2 left) ≃* Equiv.Perm (Fin 3))
  right_quotient : Nonempty ((right ⧸ pCore 2 right) ≃* Equiv.Perm (Fin 3))
  exhaustive : ∀ P : Subgroup G, S ≤ P → P ≤ K →
    P = S ∨ P = left ∨ P = right ∨ P = K

/-- Construct the whole Sylow interval on any A₆ member of the
original local family. Ambient C-componenthood is not required. -/
theorem localFamily_six_interval (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hf : generalizedFitting K = pCore 2 K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    Nonempty (SixParabolicInterval K (d.S ⊓ K)) := by
  obtain ⟨S,hS⟩ := ComponentModels.source20_sylow_intersection hK.2
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
      QuotientGroup.ker_mk']
  obtain ⟨P,Q,hP,hQ,hPQ,hI,hSP,hSQ,_,_,hall⟩ :=
    alternating_two_kernel_parabolics S q hq (hk ▸ pCore_isPGroup)
  have hgen : P ⊔ Q = ⊤ := by
    apply hP.2
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hQP : Q ≤ P := le_sup_right.trans_eq he.symm
    have hEq : Q = P := by
      by_contra hn
      exact hP.ne_top (hQ.2 P (lt_of_le_of_ne hQP hn))
    exact hPQ hEq.symm
  have hfit (D : Subgroup K) (hSD : (S : Subgroup K) ≤ D) :
      generalizedFitting D = pCore 2 D :=
    generalizedFitting_eq_pCore_of_normalized_by_pCore D hf
      ((pCore_isPGroup.le_sylow_of_normal S).trans (hSD.trans D.le_normalizer))
  obtain ⟨hPi,⟨ep⟩⟩ := maximal_six_quotient e S P hSP.le hP
  obtain ⟨hQi,⟨eq⟩⟩ := maximal_six_quotient e S Q hSQ.le hQ
  let B := P.map K.subtype
  let C := Q.map K.subtype
  let b : P ≃* B := P.equivMapOfInjective K.subtype K.subtype_injective
  let c : Q ≃* C := Q.equivMapOfInjective K.subtype K.subtype_injective
  have hBK : B.subgroupOf K = P := comap_map_eq_self_of_injective K.subtype_injective _
  have hCK : C.subgroupOf K = Q := comap_map_eq_self_of_injective K.subtype_injective _
  refine ⟨⟨⟨S,hS⟩,B,C,map_subtype_le _,map_subtype_le _,?_,?_,hBK ▸ hP,hCK ▸ hQ,
    ?_,?_,?_,?_,hBK ▸ hPi,hCK ▸ hQi,?_,?_,?_⟩⟩
  · rw [←hS]
    exact (map_lt_map_iff_of_injective K.subtype_injective).mpr hSP
  · rw [←hS]
    exact (map_lt_map_iff_of_injective K.subtype_injective).mpr hSQ
  · rw [←map_inf _ _ _ K.subtype_injective,hI,hS]
  · rw [←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map,range_subtype]
  · rw [←map_generalizedFitting_equiv b,←pCore_map_iso 2 b,hfit P hSP.le]
  · rw [←map_generalizedFitting_equiv c,←pCore_map_iso 2 c,hfit Q hSQ.le]
  · exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans ep⟩
  · exact ⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.trans eq⟩
  · intro D hSD hDK
    have hs : (S : Subgroup K) ≤ D.subgroupOf K := by
      intro x hx
      exact hSD (hS ▸ mem_map_of_mem K.subtype hx)
    rcases hall (D.subgroupOf K) hs with he | he | he | he
    · exact Or.inl (by rw [←map_subgroupOf_eq_of_le hDK,he,hS])
    · exact Or.inr (Or.inl (by rw [←map_subgroupOf_eq_of_le hDK,he]))
    · exact Or.inr (Or.inr (Or.inl (by rw [←map_subgroupOf_eq_of_le hDK,he])))
    · exact Or.inr (Or.inr (Or.inr (le_antisymm hDK (subgroupOf_eq_top.mp he))))


private theorem six_cubic_generates {K S P : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S K) (hSP : S ≤ P) (hPK : P ≤ K)
    (e : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) :
    (primeToResidual 3 P).map P.subtype ⊔ S = P := by
  obtain ⟨Q,hQ⟩ := hS.restrict hSP hPK
  have hh := congrArg (Subgroup.map P.subtype)
    (show primeToResidual 3 P ⊔ (Q : Subgroup P) = ⊤ by
      rw [←SymmetricThreeTwoCore.twoResidual_eq_primeToThree e]
      exact pResidual_sup_sylow_eq_top Q)
  simpa only [Subgroup.map_sup,hQ,←MonoidHom.range_eq_map,range_subtype] using hh

/-- Each parabolic is generated by the original Sylow intersection and
its literal O^{3′}; in particular that residual escapes the other parabolic. -/
theorem SixParabolicInterval.cubic_residuals {K S : Subgroup G}
    (i : SixParabolicInterval K S) :
    (primeToResidual 3 i.left).map i.left.subtype ⊔ S = i.left ∧
      (primeToResidual 3 i.right).map i.right.subtype ⊔ S = i.right ∧
      ¬ (primeToResidual 3 i.left).map i.left.subtype ≤ i.right ∧
      ¬ (primeToResidual 3 i.right).map i.right.subtype ≤ i.left := by
  obtain ⟨eL⟩ := i.left_quotient
  obtain ⟨eR⟩ := i.right_quotient
  have hl := six_cubic_generates i.sylow i.sylow_left.le i.left_le eL
  have hr := six_cubic_generates i.sylow i.sylow_right.le i.right_le eR
  refine ⟨hl,hr,?_,?_⟩
  · intro hh
    have hle : i.left ≤ i.right := hl ▸ sup_le hh i.sylow_right.le
    have he : i.left = S := (inf_eq_left.mpr hle).symm.trans i.intersection
    exact i.sylow_left.ne he.symm
  · intro hh
    have hle : i.right ≤ i.left := hr ▸ sup_le hh i.sylow_left.le
    have he : i.right = S := (inf_eq_right.mpr hle).symm.trans i.intersection
    exact i.sylow_right.ne he.symm

private theorem six_parabolic_residual_size
    (hf : generalizedFitting G = pCore 2 G)
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 G) (P : Subgroup G) (hSP : (S : Subgroup G) < P)
    (hP : IsCoatom P) :
    ¬ 9 ∣ Nat.card P ∧ 12 < Nat.card (pResidual 2 P) := by
  obtain ⟨f,hsurj,hker,_⟩ := maximal_six_model e S P hSP.le hP
  have h12 : Nat.card (pResidual 2 Matrix.PSL3Two.lineParabolicSL) = 12 := by
    have hh := Matrix.PSL3Two.MarkedAutomorphisms.card_line_residual
    rw [Matrix.PSL3Two.MarkedAutomorphisms.residual,
      card_map_of_injective Matrix.PSL3Two.lineParabolicSL.subtype_injective] at hh
    exact hh
  have hne : pResidual 2 Matrix.PSL3Two.lineParabolicSL ≠ ⊥ := by
    intro he
    rw [he,card_bot] at h12
    omega
  refine ⟨?_,?_⟩
  · have hc := f.ker.card_mul_index
    rw [index_ker,f.range_eq_top_of_surjective hsurj,card_top,
      Matrix.PSL3Two.card_lineParabolicSL] at hc
    obtain ⟨r,hr⟩ := (show IsPGroup 2 f.ker from hker ▸ pCore_isPGroup.comap_subtype).exists_card_eq
    rw [hr] at hc
    intro hd
    rw [←hc] at hd
    exact (by decide : ¬9 ∣ 24)
      (((by decide : Nat.Coprime 9 2).pow_right r).dvd_of_dvd_mul_left hd)
  · rw [←h12]
    exact residual_card_lt_of_characteristic_core P
      (hf ▸ centralizer_generalizedFitting_le G)
      ((pCore_isPGroup.le_sylow_of_normal S).trans hSP.le) f hsurj hker hne

/-- Characteristic two in the original member rules out A₃-product residuals
in both lifted parabolics, including their entire two-core kernels. -/
theorem SixParabolicInterval.not_aThree_products
    {K S : Subgroup G} (i : SixParabolicInterval K S)
    (hf : generalizedFitting K = pCore 2 K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    ¬ IsAThreeProduct i.left ∧ ¬ IsAThreeProduct i.right := by
  obtain ⟨Q,hQ⟩ := i.sylow
  have one (P : Subgroup G) (hPK : P ≤ K) (hSP : S < P)
      (hmax : IsCoatom (P.subgroupOf K)) : ¬ IsAThreeProduct P := by
    have hSP' : (Q : Subgroup K) < P.subgroupOf K := by
      apply (map_lt_map_iff_of_injective K.subtype_injective).mp
      rw [hQ,map_subgroupOf_eq_of_le hPK]
      exact hSP
    obtain ⟨h9,h12⟩ := six_parabolic_residual_size hf e Q (P.subgroupOf K) hSP' hmax
    let t : P.subgroupOf K ≃* P := subgroupOfEquivOfLe hPK
    have hc : Nat.card (pResidual 2 (P.subgroupOf K)) = Nat.card (pResidual 2 P) := by
      have hh := congrArg (fun X : Subgroup P => Nat.card X)
        (map_pResidual_of_surjective 2 t.toMonoidHom t.surjective)
      rw [card_map_of_injective t.injective] at hh
      exact hh
    rw [hc] at h12
    rw [Nat.card_congr t.toEquiv] at h9
    intro hA
    have hh := aThreeProduct_residual_card_le P h9 hA
    omega
  exact ⟨one i.left i.left_le i.sylow_left i.left_maximal,
    one i.right i.right_le i.sylow_right i.right_maximal⟩

omit [Finite G] in
private theorem six_interval_other_fixed
    {K S B P Q : Subgroup G} (i : SixParabolicInterval K S)
    (hP : P = i.left ∨ P = i.right) (hQ : Q = i.left ∨ Q = i.right)
    (hne : P ≠ Q) (hBK : B ≤ normalizer (K : Set G))
    (hBS : B ≤ normalizer (S : Set G)) (hBP : B ≤ normalizer (P : Set G)) :
    B ≤ normalizer (Q : Set G) := by
  have hSQ : S < Q := by rcases hQ with rfl | rfl; exact i.sylow_left; exact i.sylow_right
  have hQK : Q < K := by
    have hle : Q ≤ K := by rcases hQ with rfl | rfl; exact i.left_le; exact i.right_le
    refine lt_of_le_of_ne hle ?_
    intro he
    have ht : Q.subgroupOf K = ⊤ := he ▸ subgroupOf_self _
    rcases hQ with he | he
    · exact i.left_maximal.ne_top (he ▸ ht)
    · exact i.right_maximal.ne_top (he ▸ ht)
  intro g hg
  let a := (MulAut.conj g).toMonoidHom
  have hKfix : K.map a = K := mem_normalizer_iff_map_conj_eq.mp (hBK hg)
  have hSfix : S.map a = S := mem_normalizer_iff_map_conj_eq.mp (hBS hg)
  have hPfix : P.map a = P := mem_normalizer_iff_map_conj_eq.mp (hBP hg)
  have hSmap : S < Q.map a := by
    rw [←hSfix]
    exact (map_lt_map_iff_of_injective (MulAut.conj g).injective).mpr hSQ
  have hmapK : Q.map a < K := by
    rw [←hKfix]
    exact (map_lt_map_iff_of_injective (MulAut.conj g).injective).mpr hQK
  have hnot : Q.map a ≠ P := by
    intro he
    rw [←hPfix] at he
    exact hne (map_injective (MulAut.conj g).injective he).symm
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases i.exhaustive (Q.map a) hSmap.le hmapK.le with he | he | he | he
  · exact (hSmap.ne he.symm).elim
  · rcases hQ with hQ | hQ
    · exact he.trans hQ.symm
    · rcases hP with hP | hP
      · exact (hnot (he.trans hP.symm)).elim
      · exact (hne (hP.trans hQ.symm)).elim
  · rcases hQ with hQ | hQ
    · rcases hP with hP | hP
      · exact (hne (hP.trans hQ.symm)).elim
      · exact (hnot (he.trans hP.symm)).elim
    · exact he.trans hQ.symm
  · exact (hmapK.ne he).elim

/-- Fixing the marked maximal member fixes the other member of the
six-point interval. The acting group is the literal N_S(L). -/
theorem SixParabolicInterval.normalized_of_marked_ne_sylow
    {d : CaseIComponentData T M Mc V} (i : SixParabolicInterval d.L d.SL)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hm : d.ML = d.SL ∨ d.ML = i.left ∨ d.ML = i.right)
    (hne : d.ML ≠ d.SL) :
    d.sylowNormalizer ≤ normalizer (i.left : Set G) ∧
      d.sylowNormalizer ≤ normalizer (i.right : Set G) := by
  have hSM : d.S ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨d.S_le_G1 hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)⟩
  have hNK : d.sylowNormalizer ≤ normalizer (d.L : Set G) := inf_le_right
  have hNS : d.sylowNormalizer ≤ normalizer (d.SL : Set G) :=
    (inf_le_inf_right _ d.S.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hNM : d.sylowNormalizer ≤ normalizer (d.ML : Set G) :=
    (inf_le_inf_right _ (hSM.trans d.MZ.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hpq : i.left ≠ i.right := by
    intro he
    have hh := i.intersection
    rw [he,inf_idem] at hh
    exact i.sylow_right.ne hh.symm
  rcases hm.resolve_left hne with hm | hm
  · have hnL : d.sylowNormalizer ≤ normalizer (i.left : Set G) := hm ▸ hNM
    exact ⟨hnL,six_interval_other_fixed i (Or.inl rfl) (Or.inr rfl) hpq hNK hNS hnL⟩
  · have hnR : d.sylowNormalizer ≤ normalizer (i.right : Set G) := hm ▸ hNM
    exact ⟨six_interval_other_fixed i (Or.inr rfl) (Or.inl rfl) hpq.symm hNK hNS hnR,hnR⟩


/-- Both original intersections lie in the proper part of the A₆ Sylow
interval, without imposing ambient C-componenthood on the member. -/
theorem localFamily_six_intersections (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S) (hout : ¬ K ≤ d.MZ)
    (i : SixParabolicInterval K (d.S ⊓ K)) :
    (d.MZ ⊓ K = d.S ⊓ K ∨ d.MZ ⊓ K = i.left ∨ d.MZ ⊓ K = i.right) ∧
      (M ⊓ K = d.S ⊓ K ∨ M ⊓ K = i.left ∨ M ⊓ K = i.right) := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hSMZ : d.S ≤ d.MZ := by
    refine le_inf d.S_le_G1 ?_
    intro x hx
    exact hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)
  have classify (A : Subgroup G) (hSA : d.S ≤ A) (hne : ¬ K ≤ A) :
      A ⊓ K = d.S ⊓ K ∨ A ⊓ K = i.left ∨ A ⊓ K = i.right := by
    rcases i.exhaustive (A ⊓ K) (inf_le_inf_right _ hSA) inf_le_right with he | he | he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
    · exact (hne (he ▸ inf_le_left)).elim
  exact ⟨classify d.MZ hSMZ hout,classify M (d.S_le_T.trans hM.1.2)
    (d.localFamily_not_le_M hG hempty hM hu hK hout)⟩


/-- In the ordinary A₆ block, both source intersections are the opposite
maximal members of the literal Sylow interval, with full source membership. -/
theorem PreExclusionSource.constrained_six_source_parabolics
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hb : IsAlternatingBlock d.L 6)
    (e : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 6)) :
    ∃ i : SixParabolicInterval d.L d.SL,
      d.IsSourceParabolic i.left ∧ d.IsSourceParabolic i.right ∧
        ((d.ML = i.left ∧ M ⊓ d.L = i.right) ∨
          (d.ML = i.right ∧ M ⊓ d.L = i.left)) := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  obtain ⟨i⟩ := d.localFamily_six_interval hK hb.2.1.fitting e
  have ⟨hm,hn⟩ := d.localFamily_six_intersections hG hempty hM hu hK d.L_not_le_MZ i
  change d.ML = d.SL ∨ d.ML = i.left ∨ d.ML = i.right at hm
  have hmax := (s.constrained_six_centralizing (h := h) hG hM.1.2 hu hfull hb).2
  have hms : d.ML ≠ d.SL := by
    intro he
    have hlt : d.ML.subgroupOf d.L < i.left.subgroupOf d.L := by
      apply (map_lt_map_iff_of_injective d.L.subtype_injective).mp
      rw [map_subgroupOf_eq_of_le (show d.ML ≤ d.L from inf_le_right),
        map_subgroupOf_eq_of_le i.left_le,he]
      exact i.sylow_left
    exact i.left_maximal.ne_top (hmax.2 _ hlt)
  have hnorm := i.normalized_of_marked_ne_sylow hu hm hms
  have hnot := i.not_aThree_products hb.2.1.fitting e
  have htwo : IsPGroup 2 d.sylowNormalizer :=
    T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)
  have hleft : d.IsSourceParabolic i.left := by
    obtain ⟨eP⟩ := i.left_quotient
    exact ⟨i.left_le,hnorm.1,i.left_fitting,Or.inl
      (NormalSymmetricThreeExtension.normalized_join _ _ hnorm.1 eP htwo),hnot.1⟩
  have hright : d.IsSourceParabolic i.right := by
    obtain ⟨eP⟩ := i.right_quotient
    exact ⟨i.right_le,hnorm.2,i.right_fitting,Or.inl
      (NormalSymmetricThreeExtension.normalized_join _ _ hnorm.2 eP htwo),hnot.2⟩
  have hplace := s.parabolic_placement_of_constrained (h := h) hG hempty hM hJ hu hb.2.1.fitting
  have hgen : (M ⊓ d.L) ⊔ d.ML = d.L := by
    apply le_antisymm (sup_le inf_le_right inf_le_right)
    calc
      d.L = i.left ⊔ i.right := i.generated.symm
      _ ≤ (M ⊓ d.L) ⊔ d.ML := sup_le
        ((hplace i.left hleft).elim (fun h => h.trans le_sup_left) (fun h => h.trans le_sup_right))
        ((hplace i.right hright).elim (fun h => h.trans le_sup_left) (fun h => h.trans le_sup_right))
  have hSML : d.SL ≤ d.ML := by
    rcases hm.resolve_left hms with he | he
    · exact he.symm ▸ i.sylow_left.le
    · exact he.symm ▸ i.sylow_right.le
  have hns : M ⊓ d.L ≠ d.SL := by
    intro he
    rw [he,sup_eq_right.mpr hSML] at hgen
    exact d.L_not_le_MZ (hgen ▸ inf_le_left)
  have hne : d.ML ≠ M ⊓ d.L := by
    intro he
    rw [←he,sup_idem] at hgen
    exact d.L_not_le_MZ (hgen ▸ inf_le_left)
  refine ⟨i,hleft,hright,?_⟩
  rcases hm.resolve_left hms with hm | hm <;>
    rcases hn.resolve_left hns with hn | hn
  · exact (hne (hm.trans hn.symm)).elim
  · exact Or.inl ⟨hm,hn⟩
  · exact Or.inr ⟨hm,hn⟩
  · exact (hne (hm.trans hn.symm)).elim

/-- The whole ordinary A₆ block has both literal parabolics and centralizer
clauses. The block hypothesis is retained until whole-core reconstruction. -/
theorem PreExclusionSource.constrained_six_of_block
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hb : IsAlternatingBlock d.L 6) :
    Nat.card d.plusOmega = 2 ∧
      d.ML = d.L ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom (d.ML.subgroupOf d.L) ∧ IsCoatom ((M ⊓ d.L).subgroupOf d.L) ∧
      d.ML ≠ M ⊓ d.L ∧ (M ⊓ d.L) ⊔ d.ML = d.L ∧
      d.IsSourceParabolic d.ML ∧ d.IsSourceParabolic (M ⊓ d.L) ∧
      ((d.ML.subgroupOf d.L).index = 15 ∧ ((M ⊓ d.L).subgroupOf d.L).index = 15) ∧
      d.ConstrainedCentralizerIdentity ∧ d.ConstrainedAlternatives := by
  obtain ⟨ρ,⟨m⟩,_⟩ := hb.2.2
  obtain ⟨i,hleft,hright,hpos⟩ := s.constrained_six_source_parabolics (h := h)
    hG hempty hM hJ hu hfull hb m.quotientIso
  have hc := s.constrained_six_plusOmega_card (h := h) hG hM.1.2 hu hb
  have hseed := s.constrained_six_centralizing (h := h) hG hM.1.2 hu hfull hb
  have hres := i.cubic_residuals
  have hgeom : IsCoatom ((M ⊓ d.L).subgroupOf d.L) ∧
      d.ML ≠ M ⊓ d.L ∧ (M ⊓ d.L) ⊔ d.ML = d.L ∧
      d.IsSourceParabolic d.ML ∧ d.IsSourceParabolic (M ⊓ d.L) ∧
      ((d.ML.subgroupOf d.L).index = 15 ∧ ((M ⊓ d.L).subgroupOf d.L).index = 15) ∧
      ¬ d.localThreeResidual ≤ d.ML := by
    have hne : i.left ≠ i.right := by
      intro he
      have hh := i.intersection
      rw [he,inf_idem] at hh
      exact i.sylow_right.ne hh.symm
    rcases hpos with ⟨hm,hn⟩ | ⟨hm,hn⟩
    · refine ⟨hn.symm ▸ i.right_maximal,?_,?_,hm.symm ▸ hleft,hn.symm ▸ hright,
        ⟨hm.symm ▸ i.left_index,hn.symm ▸ i.right_index⟩,?_⟩
      · rw [hm,hn]; exact hne
      · rw [hm,hn,sup_comm,i.generated]
      · change ¬ (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ≤ d.ML
        rw [hn,hm]
        exact hres.2.2.2
    · refine ⟨hn.symm ▸ i.left_maximal,?_,?_,hm.symm ▸ hright,hn.symm ▸ hleft,
        ⟨hm.symm ▸ i.right_index,hn.symm ▸ i.left_index⟩,?_⟩
      · rw [hm,hn]; exact hne.symm
      · rw [hm,hn,i.generated]
      · change ¬ (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ≤ d.ML
        rw [hn,hm]
        exact hres.2.2.1
  have hcent := s.source_residual_centralizer (h := h) hG hfull hM.1.2 hu hc hgeom.2.2.2.2.2.2
  exact ⟨hc,hseed.1,hseed.2,hgeom.1,hgeom.2.1,hgeom.2.2.1,
    hgeom.2.2.2.1,hgeom.2.2.2.2.1,hgeom.2.2.2.2.2.1,hcent,.alternatingSix hb hcent⟩

/-- Both original intersections are opposite parabolics under the prescribed
isomorphism of the literal two-core quotient. The same conjugator marks both. -/
theorem PreExclusionSource.constrained_six_marked_parabolics
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M) (hb : IsAlternatingBlock d.L 6)
    (e : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 6)) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
    ∃ g : alternatingGroup (Fin 6),
      (((d.ML.subgroupOf d.L).map q =
          (MulAut.conj g).mapSubgroup a6DuadStabilizer ∧
        ((M ⊓ d.L).subgroupOf d.L).map q =
          (MulAut.conj g).mapSubgroup a6SynthemeStabilizer) ∨
       ((d.ML.subgroupOf d.L).map q =
          (MulAut.conj g).mapSubgroup a6SynthemeStabilizer ∧
        ((M ⊓ d.L).subgroupOf d.L).map q =
          (MulAut.conj g).mapSubgroup a6DuadStabilizer)) := by
  intro q
  obtain ⟨_,_,hmax,hmax',hne,_,_,_,_,_,_⟩ :=
    s.constrained_six_of_block (h := h) hG hempty hM hJ hu hfull hb
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 d.L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := s.component_sylow
  have hloc := s.local_intersections (h := h) hG hu hM.1.2
  have hPM : (P : Subgroup d.L) ≤ d.ML.subgroupOf d.L := by
    intro x hx
    exact hloc.2.1 (hP ▸ mem_map_of_mem d.L.subtype hx)
  have hPN : (P : Subgroup d.L) ≤ (M ⊓ d.L).subgroupOf d.L := by
    intro x hx
    exact hloc.2.2.2.1 (hP ▸ mem_map_of_mem d.L.subtype hx)
  have hkM : q.ker ≤ d.ML.subgroupOf d.L := hk ▸ (pCore_isPGroup.le_sylow_of_normal P).trans hPM
  have hkN : q.ker ≤ (M ⊓ d.L).subgroupOf d.L := hk ▸ (pCore_isPGroup.le_sylow_of_normal P).trans hPN
  have hMmax := isCoatom_map_of_surjective_of_ker_le q hq _ hkM hmax
  have hNmax := isCoatom_map_of_surjective_of_ker_le q hq _ hkN hmax'
  have himne : (d.ML.subgroupOf d.L).map q ≠ ((M ⊓ d.L).subgroupOf d.L).map q := by
    intro he
    have hh := congrArg (Subgroup.comap q) he
    rw [comap_map_eq_self hkM,comap_map_eq_self hkN] at hh
    apply hne
    have hh' := congrArg (Subgroup.map d.L.subtype) hh
    simpa only [map_subgroupOf_eq_of_le (show d.ML ≤ d.L from inf_le_right),
      map_subgroupOf_eq_of_le (show M ⊓ d.L ≤ d.L from inf_le_right)] using hh'
  obtain ⟨g,_,hg⟩ := a6_coatoms_over_sylow (P.mapSurjective hq)
  refine ⟨g,?_⟩
  rcases (hg _).mp ⟨hMmax,map_mono hPM⟩ with hm | hm <;>
    rcases (hg _).mp ⟨hNmax,map_mono hPN⟩ with hn | hn
  · exact (himne (hm.trans hn.symm)).elim
  · exact Or.inl ⟨hm,hn⟩
  · exact Or.inr ⟨hm,hn⟩
  · exact (himne (hm.trans hn.symm)).elim

/-- The FF marking is preserved on the entire ordinary A₆ two-core quotient.
It is not replaced by an unrelated natural-model isomorphism. -/
theorem PreExclusionSource.constrained_six_core_marking
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hb : IsAlternatingBlock d.L 6)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 6)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 6),
      ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hb.2.1.fitting
  obtain ⟨ρ,⟨m⟩,_⟩ := hb.2.2
  have hi : Function.Bijective a.coreToImage := a.coreToImage_surjective.bijective_of_nat_card_le
    (by rw [Nat.card_congr m.quotientIso.toEquiv,Nat.card_congr e.toEquiv])
  let t := (MulEquiv.ofBijective a.coreToImage hi).trans e
  exact ⟨t,fun k => congrArg e (a.coreToImage_mk k)⟩

/-- The later exchanged-source obstruction applies to this same original
component after its ordinary A₆ centralizer identity has been constructed. -/
theorem ExchangedSource.not_constrained_six_block_of_preExclusion
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (x : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M) : ¬ IsAlternatingBlock d.L 6 := by
  intro hb
  obtain ⟨_,_,_,_,_,_,_,_,_,hc,_⟩ :=
    s.constrained_six_of_block (h := h) hG hempty hM hJ hu hfull hb
  exact x.no_constrained_a6_centralizers hG hM.1.2 h hb hc
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
