module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryParabolicEscape
public import Theory.SpecificGroups.SymmetricFive.SylowOvergroup
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# The canonical S5 parabolic in the original invariant cover

A Sylow two-subgroup of S5 fixes exactly one point. Every proper overgroup
of that Sylow fixes the same point, so its S4 stabilizer is the unique
maximal proper Sylow overgroup. Its literal two-core quotient is S3.
Pulling back through the original two-core quotient of the invariant cover
K = P O2(N) gives a canonical parabolic B containing T ∩ K. Uniqueness
makes B invariant under N_G(K) ∩ N_G(T). Adjoining T retains the S3 quotient
and gives the exact index |BT:T| = 3.

The final theorems apply this construction to the original W/Z_S action,
retaining its factor, invariant cover and quotient maps. The source cubic
D_L need not normalize T; its invariance of B is not asserted here. That
step, escape of B from M, the L3(2) row and the amalgam contradiction, as
well as initial 6.1.4–5 and the remaining geometry, stay with
qt-d-1222-rankone-recognition-natural for unconditional 6.1.27 assembly.

Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveParabolic
local notation "S5" => Equiv.Perm (Fin 5)
local notation "S3" => Equiv.Perm (Fin 3)
private theorem card_stabilizer (i : Fin 5) :
    Nat.card (MulAction.stabilizer S5 i) = 24 := by
  have hi : (MulAction.stabilizer S5 i).index = 5 := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
    simp
  have hh := (MulAction.stabilizer S5 i).card_mul_index
  rw [hi, Nat.card_perm, show Nat.card (Fin 5) = 5 from by simp] at hh
  norm_num [Nat.factorial] at hh ⊢
  omega

private def point_equiv (i : Fin 5) :
    MulAction.stabilizer S5 i ≃* Equiv.Perm (Fin 4) := by
  classical
  let X := {x : Fin 5 // x ≠ i}
  let f : MulAction.stabilizer S5 i →* Equiv.Perm X := {
    toFun g := g.val.subtypePerm (fun x => by
      have hg : g.val i = i := g.property
      simpa only [hg] using g.val.injective.ne_iff (x := x) (y := i))
    map_one' := by ext x; rfl
    map_mul' := by intros; ext x; rfl }
  have hfi : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x = i
    · subst x; exact g.property.trans h.property.symm
    · exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x,hx⟩)
  have hX : Fintype.card X = 4 := by
    simp [X,Fintype.card_subtype_compl]
  have hc : Nat.card (MulAction.stabilizer S5 i) = Nat.card (Equiv.Perm X) := by
    rw [card_stabilizer,Nat.card_eq_fintype_card,Fintype.card_perm,hX]
    rfl
  let e := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi,hc⟩)
  let b : X ≃ Fin 4 := Fintype.equivFinOfCardEq hX
  exact e.trans (Equiv.permCongrHom b)

private def point_quotient (i : Fin 5) :
    ((MulAction.stabilizer S5 i) ⧸ pCore 2 (MulAction.stabilizer S5 i)) ≃* S3 := by
  let e := point_equiv i
  let q := Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom
  let f := q.comp e.toMonoidHom
  have hf : Function.Surjective f :=
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom_surjective.comp e.surjective
  have hk : IsPGroup 2 f.ker := by
    exact (IsElementaryAbelian.isPGroup 2 q.ker).comap_of_injective e.toMonoidHom e.injective
  exact (QuotientGroup.quotientMulEquivOfEq
    (ker_eq_twoCore_of_surjective_perm_three f hf hk).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)

private theorem fixed_point_unique (S : Sylow 2 S5) (i j : Fin 5)
    (hi : (S : Subgroup S5) ≤ MulAction.stabilizer S5 i)
    (hj : (S : Subgroup S5) ≤ MulAction.stabilizer S5 j) : i = j := by
  classical
  by_contra hne
  have hc : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity,Nat.card_perm,show Nat.card (Fin 5) = 5 from by simp]
    decide +kernel
  have hh : ∀ i j : Fin 5, i ≠ j →
      (Finset.univ.filter (fun g : S5 => g i = i ∧ g j = j)).card = 6 := by
    decide +kernel
  have hsmall : Nat.card (MulAction.stabilizer S5 i ⊓ MulAction.stabilizer S5 j : Subgroup S5) = 6 := by
    let : DecidablePred (· ∈ (MulAction.stabilizer S5 i ⊓ MulAction.stabilizer S5 j : Subgroup S5)) :=
      fun g => inferInstanceAs (Decidable (g i = i ∧ g j = j))
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hh i j hne
  have hd := card_dvd_of_le (le_inf hi hj)
  rw [hc,hsmall] at hd
  norm_num at hd

/-- The unique maximal proper Sylow overgroup in S5, with its actual S3 quotient. -/
private theorem model_parabolic (S : Sylow 2 S5) :
    ∃ B : Subgroup S5, (S : Subgroup S5) ≤ B ∧ B ≠ ⊤ ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* S3) ∧
      (∀ C : Subgroup S5, (S : Subgroup S5) ≤ C → C ≠ ⊤ → C ≤ B) := by
  obtain ⟨i,hi⟩ := S.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) (by norm_num)
  have hSB : (S : Subgroup S5) ≤ MulAction.stabilizer S5 i := fun g hg => hi ⟨g,hg⟩
  refine ⟨MulAction.stabilizer S5 i,hSB,?_,⟨point_quotient i⟩,?_⟩
  · intro he
    have hc := card_stabilizer i
    rw [he,card_top,Nat.card_perm,show Nat.card (Fin 5) = 5 from by simp] at hc
    norm_num [Nat.factorial] at hc
  · intro C hSC hC
    obtain ⟨j,hj⟩ := Theory.SpecificGroups.SymmetricFive.SylowOvergroup.exists_le_point_stabilizer S C hSC hC
    rw [fixed_point_unique S i j hSB (hSC.trans hj)]
    exact hj

private theorem quotient_parabolic {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (e : (A ⧸ pCore 2 A) ≃* S5) :
    ∃ B : Subgroup A, (S : Subgroup A) ≤ B ∧ B ≠ ⊤ ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* S3) ∧
      (∀ C : Subgroup A, (S : Subgroup A) ≤ C → C ≠ ⊤ → C ≤ B) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkS : q.ker ≤ (S : Subgroup A) := hk ▸ pCore_isPGroup.le_sylow_of_normal S
  obtain ⟨D,hSD,hD,⟨eD⟩,hmax⟩ := model_parabolic (S.mapSurjective hq)
  let B := D.comap q
  have hBq : B.map q = D := map_comap_eq_self (by rw [q.range_eq_top_of_surjective hq]; exact le_top)
  let f : B →* D := (MulEquiv.subgroupCongr hBq).toMonoidHom.comp (q.subgroupMap B)
  have hf : Function.Surjective f := (MulEquiv.subgroupCongr hBq).surjective.comp
    (q.subgroupMap_surjective B)
  have hfk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hBq).injective,
      ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  refine ⟨B,map_le_iff_le_comap.mp hSD,?_,⟨(f.pCoreQuotientEquiv hf hfk).trans eD⟩,?_⟩
  · intro he
    apply hD
    rw [←hBq,he,map_top_of_surjective q hq]
  · intro C hSC hC
    apply map_le_iff_le_comap.mp
    apply hmax _ (map_mono hSC)
    intro he
    apply hC
    have hh := congrArg (comap q) he
    rwa [comap_map_eq_self (hkS.trans hSC),comap_top] at hh

/-- The S5 quotient constructs a canonical invariant parabolic in the
original cover. Its Sylow extension has the actual S3 quotient and index three. -/
private theorem invariant_parabolic {A : Type*} [Group A] [Finite A]
    (T : Sylow 2 A) (K : Subgroup A)
    (hTK : (T : Subgroup A) ≤ normalizer (K : Set A))
    (e : (K ⧸ pCore 2 K) ≃* S5) :
    ∃ B : Subgroup A, B < K ∧ (T : Subgroup A) ⊓ K ≤ B ∧
      normalizer (K : Set A) ⊓ normalizer (T : Set A) ≤ normalizer (B : Set A) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* S3) ∧
      (∀ C : Subgroup A, (T : Subgroup A) ⊓ K ≤ C → C < K → C ≤ B) ∧
      Nonempty (((B ⊔ (T : Subgroup A) : Subgroup A) ⧸
        pCore 2 (B ⊔ (T : Subgroup A) : Subgroup A)) ≃* S3) ∧
      (T : Subgroup A).relIndex (B ⊔ (T : Subgroup A)) = 3 := by
  obtain ⟨S,hS⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K hTK
  obtain ⟨D,hSD,hD,⟨eD⟩,hmax⟩ := quotient_parabolic S e
  let B := D.map K.subtype
  have hBK : B ≤ K := map_subtype_le _
  have hBne : B ≠ K := by
    intro he
    apply hD
    apply map_injective K.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype]
    exact he
  have hSB : (T : Subgroup A) ⊓ K ≤ B := by
    have hh := map_mono hSD (f := K.subtype)
    rwa [hS,subgroupOf_map_subtype] at hh
  have hmaxB (C : Subgroup A) (hSC : (T : Subgroup A) ⊓ K ≤ C) (hC : C < K) : C ≤ B := by
    have hc : C.subgroupOf K ≤ D := by
      apply hmax
      · rw [hS]
        intro x hx
        exact hSC ⟨hx,x.property⟩
      · intro hc
        apply hC.ne
        have hh := congrArg (map K.subtype) hc
        rwa [map_subgroupOf_eq_of_le hC.le,←MonoidHom.range_eq_map,range_subtype] at hh
    have hh := map_mono hc (f := K.subtype)
    rwa [map_subgroupOf_eq_of_le hC.le] at hh
  have hnB : normalizer (K : Set A) ⊓ normalizer (T : Set A) ≤ normalizer (B : Set A) := by
    intro a ha
    let f := (MulAut.conj a).toMonoidHom
    have hf := (MulAut.conj a).injective
    have hK : K.map f = K := mem_normalizer_iff_map_conj_eq.mp ha.1
    have hT : (T : Subgroup A).map f = (T : Subgroup A) := mem_normalizer_iff_map_conj_eq.mp ha.2
    have hBC : B.map f ≤ K := hK ▸ map_mono hBK
    have hBClt : B.map f < K := lt_of_le_of_ne hBC (fun he =>
      hBne ((map_injective hf) (he.trans hK.symm)))
    have hSBC : (T : Subgroup A) ⊓ K ≤ B.map f := by
      have hh := map_mono hSB (f := f)
      rwa [Subgroup.map_inf _ _ _ hf,hK,hT] at hh
    have hle := hmaxB _ hSBC hBClt
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : B.map f = B := eq_of_le_of_card_ge hle
      (card_map_of_injective (K := B) (f := f) hf).ge
    exact he
  let eB := D.equivMapOfInjective K.subtype K.subtype_injective
  let eBQ : (B ⧸ pCore 2 B) ≃* S3 :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).symm.trans eD
  have hTB : (T : Subgroup A) ≤ normalizer (B : Set A) :=
    (le_inf hTK (T : Subgroup A).le_normalizer).trans hnB
  let H := B ⊔ (T : Subgroup A)
  have hBH : B ≤ H := le_sup_left
  have hTH : (T : Subgroup A) ≤ H := le_sup_right
  let D' := B.subgroupOf H
  let S' := (T : Subgroup A).subgroupOf H
  let : D'.Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hTB)
  have hgen : D' ⊔ S' = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype]
  let eD' := subgroupOfEquivOfLe hBH
  obtain ⟨eH⟩ := NormalSymmetricThree.quotient_symmetricThree_of_normal_twoGroup_supplement
    D' S' ((QuotientGroup.congr _ _ eD' (pCore_map_iso 2 eD')).trans eBQ)
    T.isPGroup'.comap_subtype hgen
  exact ⟨B,lt_of_le_of_ne hBK hBne,hSB,hnB,⟨eBQ⟩,hmaxB,⟨eH⟩,
    SymmetricThreeTwoCore.sylow_index_three eH (T.subtype hTH)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveParabolic

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Subgroup Theory.GroupTheory
/-- The canonical S5 parabolic in the invariant cover, over the original
Sylow intersection. Cubic invariance and escape are separate source obligations. -/
@[expose] def NaturalFiveParabolicData {G : Type*} [Group G]
    (T : Sylow 2 G) (P N : Subgroup G) : Prop :=
  Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5)) →
    let K := P ⊔ N.pCoreIn 2
    ∃ B : Subgroup G, B < K ∧ (T : Subgroup G) ⊓ K ≤ B ∧
      N ⊓ normalizer (T : Set G) ≤ normalizer (B : Set G) ∧
      (T : Subgroup G) ≤ normalizer (B : Set G) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
      (∀ C : Subgroup G, (T : Subgroup G) ⊓ K ≤ C → C < K → C ≤ B) ∧
      Nonempty (((B ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      (T : Subgroup G).relIndex (B ⊔ (T : Subgroup G)) = 3

/-- Apply the canonical parabolic construction to the very same invariant cover
and action witness. No normalization of the smaller original P is assumed. -/
theorem natural_five_parabolic_of_invariant_cover
    {G X : Type*} [Group G] [Finite G] [Group X]
    (T : Sylow 2 G) (P I N : Subgroup G) (σ : I →* MulAut X) (hPI : P ≤ I)
    (hc : NaturalInvariantCoverData T P I N σ hPI) :
    NaturalFiveParabolicData T P N := by
  rintro ⟨eP⟩
  obtain ⟨hKI,hNK,hTK,hcore,⟨eK⟩,hrange,hker,hthree⟩ := hc
  obtain ⟨B,hBK,hSB,hNB,eB,hmax,eBT,hi⟩ :=
    NaturalFiveParabolic.invariant_parabolic T _ hTK (eK.trans eP)
  exact ⟨B,hBK,hSB,(inf_le_inf hNK le_rfl).trans hNB,
    (le_inf hTK (T : Subgroup G).le_normalizer).trans hNB,eB,hmax,eBT,hi⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The original W/Z_S witness, with the canonical S5 parabolic constructed
in its invariant cover and the exact Sylow index three. -/
theorem exists_ambient_five_parabolic
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N M ∧
            NaturalFiveParabolicData T P N := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape⟩ :=
    d.exists_ambient_escaping_cover h hnat hE hs hNS hab
  let := hZ
  let := hX
  exact ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,
    natural_five_parabolic_of_invariant_cover T _ _ _ σ hPI hcover⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
