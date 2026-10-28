module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.UnitaryLocal.Construction
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleRadicalTwoExtension
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.SpecificGroups.SU3.FixedCentralizerRigidity
public import Theory.ElementaryAbelian.BinaryKernelRankDrop

/-!
# The radical quotient of the unitary local candidate

The candidate `C_L(t) τ` has a normal simple subgroup, and its quotient by
that subgroup is a two-group.  We retain the intrinsic quotient maps here:
the solvable radical is a two-group, the image of the fixed subgroup is the
single component of the radical quotient, and the local tau orbit is that
component.  The involution `t` is central in the candidate and belongs to its
radical, so the ambient `f+1` rank bound drops to `f` in the quotient.

Source: Aschbacher--Smith E.1.1--6 and E.1.14(1), pp.209--211, 214.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.Converse Theory.GroupTheory
open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G] [Finite G]

private theorem localCandidate_eCase
    (L : Subgroup G) [L.Normal] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSU3Model f) (hC : centralizer (L : Set G) = ⊥)
    (hO : pCore 2 G = ⊥) (S : Sylow 2 G) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hAS : A ≤ (S : Subgroup G))
    (hr : f < Group.rank A)
    {t : G} (htA : t ∈ A) (htL : t ∉ L) (ht2 : t ^ 2 = 1)
    (P : Sylow 2 (fixedCore L t))
    (_hPA : (P : Subgroup (fixedCore L t)).map (fixedCore L t).subtype ≤ A) :
    ECaseComponent (S : Subgroup G) A (localCandidate L (S : Subgroup G) A t) ∧
      ∃ C : Subgroup (localCandidate L (S : Subgroup G) A t ⧸
        solvableRadical (localCandidate L (S : Subgroup G) A t)),
        C.Normal ∧
        IsComponent (localCandidate L (S : Subgroup G) A t ⧸
          solvableRadical (localCandidate L (S : Subgroup G) A t)) C ∧
        componentLayer (localCandidate L (S : Subgroup G) A t ⧸
          solvableRadical (localCandidate L (S : Subgroup G) A t)) = C ∧
        componentLayer (localCandidate L (S : Subgroup G) A t ⧸
          solvableRadical (localCandidate L (S : Subgroup G) A t)) =
          conjugateJoin
            ((tau ((S : Subgroup G).subgroupOf (localCandidate L (S : Subgroup G) A t))
              (A.subgroupOf (localCandidate L (S : Subgroup G) A t))).map
                (QuotientGroup.mk' (solvableRadical (localCandidate L (S : Subgroup G) A t)))) C ∧
        C = ⁅C, (A.subgroupOf (localCandidate L (S : Subgroup G) A t)).map
          (QuotientGroup.mk' (solvableRadical (localCandidate L (S : Subgroup G) A t)))⁆ := by
  let N₀ := fixedCore L t
  let D₀ := tau (S : Subgroup G) A
  let K := localCandidate L (S : Subgroup G) A t
  let N := N₀.subgroupOf K
  let D := D₀.subgroupOf K
  have hAD : A ≤ D₀ := by
    let : IsElementaryAbelian 2 A := hA
    exact le_centralizerModulo_of_isMulCommutative hAS
  have hAK : A ≤ K := hAD.trans le_sup_right
  have hND : N ⊔ D = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show N₀ ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show D₀ ≤ K from le_sup_right)]
    have htop : (⊤ : Subgroup K).map K.subtype = K := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    rw [htop]
    rfl
  have hDN : D₀ ≤ normalizer (N₀ : Set G) :=
    tau_normalizes_fixedCore L (S : Subgroup G) A hO htA
  have hKN : K ≤ normalizer (N₀ : Set G) :=
    sup_le (show N₀ ≤ normalizer (N₀ : Set G) from le_normalizer) hDN
  let : N.Normal := normal_subgroupOf_of_le_normalizer hKN
  obtain ⟨hNsimple₀, hNnoncomm₀⟩ := fixedCore_simple_nonabelian L hf e hC t htL ht2
  let eN : N ≃* N₀ := subgroupOfEquivOfLe (show N₀ ≤ K from le_sup_left)
  let : IsSimpleGroup N := (MulEquiv.isSimpleGroup_congr eN).mpr hNsimple₀
  have hNnoncomm : ¬ IsMulCommutative N := by
    intro h
    apply hNnoncomm₀
    exact isMulCommutative_iff.mpr (fun x y => by
      apply eN.symm.injective
      exact (isMulCommutative_iff.mp h) (eN.symm x) (eN.symm y))
  let : Group.IsPerfect N := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator N)
      inferInstance).resolve_left (fun h => hNnoncomm ((commutator_eq_bot_iff N).mp h))⟩
  have hNcenter : center N = ⊥ := by
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center N) inferInstance).resolve_right
      (fun h => hNnoncomm (center_eq_top_iff.mp h))
  let : IsQuasisimple N := ⟨
    ((QuotientGroup.quotientMulEquivOfEq hNcenter).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hDtwo : IsPGroup 2 D₀ :=
    S.isPGroup'.to_le (tau_le (S : Subgroup G) A)
  have hquot : IsPGroup 2 (K ⧸ N) := by
    exact isPGroup_quotient_of_sup_eq_top N D
      (hDtwo.of_equiv (subgroupOfEquivOfLe (show D₀ ≤ K from le_sup_right)).symm) hND
  have hRtwo : IsPGroup 2 (solvableRadical K) := by
    have hz : IsPGroup 2 (center N) := by rw [hNcenter]; exact IsPGroup.of_bot
    exact radical_isTwoGroup_of_quasisimple_two_quotient N hz hquot
  have hRcentral : solvableRadical K ≤ centralizer (N : Set K) := by
    rcases simple_subnormal_normal_dichotomy N (solvableRadical K)
      (inferInstance : N.Normal).isSubnormal with hNR | hcommR
    · have hsolv : Group.IsSolvable N :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNR)
      exact (hNnoncomm (isMulCommutative_iff.mpr
        ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv))).elim
    · rw [commutator_comm] at hcommR
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommR
  let _ : NeZero f := ⟨by omega⟩
  let a : MulAut L := MulAut.conjNormal t
  have ha2 : a ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  have hao : ¬ ∃ x : L, a = MulAut.conj x := by
    rintro ⟨x, hx⟩
    have heq : t = (x : G) :=
      MulAut.conjNormal_injective_of_centralizer_eq_bot L hC
        (hx.trans MulAut.conjNormal_val.symm)
    exact htL (by simpa only [heq] using x.property)
  let eM := e.trans (MulEquiv.subgroupCongr (psu3Model_eq_projective f))
  have hrigidModel := BenderSuzuki.MatrixGroups.HermitianForm.projective_outer_fixedCentralizerRigid
    (uform f) hf (uform_form f) (card_UField f (by omega))
      (card_fixed_UField f (by omega)) (MulAut.congr eM a) (by
        rw [← map_pow, ha2, map_one]) (fun h => hao ((MulAut.congr_inner_iff eM a).mp h))
  have hrigid : MulAut.FixedCentralizerRigid a :=
    (MulAut.fixedCentralizerRigid_congr_iff eM a).mp hrigidModel
  have hA_rank_one_of_le_radical (hAR : A.subgroupOf K ≤ solvableRadical K) :
      Group.rank A ≤ 1 := by
    let : IsElementaryAbelian 2 A := hA
    let jA : A →* MulAut L :=
      (MulAut.conjNormal : G →* MulAut L).comp A.subtype
    have hjA : Function.Injective jA :=
      (MulAut.conjNormal_injective_of_centralizer_eq_bot L hC).comp
        A.subtype_injective
    have hjz : jA.range ≤ Subgroup.zpowers a := by
      rintro _ ⟨x, rfl⟩
      have hcommA : Commute (jA x) a := by
        change MulAut.conjNormal (x : G) * MulAut.conjNormal t =
          MulAut.conjNormal t * MulAut.conjNormal (x : G)
        have hxtA : x * (⟨t, htA⟩ : A) = (⟨t, htA⟩ : A) * x :=
          (isMulCommutative_iff.mp (inferInstance : IsMulCommutative A)) x ⟨t, htA⟩
        have hxt : (x : G) * t = t * (x : G) :=
          congrArg (fun z : A => (z : G)) hxtA
        simpa only [map_mul] using
          congrArg (fun z : G => (MulAut.conjNormal (H := L) z)) hxt
      let xK : K := ⟨(x : G), hAK x.property⟩
      have hxA : xK ∈ A.subgroupOf K := by
        change (x : G) ∈ A
        exact x.property
      have hxR : xK ∈ solvableRadical K := hAR hxA
      have hxN : ∀ y : N₀, Commute (x : G) (y : G) := by
        intro y
        let hyK : K := ⟨(y : G), by
          change (y : G) ∈ N₀ ⊔ D₀
          exact (show N₀ ≤ N₀ ⊔ D₀ from le_sup_left) y.property⟩
        have hyN : hyK ∈ N := by
          rw [Subgroup.mem_subgroupOf]
          have hval : (hyK : G) = (y : G) := rfl
          rw [hval]
          exact y.property
        have hxCent : xK ∈ centralizer (N : Set K) := hRcentral hxR
        change (x : G) * (y : G) = (y : G) * (x : G)
        calc
          (x : G) * (y : G) = (xK : G) * (hyK : G) := rfl
          _ = (hyK : G) * (xK : G) := congrArg (fun z : K => (z : G))
            (mem_centralizer_iff.mp hxCent hyK hyN).symm
          _ = (y : G) * (x : G) := rfl
      have hfix' : ∀ y : L, a y = y → jA x y = y := by
        intro y hy
        have hyN : (y : G) ∈ N₀ := by
          refine ⟨?_, y.property⟩
          change (y : G) ∈ centralizer ({t} : Set G)
          rw [mem_centralizer_singleton_iff]
          exact (show (y : G) * t = t * (y : G) by
            have hy' : t * (y : G) * t⁻¹ = (y : G) := by
              simpa [a, MulAut.conjNormal_apply] using congrArg (fun z : L => (z : G)) hy
            rw [mul_inv_eq_iff_eq_mul, eq_comm] at hy'
            exact hy')
        apply Subtype.ext
        change (x : G) * (y : G) * (x : G)⁻¹ = (y : G)
        rw [mul_inv_eq_iff_eq_mul]
        exact (hxN ⟨(y : G), hyN⟩).eq
      rcases hrigid (jA x) hcommA hfix' with hx | hx
      · rw [hx]
        exact Subgroup.one_mem _
      · rw [hx]
        exact Subgroup.mem_zpowers a
    let jAz : A →* Subgroup.zpowers a := jA.codRestrict _ (fun x => by
      have hxrange : jA x ∈ jA.range := ⟨x, rfl⟩
      exact hjz hxrange)
    have hjAz : Function.Injective jAz :=
      (MonoidHom.injective_codRestrict jA _ _).mpr hjA
    have hp : primeRank 2 A ≤ primeRank 2 (Subgroup.zpowers a) :=
      primeRank_le_of_injective 2 jAz hjAz
    obtain ⟨Pz⟩ := Sylow.nonempty (p := 2) (G := Subgroup.zpowers a)
    have hpz : primeRank 2 (Subgroup.zpowers a) ≤ 1 :=
      Pz.primeRank_le_one_of_isCyclic (Subgroup.isCyclic_of_le le_top)
    have hpr : IsPGroup 2 jAz.range :=
      hA.isPGroup.of_surjective jAz.rangeRestrict jAz.rangeRestrict_surjective
    have hrange : Group.rank jAz.range ≤ primeRank 2 (Subgroup.zpowers a) :=
      jAz.range.rank_le_primeRank 2 hpr
    calc
      Group.rank A = Group.rank jAz.range :=
        Group.rank_congr (MonoidHom.ofInjective hjAz)
      _ ≤ primeRank 2 (Subgroup.zpowers a) := hrange
      _ ≤ 1 := hpz
  have hARnot : ¬ A.subgroupOf K ≤ solvableRadical K := by
    intro hAR
    have hrA := hA_rank_one_of_le_radical hAR
    omega
  have hclosed : IsTwoClosed (solvableRadical K) := by
    obtain ⟨U, hU⟩ := (hRtwo.to_subgroup (⊤ : Subgroup (solvableRadical K))).exists_le_sylow
    have hUtop : (U : Subgroup (solvableRadical K)) = ⊤ := top_unique hU
    exact ⟨U, hUtop ▸ inferInstance⟩
  let Q := K ⧸ solvableRadical K
  let q := QuotientGroup.mk' (solvableRadical K)
  let C := N.map q
  let : C.Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  let eC := normalRadicalQuotientEquivImage N
  let : IsSimpleGroup (N ⧸ solvableRadical N) := quasisimple_radicalQuotient_isSimple N
  let : IsSimpleGroup C := eC.symm.isSimpleGroup
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap N) (q.subgroupMap_surjective N)
  have hCnoncomm : ¬ IsMulCommutative C := Group.IsPerfect.not_isMulCommutative C
  have hCcenter : center C = ⊥ := by
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center C) inferInstance).resolve_right
      (fun h => hCnoncomm (center_eq_top_iff.mp h))
  let : IsQuasisimple C := ⟨
    ((QuotientGroup.quotientMulEquivOfEq hCcenter).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hqC : IsPGroup 2 (Q ⧸ C) := normal_radical_image_two_quotient N hquot
  have hcore : pCore 2 Q = ⊥ :=
    SimpleSocle.pCore_eq_bot solvableRadical_quotient_solvableRadical 2
  have hcentral : centralizer (C : Set Q) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient C
      (Group.IsPerfect.not_isMulCommutative C) hqC hcore
  have hlayer : componentLayer Q = C :=
    (SimpleSocle.layer_residuals C hqC).1
  have hres : pResidual 2 K = solvableResidual K := by
    obtain ⟨_, hp, hs⟩ := SimpleSocle.layer_residuals N hquot
    exact hp.trans hs.symm
  have hquotLayer : HasTwoGroupQuotient (componentLayer Q) := by
    rw [hlayer]
    exact ⟨inferInstance, hqC⟩
  have hcomm : C = ⁅C, (A.subgroupOf K).map q⁆ := by
    have hAQ : (A.subgroupOf K).map q ≠ ⊥ := by
      intro hAQ
      apply hARnot
      simpa only [q, QuotientGroup.ker_mk'] using
        (Subgroup.map_eq_bot_iff (A.subgroupOf K)).mp hAQ
    have hc := SimpleSocle.commutator_eq C hcentral
      ((A.subgroupOf K).map q) hAQ
    exact hc
  have hlocalOrbit : componentLayer Q = conjugateJoin
      ((tau ((S : Subgroup G).subgroupOf K) (A.subgroupOf K)).map q) C := by
    rw [conjugateJoin_eq_of_normal, hlayer]
  refine ⟨⟨hclosed, hquotLayer, hres, C,
      ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩,
      hlocalOrbit, Or.inl hcomm⟩,
    ⟨C, (inferInstance : C.Normal),
      ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩,
      hlayer, hlocalOrbit, hcomm⟩⟩

/- The full E.1.5 witness, including the literal quotient-rank drop. -/
theorem isEMemberAt_localCandidate
    (L : Subgroup G) [L.Normal] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSU3Model f) (hC : centralizer (L : Set G) = ⊥)
    (hO : pCore 2 G = ⊥) (S : Sylow 2 G) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hAS : A ≤ (S : Subgroup G))
    (hr : f < Group.rank A) {t : G} (htA : t ∈ A) (htL : t ∉ L)
    (ht2 : t ^ 2 = 1) (P : Sylow 2 (fixedCore L t))
    (hPA : (P : Subgroup (fixedCore L t)).map (fixedCore L t).subtype ≤ A) :
    IsEMemberAt f (S : Subgroup G) A (localCandidate L (S : Subgroup G) A t) ∧
      ¬ localCandidate L (S : Subgroup G) A t ≤
        normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  let K := localCandidate L (S : Subgroup G) A t
  obtain ⟨hAK, htau, hSyl⟩ := localCandidate_E0 L S A hA hAS hO htA P hPA
  have hAK' : A ≤ K := by simpa [K] using hAK
  have htau' : tau (S : Subgroup G) A ≤ K := by simpa [K] using htau
  have hSyl' : ∃ U : Sylow 2 K, (U : Subgroup K) = (S : Subgroup G).subgroupOf K := by
    simpa [K] using hSyl
  have hpack := localCandidate_eCase L hf e hC hO S A hA hAS hr htA htL ht2 P hPA
  rcases hpack with ⟨hcomp, C, hCnormal, hCcomp, hlayer, hlocalOrbit, hcomm⟩
  have hcomp : ECaseComponent (S : Subgroup G) A K := by
    simpa [K] using hcomp
  dsimp [ECaseComponent] at hcomp
  rcases hcomp with ⟨hclosed, hquot, hres, _hrest⟩
  let : C.Normal := hCnormal
  have hCcomp' : IsComponent (K ⧸ solvableRadical K) C := by
    simpa [K] using hCcomp
  have hlayer' : componentLayer (K ⧸ solvableRadical K) = C := by
    simpa [K] using hlayer
  let q := QuotientGroup.mk' (solvableRadical K)
  let z : K := ⟨t, hAK' htA⟩
  have hztop : z ∈ center K := by
    rw [mem_center_iff]
    intro y
    have hyK : (y : G) ∈ localCandidate L (S : Subgroup G) A t := by
      change (y : G) ∈ K
      exact y.property
    have hyC : (y : G) ∈ centralizer ({t} : Set G) :=
      localCandidate_le_centralizer L (S : Subgroup G) A hO htA hyK
    have hycomm : t * (y : G) = (y : G) * t :=
      (mem_centralizer_iff.mp hyC) t (Set.mem_singleton t)
    apply Subtype.ext
    change (y : G) * t = t * (y : G)
    exact hycomm.symm
  have hztR : z ∈ solvableRadical K :=
    (le_solvableRadical (center K) inferInstance inferInstance) hztop
  let : IsElementaryAbelian 2 (A.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf hAK'
  have hrankSub : Group.rank (A.subgroupOf K) ≤ f + 1 := by
    rw [Group.rank_congr (subgroupOfEquivOfLe hAK')]
    exact ambient_elementary_rank L hf e hC A hA
  have hzA : z ∈ A.subgroupOf K := by
    change t ∈ A
    exact htA
  have hzt1 : z ≠ 1 := by
    intro hz
    apply htL
    have : t = 1 := congrArg (fun x : K => (x : G)) hz
    rw [this]
    exact L.one_mem
  have hqz : q z = 1 := by
    exact (QuotientGroup.eq_one_iff z).mpr hztR
  have hqrank : Group.rank ((A.subgroupOf K).map q) ≤ f :=
    IsElementaryAbelian.rank_map_le_of_nontrivial_kernel (A.subgroupOf K) q hrankSub z hzA hzt1 hqz
  have hE : IsEMemberAt f (S : Subgroup G) A K := by
    apply isEMemberAt_of_normal_quotient_component
      (T := (S : Subgroup G)) (A := A) (K := K)
      hA hAS hAK' htau' hSyl' hclosed hquot hres C hCcomp' hlayer' hcomm hqrank
  have hescape : ¬ K ≤ normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    intro hKB
    apply fixedCore_not_le_borel L hf e hC S t htL ht2
    exact (show fixedCore L t ≤ K from le_sup_left).trans hKB
  exact ⟨hE, hescape⟩

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal
