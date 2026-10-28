module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalCore
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The literal A₅ pair supplies its rank-one Sylow and Borel

The original quotient map from the pair I into H/O₂(H) has a two-group
kernel and symmetric-three image. Hence its kernel is exactly O₂(I),
so I/O₂(I) is S₃. Since the original T contains O₂(I) and the selected
involution outside that core, T ∩ I has index three in I. It is Sylow
and self-normalizing, and equals U_H V.

The final source consumer constructs the actual rank-one model, Sylow
intersection and Borel of I used in F.1.1 and the F.1.12 application in
13.5.17. The earlier ambient identification H=G₁, maximal core V, the
remaining weak-BN hypotheses and F.4.31 recognition are separate source
obligations; no ambient model conclusion is assumed here.

Source: Aschbacher–Smith, 13.5.15 and 13.5.17, printed pp.920,922.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.Section09.Setup.Hypothesis
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)

include d hA312 hH in
/-- The exact pair quotient is S₃, using its original starred projection. -/
theorem normal_pair_quotient_symmetricThree (r : G) (hrH : r ∈ H)
    (hj : Nonempty (Source.starImage H (V ⊔ V.map (MulAut.conj r).toMonoidHom) ≃*
      Equiv.Perm (Fin 3))) :
    let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
  have hIH : I ≤ H := sup_le hf.V_le_H (by
    rintro _ ⟨x,hx,rfl⟩
    exact H.mul_mem (H.mul_mem hrH (hf.V_le_H hx)) (H.inv_mem hrH))
  obtain ⟨j⟩ := hj
  let f := pairProjection (D := D) I hIH
  let j' := (MulEquiv.subgroupCongr (pairProjection_range (D := D) I hIH)).trans j
  let η := j'.toMonoidHom.comp f.rangeRestrict
  have hη : Function.Surjective η := j'.surjective.comp f.rangeRestrict_surjective
  have hk : η.ker = f.ker := by
    ext x
    change j' (f.rangeRestrict x) = 1 ↔ f x = 1
    rw [j'.map_eq_one_iff]
    exact Subtype.ext_iff
  have htwo : IsPGroup 2 η.ker := by
    rw [hk,pairProjection_ker]
    exact (isPGroup_pCoreIn 2 H).comap_subtype
  have hcore := ker_eq_twoCore_of_surjective_perm_three η hη htwo
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective η hη)⟩

include d hA312 hH hU hn in
/-- The literal T ∩ I is U_H V and is a self-normalizing Sylow subgroup of I. -/
theorem normal_pair_sylow_normalizer (v r : G) (hv : v ∈ V) (hvq : v ∉ Source.QH H)
    (hv2 : v ^ 2 = 1) (hr : orderOf r = 3) (hrH : r ∈ H) (hi : v * r * v⁻¹ = r⁻¹) :
    let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
    (T : Subgroup G) ⊓ I = Source.UH H V₃ ⊔ V ∧
    ∃ S : Sylow 2 I, (S : Subgroup I) = (T : Subgroup G).subgroupOf I ∧
      I ⊓ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) = (T : Subgroup G) ⊓ I := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
  let P := (T : Subgroup G).subgroupOf I
  have hp : IsPGroup 2 P := T.isPGroup'.comap_subtype
  have hc : I.pCoreIn 2 = Source.UH H V₃ :=
    normal_pair_core_eq d hA312 hH hU hn v r hv hvq hv2 hr hrH hi
  have hpair := (normal_odd_rotation_cubic d hA312 hH hU v r hv hv2
    (by decide : Nat.Prime 3) (by decide : 3 ≠ 2) hr hrH hi).2
  have hj := hf.pair_star_symmetricThree d.third_index d.module_card
    (fun _ hk hi => source13_5_13_one d hA312 hH hU hk hi)
    (source_seed_centralizer_bound d hA312) r hrH hpair
  obtain ⟨e⟩ := normal_pair_quotient_symmetricThree d hA312 hH r hrH hj
  have hcoreP : pCore 2 I ≤ P := by
    intro x hx
    exact hf.QH_le_T (hf.UH_le_QH (hc.le (mem_map_of_mem I.subtype hx)))
  have hnot : ¬ P ≤ pCore 2 I := by
    intro hle
    have hx := mem_map_of_mem I.subtype (hle (show (⟨v,mem_sup_left hv⟩ : I) ∈ P from hf.V_le_T hv))
    exact hvq (hf.UH_le_QH (hc.le hx))
  obtain ⟨S,hPS⟩ := hp.exists_le_sylow
  have hSi := SymmetricThreeTwoCore.sylow_index_three e S
  have hCi := SymmetricThreeTwoCore.core_index e
  have hmul := relIndex_mul_index hcoreP
  have hmulS := relIndex_mul_index hPS
  rw [hCi] at hmul
  rw [hSi] at hmulS
  have hrel : 2 ≤ (pCore 2 I).relIndex P := by
    have hpos : 0 < (pCore 2 I).relIndex P := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hne : (pCore 2 I).relIndex P ≠ 1 := fun he => hnot (relIndex_eq_one.mp he)
    omega
  have hpos : 0 < P.relIndex (S : Subgroup I) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hPi : P.index = 3 := by nlinarith
  have hodd : ¬ 2 ∣ P.index := by rw [hPi]; decide
  let S₀ : Sylow 2 I := hp.toSylow hodd
  have hnorm := SymmetricThreeTwoCore.sylow_self_normalizing e S₀
  change normalizer (P : Set I) = P at hnorm
  have hTI : ((T : Subgroup G) ⊓ I).subgroupOf I = P := by ext x; exact and_iff_left x.property
  have hnormal : I ⊓ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) = (T : Subgroup G) ⊓ I := by
    rw [← hTI,← subgroupOf_normalizer_eq inf_le_right] at hnorm
    apply le_antisymm
    · rintro x ⟨hxI,hxN⟩
      exact show (⟨x,hxI⟩ : I) ∈ ((T : Subgroup G) ⊓ I).subgroupOf I from
        hnorm ▸ (show (⟨x,hxI⟩ : I) ∈ (normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G)).subgroupOf I from hxN)
    · exact le_inf inf_le_right ((T : Subgroup G) ⊓ I).le_normalizer
  have hUV : Source.UH H V₃ ⊔ V ≤ (T : Subgroup G) ⊓ I :=
    sup_le (le_inf (hf.UH_le_QH.trans hf.QH_le_T) (hc.ge.trans (pCoreIn_le 2 I)))
      (le_inf hf.V_le_T le_sup_left)
  have hUVeq : Source.UH H V₃ ⊔ V = (T : Subgroup G) ⊓ I := by
    apply le_antisymm hUV
    have hi2 : (pCore 2 I).relIndex P = 2 := by rw [hPi] at hmul; omega
    let vI : I := ⟨v,mem_sup_left hv⟩
    have hvP : vI ∈ P := hf.V_le_T hv
    have hvC : vI ∉ pCore 2 I := by
      intro hvC
      exact hvq (hf.UH_le_QH (hc.le (mem_map_of_mem I.subtype hvC)))
    have hgen := sup_zpowers_eq_of_relIndex_prime hcoreP Nat.prime_two hi2 hvP hvC
    have hm := congrArg (Subgroup.map I.subtype) hgen
    rw [Subgroup.map_sup,MonoidHom.map_zpowers] at hm
    change I.pCoreIn 2 ⊔ zpowers v = P.map I.subtype at hm
    rw [hc] at hm
    have he : P.map I.subtype = (T : Subgroup G) ⊓ I := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨hy,y.property⟩
      · rintro ⟨hxT,hxI⟩
        exact ⟨⟨x,hxI⟩,hxT,rfl⟩
    rw [←he,←hm]
    exact sup_le_sup_left (zpowers_le.mpr hv) (Source.UH H V₃)
  exact ⟨hUVeq.symm,S₀,rfl,hnormal⟩

include d hA312 hH hU hn in
/-- Original 13.5.17's rank-one and self-normalizing Sylow clauses on the
source pair, expressed using the genuine F.1 definitions. -/
theorem source_normal_pair_rank_one :
    ∃ r ∈ H, orderOf r = 3 ∧
      let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
      I.pCoreIn 2 = Source.UH H V₃ ∧
      ChapterF.Source.IsRankOneModel (I ⧸ pCore 2 I) ∧
      ChapterF.Source.borel I (T : Subgroup G) = Source.UH H V₃ ⊔ V ∧
      ∃ S : Sylow 2 I,
        (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I := by
  obtain ⟨v,hv,hvq,hv2,r,hrH,hr,hi,hcore,hj⟩ :=
    source_normal_pair_core d hA312 hH hU hn
  obtain ⟨e⟩ := normal_pair_quotient_symmetricThree d hA312 hH r hrH hj
  obtain ⟨hTI,S,hS,hN⟩ := normal_pair_sylow_normalizer d hA312 hH hU hn
    v r hv hvq hv2 hr hrH hi
  refine ⟨r,hrH,hr,hcore,?_,hN.trans hTI,S,?_⟩
  · apply ChapterF.Source.IsRankOneModel.linear 1 (by decide)
    refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
    exact ⟨e.trans (SLTwoPermThree.sl2Two_equiv_perm_three.some.symm.trans
      (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))⟩
  · rw [hS]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy,y.property⟩
    · rintro ⟨hxT,hxI⟩
      exact ⟨⟨x,hxI⟩,hxT,rfl⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
