module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFLinear
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFSolvable
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartan
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import Theory.GroupTheory.PerfectNormalizerCoreQuotient
public import Theory.GroupTheory.PerfectSolvableSectionLift
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# Cartan normalization in the projective-three containing row

Let K be the original residual in a normal containing C-component J of
N_G(V₁), with J/O₂(J) isomorphic to PSL₃(4). The original Cartan together
with T generates a solvable subgroup. After quotienting N_G(V₁) by its
two-core, solvable Sylow control therefore makes its Cartan image preserve
the marked Sylow of the J-image. Cubic automorphisms fixing that Sylow fix
each proper local component, by the actual point and line parabolic pair.

The ambient two-core lies in T and normalizes K. Perfectness both preserves
properness in the quotient and lifts the resulting normalizer back to K.
The final theorem supplies this argument for the literal old residual,
Cartan, tensor line and containing component, without a normalization
assumption on the Cartan or its action on T.

Source: Aschbacher--Smith, Proposition 9.3.1, printed p.732, the PSL₃(4)
case of the containing-component reduction using A.3.14.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalizationLinear
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem projective_cubic_preserves_local_of_equiv {I : Type*} [Group I] [Finite I]
    (hF : Nat.card F = 4) (e : I ≃* PSL(3,F))
    (S : Sylow 2 I) (B : Subgroup I)
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (a : MulAut I) (ha : a ^ 3 = 1)
    (hS : (S : Subgroup I).map a.toMonoidHom = S) : B.map a.toMonoidHom = B := by
  let c := MulAut.congr e a
  have hc : c ^ 3 = 1 := by rw [←map_pow,ha,map_one]
  have hcomm (K : Subgroup I) :
      (K.map e.toMonoidHom).map c.toMonoidHom = (K.map a.toMonoidHom).map e.toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [c,MulAut.congr_apply]
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup PSL(3,F)).map c.toMonoidHom = P := by
    change ((S : Subgroup I).map e.toMonoidHom).map c.toMonoidHom =
      (S : Subgroup I).map e.toMonoidHom
    rw [hcomm,hS]
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hl : B.map e.toMonoidHom ∈ localCComponents (P : Subgroup PSL(3,F)) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom
  have hp' : B.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hp
    exact (map_injective e.injective) (ht.trans (map_top_of_surjective _ e.surjective).symm)
  have hm := SourceOldResidualLineFFLinear.projective_cubic_preserves_local
    hF P _ hl hp' c hc hP
  rw [hcomm] at hm
  exact map_injective e.injective hm

private theorem projective_cubic_subgroup_normalizes_local
    {Q : Type*} [Group Q] [Finite Q]
    (I A Y : Subgroup Q) [I.Normal] [Group.IsSolvable Y]
    (hF : Nat.card F = 4) (e : I ≃* PSL(3,F))
    (R : Sylow 2 I) (B : Subgroup I)
    (hB : B ∈ localCComponents R) (hp : B ≠ ⊤)
    (hAY : A ≤ Y) (hRY : (R : Subgroup I).map I.subtype ≤ Y)
    (hA : ∀ a ∈ A, a ^ 3 = 1) : A ≤ normalizer (B.map I.subtype : Set Q) := by
  have hcontrol : SolvableSylowControl 2 I := SolvableSylowControl.of_equiv e
    (SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le F
      (by decide : 2 ≤ 2) (by simpa using hF))
  have hYR : Y ≤ normalizer ((R : Subgroup I).map I.subtype : Set Q) :=
    SolvableSylowControl.normalizes_sylow I Y hcontrol R (by
      rw [I.normalizer_eq_top]
      exact le_top) hRY
  intro a ha
  let c : MulAut I := MulAut.conjNormal a
  have hc : c ^ 3 = 1 := by rw [←map_pow,hA a ha,map_one]
  have hcomm (K : Subgroup I) :
      (K.map c.toMonoidHom).map I.subtype =
        (K.map I.subtype).map (MulAut.conj a).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  have hR : (R : Subgroup I).map c.toMonoidHom = R := by
    apply map_injective I.subtype_injective
    rw [hcomm]
    exact mem_normalizer_iff_map_conj_eq.mp (hYR (hAY ha))
  have hlocal := projective_cubic_preserves_local_of_equiv hF e R B hB hp c hc hR
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (B.map I.subtype).map (MulAut.conj a).toMonoidHom = B.map I.subtype
  rw [←hcomm,hlocal]

/-- The normal projective-three container controls the original perfect local
subgroup, with both the ambient two-core and the marked Sylow retained. -/
theorem cartan_normalizes_in_projective_container
    {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (K J A Y : Subgroup X) [J.Normal] [Group.IsSolvable Y]
    (hJ : J.IsCComponent) (hK : K ∈ localCComponents P)
    (hKJ : K < J) (hPK : (P : Subgroup X) ≤ normalizer (K : Set X))
    (hAY : A ≤ Y) (hPY : (P : Subgroup X) ≤ Y)
    (hA : ∀ a ∈ A, a ^ 3 = 1)
    (hF : Nat.card F = 4) (eJ : (J ⧸ pCore 2 J) ≃* PSL(3,F)) :
    A ≤ normalizer (K : Set X) := by
  let Q := pCore 2 X
  let q := QuotientGroup.mk' Q
  let : Group.IsNilpotent Q := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hQK : Q ≤ normalizer (K : Set X) :=
    (pCore_isPGroup.le_sylow_of_normal P).trans hPK
  let : Group.IsPerfect K := by
    let := hK.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (P : Subgroup X) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : Group.IsPerfect J := hJ.perfect
  let S := P.mapSurjective (QuotientGroup.mk'_surjective Q)
  let I := J.map q
  let KB := K.map q
  let : I.Normal := inferInstance
  have hIB : KB ≤ I := map_mono hKJ.le
  have hl : KB ∈ localCComponents S :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hK q
  have hSK : (S : Subgroup (X ⧸ Q)) ≤ normalizer (KB : Set (X ⧸ Q)) :=
    (map_mono hPK).trans (le_normalizer_map q)
  have hI : I.IsCComponent := hJ.map_quotient Q
  obtain ⟨R,hR,hlocal,_⟩ := exists_local_sylow_normalizing S hl hI.subnormal hIB hSK
  have hproper : KB.subgroupOf I ≠ ⊤ := by
    intro ht
    have he : KB = I := le_antisymm hIB (subgroupOf_eq_top.mp ht)
    have hsup : K ⊔ Q = J ⊔ Q := by
      simpa only [KB,I,q,comap_map_eq,QuotientGroup.ker_mk'] using congrArg (comap q) he
    have hJK : J ≤ K := by
      rw [←map_solvableResidual_sup_eq_of_perfect_normalized K Q hQK]
      apply le_map_solvableResidual_of_isPerfect J (K ⊔ Q)
      rw [hsup]
      exact le_sup_left
    exact hKJ.not_ge hJK
  let ei : I ≃* PSL(3,F) := (cComponentTwoCoreQuotientEquiv hJ).symm.trans eJ
  let : Group.IsSolvable (Y.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective Y)
  have hn := projective_cubic_subgroup_normalizes_local I (A.map q) (Y.map q) hF ei
    R (KB.subgroupOf I) hlocal hproper (map_mono hAY) (by
      rw [hR,subgroupOf_map_subtype]
      exact inf_le_left.trans (map_mono hPY)) (by
      rintro a ⟨a,ha,rfl⟩
      rw [←map_pow,hA a ha,map_one])
  rw [map_subgroupOf_eq_of_le hIB] at hn
  have hc := map_le_iff_le_comap.mp hn
  rwa [normalizer_perfect_image_comap K Q pCore_isPGroup hQK] at hc

end CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalizationLinear

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual original Cartan normalizes the old residual in the PSL₃(4)
containing-component row of the line-normalizer reduction. -/
theorem cartan_normalizes_old_residual_of_projective_three_container
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A J : Subgroup G) [IsElementaryAbelian 3 A]
    (hAB : A ≤ sourceOrbitBorel T L)
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hKJ : (pResidual 2 H).map H.subtype < J)
    {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (eJ : (J ⧸ pCore 2 J) ≃* PSL(3,F)) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa [Nat.card_eq_fintype_card] using hF : Fintype.card F = 2 ^ 2)
  let N := normalizer (m.tensorLine : Set G)
  let K0 := (pResidual 2 H).map H.subtype
  have hKN : K0 ≤ N := hKJ.le.trans hJU
  have hAN : A ≤ N := hAB.trans m.borel_normalizes_tensorLine
  let P := T.subtype m.tensorLine_normalized
  let K := K0.subgroupOf N
  let JN := J.subgroupOf N
  let Y := (A ⊔ (T : Subgroup G)).subgroupOf N
  let : JN.Normal := hnJ
  let : Group.IsSolvable (A ⊔ (T : Subgroup G) : Subgroup G) :=
    m.cartan_sylow_join_isSolvable A hAB
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (sup_le hAN m.tensorLine_normalized)).toMonoidHom)
    (subgroupOfEquivOfLe (sup_le hAN m.tensorLine_normalized)).injective
  have hlocal : K ∈ localCComponents P := SourceEmbeddings.local_restrict
    (source_hstar_residual_mem_local_of_a5 hH eK).1 hKN
  have hKJN : K < JN := by
    refine lt_iff_le_not_ge.mpr ⟨comap_mono hKJ.le,?_⟩
    intro hh
    apply hKJ.not_ge
    have hm := map_mono (f := N.subtype) hh
    rwa [map_subgroupOf_eq_of_le hJU,map_subgroupOf_eq_of_le hKN] at hm
  have hPK : (P : Subgroup N) ≤ normalizer (K : Set N) := by
    rw [←subgroupOf_normalizer_eq hKN]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))
  let b : JN ≃* J := subgroupOfEquivOfLe hJU
  let eJN : (JN ⧸ pCore 2 JN) ≃* PSL(3,F) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eJ
  have hn := SourceOldResidualCartanNormalizationLinear.cartan_normalizes_in_projective_container
    P K JN (A.subgroupOf N) Y hJ hlocal hKJN hPK
    (comap_mono le_sup_left) (comap_mono le_sup_right) (by
      intro a ha
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 3) (a : G) ha)) hF eJN
  rw [←subgroupOf_normalizer_eq hKN] at hn
  exact fun a ha => hn (show (⟨a,hAN ha⟩ : N) ∈ A.subgroupOf N from ha)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
