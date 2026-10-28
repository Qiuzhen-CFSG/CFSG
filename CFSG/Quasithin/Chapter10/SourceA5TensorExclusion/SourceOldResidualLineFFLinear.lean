module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SpecialLinearThree
public import Theory.SpecificGroups.PSL3Even.TauGeometry.Pair
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.FixedCubic
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.SolvableSylowControl

/-!
# Cubic Cartan normalization in the linear-three FF rows

A proper local component at the standard Sylow of PSL₃(4) is one of its
point and line parabolic residuals. Sylow-stabilizing automorphisms permute
these two actual subgroups, so a cubic automorphism fixes both. Perfectness
lifts the resulting equality through the central SL₃-to-PSL₃ projection.

Solvable Sylow overgroups of SL₃(4) normalize the marked Sylow. Applying
this fact to the intersection with a normal special-linear image makes
an original cubic Cartan preserve that image's proper local component.
The final consumer retains the actual quotient map, old local component,
Sylow intersection and solvable Cartan--Sylow image. Both the single and
repeated linear-three moved-section models use this same actor theorem.

Source: Aschbacher--Smith, Proposition 9.3.1, printed pp.732--733, especially
the Cartan-normalization step on p.733; the local embeddings are A.3.14.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3.LinearThree.OuterExtensions
open CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceOldResidualLineFFLinear
open ChapterA.Section03
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem local_perfect {Q : Type*} [Group Q] {S B : Subgroup Q}
    (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

/-- At the standard full Sylow, the literal proper local component is one
of the two affine parabolic residuals. -/
theorem projective_standard_local (hF : Nat.card F = 4)
    (B : Subgroup PSL(3,F)) (hB : B ∈ localCComponents (unipotent F))
    (hproper : B ≠ ⊤) : B = pointLocal F ∨ B = lineLocal F := by
  let S := unipotentSylow F (by decide : 0 < 2) (by simpa using hF : Nat.card F = 2 ^ 2)
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect B := local_perfect hB
  have hjoin : B ⊔ unipotent F ≠ ⊤ := by
    intro ht
    have hc : B.IsCComponent := by
      have hm := hB
      change (B.subgroupOf (B ⊔ unipotent F)).IsCComponent at hm
      rw [ht] at hm
      simpa only [map_subgroupOf_eq_of_le le_top] using hm.map_subtype (.top)
    exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hproper
  obtain hp | hp := UnipotentOvergroups.overgroup_unipotent F _ le_sup_right hjoin
  · left
    let := pointLocal_isPerfect F (by omega)
    apply local_eq_of_sl2_core_quotient (pointLocal F) (by omega)
      (pointLocalCoreQuotientEquiv F) S B hB
    · rw [← ParabolicResiduals.pointParabolic_residual F (by omega)]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    · exact unipotent_le_pointLocal F
  · right
    let := lineLocal_isPerfect F (by omega)
    apply local_eq_of_sl2_core_quotient (lineLocal F) (by omega)
      (lineLocalCoreQuotientEquiv F) S B hB
    · rw [← ParabolicResiduals.lineParabolic_residual F (by omega)]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    · exact unipotent_le_lineLocal F

private theorem cubic_map_of_square_map {Q : Type*} [Group Q]
    (a : MulAut Q) (ha : a ^ 3 = 1) (B : Subgroup Q)
    (hB : (B.map a.toMonoidHom).map a.toMonoidHom = B) : B.map a.toMonoidHom = B := by
  have hc : ((B.map a.toMonoidHom).map a.toMonoidHom).map a.toMonoidHom = B := by
    rw [map_map,map_map]
    have he : (a.toMonoidHom.comp a.toMonoidHom).comp a.toMonoidHom = (a ^ 3).toMonoidHom := by
      ext x
      simp [pow_succ,MulAut.mul_apply]
    rw [he,ha]
    exact map_id B
  rwa [hB] at hc

/-- Cubic automorphisms preserving the standard Sylow fix both actual
parabolic residuals, including the four-element field. -/
theorem projective_cubic_preserves_standard_locals (hF : Nat.card F = 4)
    (a : MulAut PSL(3,F)) (ha : a ^ 3 = 1)
    (hU : (unipotent F).map a.toMonoidHom = unipotent F) (b : Bool) :
    (localFactor F b).map a.toMonoidHom = localFactor F b := by
  obtain h | h := Matrix.PSL3Even.TauGeometry.local_pair_of_unipotent_stable F
    (by decide : 0 < 2) (by simpa using hF : Nat.card F = 2 ^ 2) a hU
  · exact h b
  · apply cubic_map_of_square_map a ha
    rw [h b,h (!b),Bool.not_not]

/-- A cubic automorphism preserving a supplied full Sylow fixes every
proper local C-component of PSL₃(4) at that Sylow. -/
theorem projective_cubic_preserves_local (hF : Nat.card F = 4)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (a : MulAut PSL(3,F)) (ha : a ^ 3 = 1)
    (hS : (S : Subgroup PSL(3,F)).map a.toMonoidHom = S) : B.map a.toMonoidHom = B := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) S
    (unipotentSylow F (by decide : 0 < 2) (by simpa using hF : Nat.card F = 2 ^ 2))
  let e := MulAut.conj g
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hstd : (S' : Subgroup PSL(3,F)) = unipotent F := congrArg Sylow.toSubgroup hg
  let c := MulAut.congr e a
  have hc : c ^ 3 = 1 := by rw [← map_pow,ha,map_one]
  have hcomm (K : Subgroup PSL(3,F)) :
      (K.map e.toMonoidHom).map c.toMonoidHom = (K.map a.toMonoidHom).map e.toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [c,MulAut.congr_apply]
  have hU : (unipotent F).map c.toMonoidHom = unipotent F := by
    rw [←hstd]
    change ((S : Subgroup PSL(3,F)).map e.toMonoidHom).map c.toMonoidHom = _
    rw [hcomm,hS]
    exact (Sylow.coe_mapSurjective e.surjective S).symm
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hl : B.map e.toMonoidHom ∈ localCComponents (unipotent F) := by
    rw [←hstd]
    exact Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom
  have hp : B.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hproper
    exact (map_injective e.injective) (ht.trans (map_top_of_surjective _ e.surjective).symm)
  have hm : (B.map e.toMonoidHom).map c.toMonoidHom = B.map e.toMonoidHom := by
    obtain hb | hb := projective_standard_local hF _ hl hp
    · rw [hb]
      exact projective_cubic_preserves_standard_locals hF c hc hU true
    · rw [hb]
      exact projective_cubic_preserves_standard_locals hF c hc hU false
  rw [hcomm] at hm
  exact map_injective e.injective hm

/-- The cubic Sylow stabilizer also fixes the actual perfect local subgroup
in SL₃(4). Only the central SL₃-to-PSL₃ projection is used to lift equality. -/
theorem special_linear_cubic_preserves_local (hF : Nat.card F = 4)
    (S : Sylow 2 SL(3,F)) (B : Subgroup SL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (a : MulAut SL(3,F)) (ha : a ^ 3 = 1)
    (hS : (S : Subgroup SL(3,F)).map a.toMonoidHom = S) : B.map a.toMonoidHom = B := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect B := local_perfect hB
  let : Group.IsPerfect (B.map a.toMonoidHom) := Group.IsPerfect.map _
  let c : MulAut PSL(3,F) := quotientAut (center SL(3,F)) a
  have hc : c ^ 3 = 1 := by rw [←map_pow,ha,map_one]
  have hcomm (K : Subgroup SL(3,F)) :
      (K.map (projection F)).map c.toMonoidHom = (K.map a.toMonoidHom).map (projection F) := by
    rw [map_map,map_map]
    congr 1
    ext x
    exact quotientAut_apply_mk (center SL(3,F)) a x
  let P := S.mapSurjective (projection_surjective F)
  have hP : (P : Subgroup PSL(3,F)).map c.toMonoidHom = P := by
    change ((S : Subgroup SL(3,F)).map (projection F)).map c.toMonoidHom = _
    rw [hcomm,hS]
    exact (Sylow.coe_mapSurjective (projection_surjective F) S).symm
  have hl : B.map (projection F) ∈ localCComponents (P : Subgroup PSL(3,F)) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB (projection F)
  have hk : (projection F).ker ≤ center SL(3,F) := (projection_ker F).le
  have hp : B.map (projection F) ≠ ⊤ := by
    intro ht
    apply hproper
    apply top_unique
    apply le_of_map_le_of_perfect (projection F) hk ⊤ B
    rw [ht]
    exact le_top
  have he := projective_cubic_preserves_local hF P _ hl hp c hc hP
  rw [hcomm] at he
  exact le_antisymm (le_of_map_le_of_perfect (projection F) hk _ _ he.le)
    (le_of_map_le_of_perfect (projection F) hk _ _ he.ge)


/-- The marked cubic-automorphism assertion is invariant under a genuine
special-linear model equivalence. -/
theorem cubic_preserves_local_of_equiv {I : Type*} [Group I] [Finite I]
    (hF : Nat.card F = 4) (e : I ≃* SL(3,F))
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
  have hP : (P : Subgroup SL(3,F)).map c.toMonoidHom = P := by
    change ((S : Subgroup I).map e.toMonoidHom).map c.toMonoidHom =
      (S : Subgroup I).map e.toMonoidHom
    rw [hcomm,hS]
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hl : B.map e.toMonoidHom ∈ localCComponents (P : Subgroup SL(3,F)) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom
  have hp' : B.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hp
    exact (map_injective e.injective) (ht.trans (map_top_of_surjective _ e.surjective).symm)
  have hm := special_linear_cubic_preserves_local hF P _ hl hp' c hc hP
  rw [hcomm] at hm
  exact map_injective e.injective hm

/-- A cubic subgroup of a solvable overgroup of the marked Sylow normalizes
the actual proper local component in a normal SL₃(4) subgroup. -/
theorem cubic_subgroup_normalizes_local {Q : Type*} [Group Q] [Finite Q]
    (I A Y : Subgroup Q) [I.Normal] [Group.IsSolvable Y]
    (hF : Nat.card F = 4) (e : I ≃* SL(3,F))
    (R : Sylow 2 I) (B : Subgroup I)
    (hB : B ∈ localCComponents R) (hp : B ≠ ⊤)
    (hAY : A ≤ Y) (hRY : (R : Subgroup I).map I.subtype ≤ Y)
    (hA : ∀ a ∈ A, a ^ 3 = 1) : A ≤ normalizer (B.map I.subtype : Set Q) := by
  have hcontrol : SolvableSylowControl 2 I :=
    SolvableSylowControl.of_equiv e (four_solvable_sylow_overgroup_normalizes hF)
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
  have hlocal := cubic_preserves_local_of_equiv hF e R B hB hp c hc hR
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (B.map I.subtype).map (MulAut.conj a).toMonoidHom = B.map I.subtype
  rw [←hcomm,hlocal]


/-- The literal image consumer. In the source application `f = actionMk W`,
`P` is the chosen Sylow, and `K` is the old residual in the normal overcomponent
`J`. The original Cartan is retained in the solvable image overgroup `Y`. -/
theorem mapped_cubic_subgroup_normalizes_local
    {X Q : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    (f : X →* Q) (hf : Function.Surjective f)
    (P A J K : Subgroup X) [J.Normal] (hKJ : K ≤ J)
    (R : Sylow 2 J) (hR : (R : Subgroup J) = P.subgroupOf J)
    (Y : Subgroup Q) [Group.IsSolvable Y]
    (hAY : A.map f ≤ Y) (hPY : P.map f ≤ Y)
    (hA : ∀ a ∈ A, a ^ 3 = 1)
    (hF : Nat.card F = 4) (e : J.map f ≃* SL(3,F))
    (hlocal : (K.map f).subgroupOf (J.map f) ∈
      localCComponents (R.mapSurjective (f.subgroupMap_surjective J)))
    (hp : (K.map f).subgroupOf (J.map f) ≠ ⊤) :
    A.map f ≤ normalizer (K.map f : Set Q) := by
  let I := J.map f
  let S := R.mapSurjective (f.subgroupMap_surjective J)
  let B := (K.map f).subgroupOf I
  let : I.Normal := (inferInstance : J.Normal).map f hf
  have hSY : (S : Subgroup I).map I.subtype ≤ Y := by
    rintro _ ⟨x,hx,rfl⟩
    change x ∈ (R : Subgroup J).map (f.subgroupMap J) at hx
    obtain ⟨j,hj,rfl⟩ := hx
    apply hPY
    refine ⟨j,?_,rfl⟩
    rw [hR] at hj
    exact hj
  have hAc : ∀ a ∈ A.map f, a ^ 3 = 1 := by
    rintro _ ⟨a,ha,rfl⟩
    rw [←map_pow,hA a ha,map_one]
  have hn := cubic_subgroup_normalizes_local I (A.map f) Y hF e S B
    hlocal hp hAY hSY hAc
  simpa only [B,I,map_subgroupOf_eq_of_le (map_mono hKJ)] using hn

end CFSG.Quasithin.Chapter10.SourceOldResidualLineFFLinear
