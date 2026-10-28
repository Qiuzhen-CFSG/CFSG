module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.FixedCentralizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import CFSG.Quasithin.ChapterE.Section01.QuotientLifting.OddSections
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.SpecificGroups.PSL2.FiveProjectivePermutation

/-!
# Positioned projective images in the characteristic-five inner model

A specified actor generates PGL₂(5) when its image has order two, or has
order four outside the literal PSL₂ range and the positioned S₅ generation
input holds. The rank-one case uses the whole-group E2 member. Generation
lifts through the actual normal two-group kernel, then E.1.8 carries each
local member to the original ambient family and literal Sylow intersection.
The pure-field centralizer application uses its marked projective projection.

`HasPositionedCentralizerGeometry` is a still-unproved finite geometric
obligation: an original family actor must be positioned in an actual
involution centralizer outside each proposed maximal overgroup containing
the weak-closure normalizer. The final conditional theorem shows precisely
how this geometry gives escape. Neither that definition nor this reduction
asserts the source theorem or constructs the missing fusion geometry.

Source: Aschbacher--Smith E.1.2, E.1.5, E.1.8, E.1.10(7), and E.1.14(6),
printed pp.210--214; the last cites Aschbacher (1982), Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

/-- Generation by a specified actor lifts through the actual normal two-kernel. -/
theorem actor_generation_of_two_kernel (q : G →* Q) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (T : Sylow 2 G) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hgen : eSubgroup 1 ((T : Subgroup G).map q) (A.map q) ⊔
      (T : Subgroup G).map q = ⊤) :
    eSubgroup 1 (T : Subgroup G) A ⊔ (T : Subgroup G) = ⊤ := by
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let π := QuotientGroup.mk' q.ker
  have he : e.toMonoidHom.comp π = q := by ext x; rfl
  have hg : eSubgroup 1 ((T : Subgroup G).map π) (A.map π) ⊔
      (T : Subgroup G).map π = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, map_eSubgroup_equiv, Subgroup.map_map, Subgroup.map_map,
      map_top_of_surjective e.toMonoidHom e.surjective, he]
    exact hgen
  have hm : (eSubgroup 1 (T : Subgroup G) A ⊔ (T : Subgroup G)).map π = ⊤ := by
    apply top_unique
    rw [← hg]
    exact sup_le (quotient_eSubgroup_le_map_sup_sylow T A q.ker hAT)
      (map_mono le_sup_right)
  have hk : q.ker ≤ eSubgroup 1 (T : Subgroup G) A ⊔ (T : Subgroup G) :=
    (hker.le_sylow_of_normal T).trans le_sup_right
  have hc := congrArg (comap π) hm
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk', sup_eq_left.mpr hk,
    comap_top] using hc

variable {F : Type*} [Field F] [Finite F]

/-- The projective coordinate of the literal pure-field centralizer. -/
@[expose] def projectiveProjection (hF : Nat.card F = 5 ^ 2) (σ : F ≃+* F)
    (hσ : orderOf σ = 2) :
    centralizer ({pure σ} : Set (innerModel F σ)) →*
      PGL2 (FixedPoints.subfield (zpowers σ) F) :=
  (MonoidHom.fst _ _).comp
    (pureCentralizerEquiv (by decide : Nat.Prime 5) (by decide) hF σ hσ).toMonoidHom

theorem projectiveProjection_surjective (hF : Nat.card F = 5 ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    Function.Surjective (projectiveProjection hF σ hσ) := by
  intro x
  exact ⟨(pureCentralizerEquiv (by decide : Nat.Prime 5) (by decide) hF σ hσ).symm
    (x, 1), by simp [projectiveProjection]⟩

theorem projectiveProjection_two_kernel (hF : Nat.card F = 5 ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    IsPGroup 2 (projectiveProjection hF σ hσ).ker := by
  let e := pureCentralizerEquiv (by decide : Nat.Prime 5) (by decide) hF σ hσ
  let j : (projectiveProjection hF σ hσ).ker →* zpowers σ :=
    ((MonoidHom.snd _ _).comp e.toMonoidHom).comp
      (projectiveProjection hF σ hσ).ker.subtype
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact h
  have hc : IsPGroup 2 (zpowers σ) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers, pow_one] using hσ)
  exact hc.of_injective j hj

/-- The coordinate equation keeps the fixed-field matrix marking. -/
theorem projectiveProjection_symm (hF : Nat.card F = 5 ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (x : PGL2 (FixedPoints.subfield (zpowers σ) F) × zpowers σ) :
    projectiveProjection hF σ hσ
      ((pureCentralizerEquiv (by decide : Nat.Prime 5) (by decide) hF σ hσ).symm x) =
      x.1 := by simp [projectiveProjection]


/-- The two usable image types in a five-element projective group. -/
@[expose] def PositionedImage (K : Type*) [Field K] (B : Subgroup (PGL2 K)) : Prop :=
  Nat.card B = 2 ∨ (Nat.card B = 4 ∧
    ¬ B ≤ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range)

/-- A nontrivial rank-one actor generates through the whole-group E2 member. -/
theorem projective_actor_generation_of_card_two (K : Type*) [Field K] [Finite K]
    [Finite (PGL2 K)] (hK : Nat.card K = 5)
    (T : Sylow 2 (PGL2 K)) (B : Subgroup (PGL2 K))
    (hB : IsElementaryAbelian 2 B) (hBT : B ≤ (T : Subgroup (PGL2 K)))
    (hcard : Nat.card B = 2) :
    eSubgroup 1 (T : Subgroup (PGL2 K)) B ⊔ (T : Subgroup (PGL2 K)) = ⊤ := by
  let i : PSL2 K →* PGL2 K := ProjectiveSpecialLinearGroup.toPGL
  have hi : Function.Injective i := ProjectiveSpecialLinearGroup.toPGL_injective
  have hq : IsOddPrimePower (Nat.card K) :=
    ⟨5, 1, by decide, by decide, le_rfl, by simpa using hK⟩
  have hc : 3 < Nat.card K := by omega
  have hindex : i.range.index = 2 := pgl2_psl2Range_index_eq_two K hq
  let : i.range.Normal := normal_of_index_eq_two hindex
  let : IsSimpleGroup (PSL2 K) := ProjectiveSpecialLinearGroup.rank_two_simple hc
  let : Group.IsPerfect (PSL2 K) := psl2_isPerfect_of_card_gt_three K hc
  let : IsSimpleGroup i.range := (MonoidHom.ofInjective hi).symm.isSimpleGroup
  let : Group.IsPerfect i.range := Group.IsPerfect.ofSurjective
    (f := (MonoidHom.ofInjective hi).toMonoidHom) (MonoidHom.ofInjective hi).surjective
  have hC : centralizer (i.range : Set (PGL2 K)) = ⊥ :=
    pgl2_psl2Range_centralizer_eq_bot K hq
  have hcore : pCore 2 (PGL2 K) = ⊥ :=
    Theory.GroupTheory.SimpleSocle.pCore_eq_bot
      (Theory.GroupTheory.SimpleSocle.radical_eq_bot i.range hC) 2
  let : Theory.GroupTheory.IsQuasisimple (PSL2 K) := ⟨
    ((QuotientGroup.quotientMulEquivOfEq (psl2_center_eq_bot K)).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  have hfit := Theory.GroupTheory.generalizedFitting_eq_range_of_quasisimple_index_two
    i hi hindex hcore
  let e : Theory.GroupTheory.generalizedFitting (PGL2 K) ≃* PSL2 K :=
    (MulEquiv.subgroupCongr hfit).trans (MonoidHom.ofInjective hi).symm
  let : IsSimpleGroup (Theory.GroupTheory.generalizedFitting (PGL2 K)) := e.isSimpleGroup
  let : Group.IsPerfect (Theory.GroupTheory.generalizedFitting (PGL2 K)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hquot : IsPGroup 2 (PGL2 K ⧸ i.range) :=
    IsPGroup.of_card (n := 1) (by simpa only [← index_eq_card, pow_one] using hindex)
  have hgen : Theory.GroupTheory.generalizedFitting (PGL2 K) ⊔
      (T : Subgroup (PGL2 K)) = ⊤ := by
    rw [hfit, sup_comm]
    exact T.sup_eq_top_of_quotient_isPGroup i.range hquot
  let := hB
  have hne : B ≠ ⊥ := by
    intro h
    simp [h] at hcard
  have hr : Group.rank B ≤ 1 :=
    IsElementaryAbelian.rank_le_of_card_le (p := 2) B (by simpa using hcard.le)
  have hmem := ValuesEvenClassical.RankOneUpper.isEMemberAt_top_of_simple_generalizedFitting
    (Group.IsPerfect.not_isMulCommutative _) T hgen T B hB hBT hne hr
  exact top_unique ((show (⊤ : Subgroup (PGL2 K)) ≤ eSubgroup 1 (T : Subgroup _) B
    from le_sSup hmem).trans le_sup_left)

/-- The precise permitted smaller-group input. -/
@[expose] def FiveGeneration : Prop :=
  ∀ (U : Sylow 2 (Equiv.Perm (Fin 5))) (B : Subgroup (Equiv.Perm (Fin 5))),
    IsElementaryAbelian 2 B → Nat.card B = 4 → B ≤ (U : Subgroup _) →
    ¬ B ≤ alternatingGroup (Fin 5) →
    eSubgroup 1 (U : Subgroup _) B ⊔ (U : Subgroup _) = ⊤

/-- Transport the positioned S5 input only after marking the actual PSL2 layer. -/
theorem projective_actor_generation_of_position (K : Type*) [Field K] [Finite K]
    [Finite (PGL2 K)] (hK : Nat.card K = 5)
    (e : PGL2 K ≃* Equiv.Perm (Fin 5))
    (he : (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
      e.toMonoidHom = alternatingGroup (Fin 5)) (hfive : FiveGeneration)
    (T : Sylow 2 (PGL2 K)) (B : Subgroup (PGL2 K))
    (hB : IsElementaryAbelian 2 B) (hBT : B ≤ (T : Subgroup (PGL2 K)))
    (hpos : PositionedImage K B) :
    eSubgroup 1 (T : Subgroup (PGL2 K)) B ⊔ (T : Subgroup (PGL2 K)) = ⊤ := by
  rcases hpos with hc | ⟨hc, hn⟩
  · exact projective_actor_generation_of_card_two K hK T B hB hBT hc
  · let := hB
    have hcard : Nat.card (B.map e.toMonoidHom) = 4 :=
      (Nat.card_congr (B.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm.trans hc
    have hnot : ¬ B.map e.toMonoidHom ≤ alternatingGroup (Fin 5) := by
      intro h
      apply hn
      rw [← he] at h
      exact (map_le_map_iff_of_injective e.injective).mp h
    have hg := hfive (T.mapSurjective (f := e.toMonoidHom) e.surjective)
      (B.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom) hcard
      (map_mono hBT) hnot
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, map_eSubgroup_equiv, map_top_of_surjective e.toMonoidHom e.surjective]
    exact hg


/-- Local actor generation gives containment, using the literal Sylow intersection
and E.1.8 for each local member. No weak-closure hypothesis is needed here. -/
theorem overgroup_le_of_actor_generation (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) {Ω : Set (Subgroup G)}
    (hΩ : IsElementaryFamily Ω) (A : Subgroup G) (hA : A ∈ Ω)
    (hAT : A ≤ (T : Subgroup G))
    (hgen : eSubgroup 1 ((T : Subgroup G).subgroupOf H) (A.subgroupOf H) ⊔
      (T : Subgroup G).subgroupOf H = ⊤) :
    H ≤ eFamilySubgroup 1 (T : Subgroup G) Ω ⊔ (T : Subgroup G) := by
  let := hΩ.1 A hA
  have hEM : (eSubgroup 1 ((T : Subgroup G).subgroupOf H) (A.subgroupOf H)).map
      H.subtype ≤ eFamilySubgroup 1 (T : Subgroup G) Ω := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro D hD
    apply map_le_iff_le_comap.mp
    have hd := hD.inherit T A H hAT ((tau_le _ _).trans hTH)
    exact (show D.map H.subtype ≤ eSubgroup 1 (T : Subgroup G) A from le_sSup hd).trans
      (le_iSup_of_le (⟨A, hA, hAT⟩ : {B : Subgroup G // B ∈ Ω ∧ B ≤ (T : Subgroup G)})
        le_rfl)
  have hg := congrArg (map H.subtype) hgen
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map, range_subtype] at hg
  rw [← hg]
  exact sup_le (hEM.trans le_sup_left) le_sup_right

/-- A positioned projective image puts the full local overgroup into the
ambient E-family join T. The quotient kernel is retained as a normal two-group. -/
theorem overgroup_le_of_positioned_image (K : Type*) [Field K] [Finite K]
    [Finite (PGL2 K)] (hK : Nat.card K = 5)
    (e : PGL2 K ≃* Equiv.Perm (Fin 5))
    (he : (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
      e.toMonoidHom = alternatingGroup (Fin 5)) (hfive : FiveGeneration)
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (q : H →* PGL2 K) (hq : Function.Surjective q) (hker : IsPGroup 2 q.ker)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (A : Subgroup G) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    (hpos : PositionedImage K ((A.subgroupOf H).map q)) :
    H ≤ eFamilySubgroup 1 (T : Subgroup G) Ω ⊔ (T : Subgroup G) := by
  let := hΩ.1 A hA
  let : IsElementaryAbelian 2 (A.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf (hAT.trans hTH)
  let R := T.subtype hTH
  have hAR : A.subgroupOf H ≤ (R : Subgroup H) := comap_mono hAT
  have hg := projective_actor_generation_of_position K hK e he hfive
    (R.mapSurjective (f := q) hq) ((A.subgroupOf H).map q)
    (IsElementaryAbelian.map q) (map_mono hAR) hpos
  exact overgroup_le_of_actor_generation T H hTH hΩ A hA hAT
    (actor_generation_of_two_kernel q hq hker R (A.subgroupOf H) hAR hg)

/-- Apply the lifting theorem to the actual marked pure-field centralizer. -/
theorem pureCentralizer_le_of_positioned_image (hF : Nat.card F = 5 ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) [Finite (innerModel F σ)]
    (e : PGL2 (FixedPoints.subfield (zpowers σ) F) ≃* Equiv.Perm (Fin 5))
    (he : (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
      (R := FixedPoints.subfield (zpowers σ) F)).range.map e.toMonoidHom =
        alternatingGroup (Fin 5)) (hfive : FiveGeneration)
    (T : Sylow 2 (innerModel F σ))
    (hTC : (T : Subgroup (innerModel F σ)) ≤ centralizer ({pure σ} : Set (innerModel F σ)))
    {Ω : Set (Subgroup (innerModel F σ))} (hΩ : IsElementaryFamily Ω)
    (A : Subgroup (innerModel F σ)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hpos : PositionedImage (FixedPoints.subfield (zpowers σ) F)
      ((A.subgroupOf (centralizer ({pure σ} : Set (innerModel F σ)))).map
        (projectiveProjection hF σ hσ))) :
    centralizer ({pure σ} : Set (innerModel F σ)) ≤
      eFamilySubgroup 1 (T : Subgroup (innerModel F σ)) Ω ⊔ (T : Subgroup _) := by
  let : Finite (PGL2 (FixedPoints.subfield (zpowers σ) F)) := Finite.of_surjective
    ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hc := fixedSubfield_card hF σ ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  exact overgroup_le_of_positioned_image _ hc e he hfive T _ hTC
    (projectiveProjection hF σ hσ) (projectiveProjection_surjective hF σ hσ)
    (projectiveProjection_two_kernel hF σ hσ) hΩ A hA hAT hpos

omit [Finite G] [Finite Q] in
/-- Change coordinates in the domain without dropping the kernel. -/
private theorem two_kernel_comp_equiv {H : Type*} [Group H]
    (q : G →* Q) (hker : IsPGroup 2 q.ker) (e : H ≃* G) :
    IsPGroup 2 (q.comp e.toMonoidHom).ker := by
  let j : (q.comp e.toMonoidHom).ker →* q.ker :=
    (e.toMonoidHom.comp (q.comp e.toMonoidHom).ker.subtype).codRestrict q.ker
      (fun x => x.property)
  apply hker.of_injective j
  intro x y h
  exact Subtype.ext (e.injective (congrArg Subtype.val h))

/-- The finite geometry still required. It positions an original family actor
in an actual involution centralizer outside the proposed overgroup. The image
uses the fixed projective coordinate after a genuine centralizer isomorphism.
This definition asserts neither its own existence nor any E-generation fact. -/
@[expose] def HasPositionedCentralizerGeometry (hF : Nat.card F = 5 ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) [Finite (innerModel F σ)] : Prop :=
  ∃ T : Sylow 2 (innerModel F σ),
    ∀ Ω : Set (Subgroup (innerModel F σ)), IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ →
        Group.rank A = 2 ∨ Group.rank A = 3) →
      ∀ M : Subgroup (innerModel F σ), IsCoatom M → (T : Subgroup _) ≤ M →
        normalizer (weakClosure (T : Subgroup _) Ω : Set (innerModel F σ)) ≤ M →
        ∃ A : Subgroup (innerModel F σ), A ∈ Ω ∧ A ≤ (T : Subgroup _) ∧
          ∃ x : innerModel F σ, orderOf x = 2 ∧
            (T : Subgroup _) ≤ centralizer ({x} : Set (innerModel F σ)) ∧
            ∃ e : centralizer ({x} : Set (innerModel F σ)) ≃*
                centralizer ({pure σ} : Set (innerModel F σ)),
              PositionedImage (FixedPoints.subfield (zpowers σ) F)
                ((A.subgroupOf (centralizer ({x} : Set (innerModel F σ)))).map
                  ((projectiveProjection hF σ hσ).comp e.toMonoidHom)) ∧
              ¬ centralizer ({x} : Set (innerModel F σ)) ≤ M

/-- Conditional assembly for the characteristic-five branch. The two remaining
geometric inputs have distinct outputs: a marked five-point action and placement
plus fusion in the 25-element model. The smaller-group premise is exactly hfive.
All original families, rank-three actors and E1/E2 conditions survive lifting. -/
theorem escape_of_marked_projective_and_geometry (hF : Nat.card F = 5 ^ 2)
    (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) [Finite (innerModel F σ)]
    (e : PGL2 (FixedPoints.subfield (zpowers σ) F) ≃* Equiv.Perm (Fin 5))
    (hgeometry : HasPositionedCentralizerGeometry hF σ
      ((orderOf_eq_prime_iff (x := σ)).mpr ⟨hsq, hne⟩))
    (hfive : FiveGeneration) :
    ∀ T : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt T := by
  classical
  let : Finite (PGL2 (FixedPoints.subfield (zpowers σ) F)) := Finite.of_surjective
    ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hσ : orderOf σ = 2 := (orderOf_eq_prime_iff (x := σ)).mpr ⟨hsq, hne⟩
  have hc := fixedSubfield_card hF σ hsq hne
  have he := Theory.PSL2.pgl2_five_equiv_maps_psl _ hc e
  obtain ⟨T, hT⟩ := hgeometry
  apply largeFamilyEscapeAt_of_sylow (T := T)
  apply largeFamilyEscapeAt_of_rank_two_or_three_witnesses (by decide : Nat.Prime 5)
    (by decide) hF (innerModel F σ) T
  intro Ω hΩ hr M hM hTM hNM
  obtain ⟨A, hA, hAT, x, _, hTx, f, hpos, hCM⟩ := hT Ω hΩ hr M hM hTM hNM
  let q := (projectiveProjection hF σ hσ).comp f.toMonoidHom
  have hq : Function.Surjective q :=
    (projectiveProjection_surjective hF σ hσ).comp f.surjective
  have hk : IsPGroup 2 q.ker :=
    two_kernel_comp_equiv _ (projectiveProjection_two_kernel hF σ hσ) f
  have hC := overgroup_le_of_positioned_image _ hc e he hfive T _ hTx q hq hk
    hΩ A hA hAT hpos
  by_contra h
  have hEM : eFamilySubgroup 1 (T : Subgroup (innerModel F σ)) Ω ≤ M := by
    apply iSup_le
    intro B
    apply sSup_le
    intro H hH
    by_contra hHM
    exact h ⟨B.val, B.property.1, B.property.2, H, hH, hHM⟩
  exact hCM (hC.trans (sup_le hEM hTM))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive
