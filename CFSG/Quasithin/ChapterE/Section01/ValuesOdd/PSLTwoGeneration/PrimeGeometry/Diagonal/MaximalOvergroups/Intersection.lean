module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OvergroupModels
public import GorensteinWalter.PGL2InnerAction
public import GorensteinWalter.PSL2DihedralSylow
public import BenderSuzuki.External.Hall.Basic
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# The literal inner intersection of a Sylow overgroup in PGL₂

The canonical PSL₂ image has index two. A subgroup containing an ambient
Sylow two-subgroup supplements this image, and its inner intersection
therefore has index two in it. Restriction to the normal PSL₂ image also
supplies a Sylow subgroup of PSL₂ inside the intersection.

These are the embedding and index facts used when applying Dickson's
classification in the prime-field calculation for Aschbacher--Smith
E.1.14(6), printed p.214. No maximal-subgroup classification is assumed.
-/

noncomputable section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups

open Subgroup GorensteinWalter

variable {F : Type*} [Field F]

/-- The actual preimage of `M` under the canonical PSL₂ inclusion. -/
public abbrev inner (M : Subgroup (PGL2 F)) : Subgroup (PSL2 F) :=
  M.comap (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))

/-- The canonical PSL₂ subgroup of PGL₂. -/
public abbrev innerRange (F : Type*) [Field F] : Subgroup (PGL2 F) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range

/-- The inner intersection viewed as a subgroup of `M`. -/
public abbrev innerIn (M : Subgroup (PGL2 F)) : Subgroup M :=
  (innerRange F).subgroupOf M

/-- The equivalence retains the canonical projective inclusion. -/
@[expose] public def innerEquiv (M : Subgroup (PGL2 F)) : inner M ≃* innerIn M :=
  MulEquiv.ofBijective
    ({
      toFun := fun x => ⟨⟨Matrix.ProjectiveSpecialLinearGroup.toPGL x.val,
          x.property⟩, ⟨x.val, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp } : inner M →* innerIn M)
    ⟨fun x y h => Subtype.ext
        (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
          (congrArg (fun z : innerIn M => z.val.val) h)),
      fun y => by
        obtain ⟨x, hx⟩ := y.property
        refine ⟨⟨x, ?_⟩, ?_⟩
        · change Matrix.ProjectiveSpecialLinearGroup.toPGL x ∈ M
          rw [hx]
          exact y.val.property
        · exact Subtype.ext (Subtype.ext hx)⟩

public theorem innerEquiv_val (M : Subgroup (PGL2 F)) (x : inner M) :
    (innerEquiv M x).val.val = Matrix.ProjectiveSpecialLinearGroup.toPGL x.val := rfl

variable [Finite F]

private theorem innerRange_normal (hF : IsOddPrimePower (Nat.card F)) :
    (innerRange F).Normal :=
  Subgroup.normal_of_index_eq_two (pgl2_psl2Range_index_eq_two F hF)

private instance finitePGL : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- Any ambient Sylow overgroup supplements the canonical PSL₂ image. -/
public theorem sup_innerRange_eq_top (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hTM : (T : Subgroup _) ≤ M) :
    M ⊔ innerRange F = ⊤ := by
  let : (innerRange F).Normal := innerRange_normal hF
  have hquot : IsPGroup 2 (PGL2 F ⧸ innerRange F) :=
    IsPGroup.of_card (n := 1) (by
      change (innerRange F).index = 2 ^ 1
      simpa using pgl2_psl2Range_index_eq_two F hF)
  apply top_unique
  rw [← T.sup_eq_top_of_quotient_isPGroup (innerRange F) hquot]
  exact sup_le_sup hTM le_rfl

/-- The inner intersection has relative index two, not merely index at most two. -/
public theorem innerIn_index (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hTM : (T : Subgroup _) ≤ M) :
    (innerIn M).index = 2 := by
  let : (innerRange F).Normal := innerRange_normal hF
  change (innerRange F).relIndex M = 2
  rw [← Subgroup.relIndex_sup_right M (innerRange F), sup_innerRange_eq_top hF T M hTM,
    Subgroup.relIndex_top_right]
  exact pgl2_psl2Range_index_eq_two F hF

/-- Normality is inside `M`; the intersection need not be normal in PSL₂. -/
public theorem innerIn_normal (hF : IsOddPrimePower (Nat.card F))
    (M : Subgroup (PGL2 F)) : (innerIn M).Normal := by
  let : (innerRange F).Normal := innerRange_normal hF
  exact Subgroup.normal_subgroupOf

/-- The whole overgroup has twice the order of its literal inner intersection. -/
public theorem card_eq_two_mul_inner (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hTM : (T : Subgroup _) ≤ M) :
    Nat.card M = 2 * Nat.card (inner M) := by
  rw [Nat.card_congr (innerEquiv M).toEquiv]
  simpa only [innerIn_index hF T M hTM] using
    (Subgroup.index_mul_card (innerIn M)).symm

/-- A proper ambient Sylow overgroup has proper inner intersection. -/
public theorem inner_ne_top (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤) : inner M ≠ ⊤ := by
  intro hi
  have hJM : innerRange F ≤ M := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ inner M := hi ▸ mem_top x
    exact hx
  exact hM (by simpa only [sup_of_le_left hJM] using sup_innerRange_eq_top hF T M hTM)

/-- Restrict the given Sylow subgroup through the normal PSL₂ image and the
canonical equivalence, preserving the literal intersection. -/
public theorem exists_inner_sylow (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) :
    ∃ S : Sylow 2 (PSL2 F), (S : Subgroup (PSL2 F)) = inner (T : Subgroup (PGL2 F)) := by
  let : (innerRange F).Normal := innerRange_normal hF
  let Q := BenderSuzuki.External.hallSylowSubgroupOfNormal T (innerRange F)
  let e := psl2EquivToPGLRange F
  let S := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨S, ?_⟩
  change (Q : Subgroup (innerRange F)).map e.symm.toMonoidHom = inner (T : Subgroup _)
  rw [BenderSuzuki.External.hallSylowSubgroupOfNormal_coe T (innerRange F)]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change Matrix.ProjectiveSpecialLinearGroup.toPGL (e.symm y) ∈ (T : Subgroup _)
    have he : Matrix.ProjectiveSpecialLinearGroup.toPGL (e.symm y) = y.val := by
      simpa only [e, psl2EquivToPGLRange_val] using congrArg Subtype.val (e.apply_symm_apply y)
    rwa [he]
  · intro hx
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    change (e x).val ∈ (T : Subgroup (PGL2 F))
    change Matrix.ProjectiveSpecialLinearGroup.toPGL x ∈ (T : Subgroup (PGL2 F)) at hx
    simpa only [e, psl2EquivToPGLRange_val] using hx

/-- The PSL₂ intersection of an ambient Sylow overgroup contains a PSL₂ Sylow. -/
public theorem exists_sylow_le_inner (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hTM : (T : Subgroup _) ≤ M) :
    ∃ S : Sylow 2 (PSL2 F), (S : Subgroup _) ≤ inner M := by
  obtain ⟨S, hS⟩ := exists_inner_sylow hF T
  exact ⟨S, hS ▸ Subgroup.comap_mono hTM⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups
