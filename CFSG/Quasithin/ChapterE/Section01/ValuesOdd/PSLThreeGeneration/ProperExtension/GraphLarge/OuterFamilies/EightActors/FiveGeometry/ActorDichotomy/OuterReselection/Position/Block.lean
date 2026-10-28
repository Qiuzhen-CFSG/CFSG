module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Coordinates
import all CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.QuotientModel
public import GorensteinWalter.PGL2DeterminantSquare

/-!
# Marked blocks in the fixed prime-five centralizer

The determinant-corrected GL₂ block acts on the last two coordinates, so its
range is precisely the normal inner centralizer of the fixed involution.
The radical of this normal subgroup is its intersection with the full
centralizer radical. Thus the induced projective map has trivial kernel.
The allowed S₅ identification makes this marked PGL₂(5) map surjective.

This is the block and kernel calculation for the fixed-actor branch of
Aschbacher--Smith E.1.14(7), p.214, with the literal quotient conventions
of E.1.2 and E.1.10, pp.210--211. The internal import of QuotientModel reuses
its private radical calculation without changing that module's API.
Imported matrix models retain their attribution and LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory Matrix GorensteinWalter
open scoped MatrixGroups Matrix
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Position
open FiveSourceAudit PSUThreeGeneration
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : IsSimpleGroup PSL(3, ZMod 5) := Atlas.psl_simple_high_rank 3 (by decide)

abbrev C := centralizer ({centralElement} : Set Model)

@[expose] def cycle : SL(3, ZMod 5) := ⟨!![0,0,1;1,0,0;0,1,0], by decide +kernel⟩

@[expose] def block : GL (Fin 2) (ZMod 5) →* SL(3, ZMod 5) :=
  (MulAut.conj cycle).toMonoidHom.comp (SL3.blockEmbedding (ZMod 5))

theorem block_injective : Function.Injective block :=
  (MulAut.conj cycle).injective.comp (SL3.blockEmbedding_injective _)

theorem block_formula (A : GL (Fin 2) (ZMod 5)) :
    (block A).val = !![↑(A.det⁻¹),0,0;0,A 0 0,A 0 1;0,A 1 0,A 1 1] := by
  have hi : cycle⁻¹ = (⟨!![0,1,0;0,0,1;1,0,0], by decide +kernel⟩ : SL(3, ZMod 5)) := by
    apply inv_eq_of_mul_eq_one_right
    decide +kernel
  change (cycle * SL3.blockEmbedding (ZMod 5) A * cycle⁻¹).val = _
  rw [hi]
  change (!![0,0,1;1,0,0;0,1,0] * SL3.blockMatrix (ZMod 5) A) *
    !![0,1,0;0,0,1;1,0,0] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SL3.blockMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem block_range : block.range = centralizer ({secondDiagonal} : Set SL(3, ZMod 5)) := by
  rw [block, MonoidHom.range_comp, SL3.blockEmbedding_range _ (by decide)]
  have he : MulAut.conj cycle (SL3.standardInvolution (ZMod 5)) = secondDiagonal := by decide +kernel
  simpa only [MulEquiv.toMonoidHom_eq_coe, he] using
    ActorDichotomy.map_elementCentralizer (MulAut.conj cycle) (SL3.standardInvolution (ZMod 5))

@[expose] noncomputable def embed : GL (Fin 2) (ZMod 5) →* C :=
  (FiveSourceAudit.innerSL.comp block).codRestrict C (by
    intro A
    apply mem_centralizer_singleton_iff.mpr
    change FiveSourceAudit.innerSL (block A) * FiveSourceAudit.innerSL secondDiagonal =
      FiveSourceAudit.innerSL secondDiagonal * FiveSourceAudit.innerSL (block A)
    rw [← map_mul, ← map_mul]
    exact congrArg FiveSourceAudit.innerSL
      (mem_centralizer_singleton_iff.mp (block_range ▸ (show block A ∈ block.range from ⟨A,rfl⟩))))

theorem embed_injective : Function.Injective embed := by
  intro a b h
  exact block_injective (innerSL_injective (congrArg (fun x : C => (x : Model)) h))

theorem embed_range : embed.range = FiveSourceAudit.inner.subgroupOf C := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change FiveSourceAudit.innerSL (block a) ∈ FiveSourceAudit.inner
    rw [← innerSL_range]
    exact ⟨_,rfl⟩
  · intro hx
    obtain ⟨a,ha⟩ := (show (x : Model) ∈ FiveSourceAudit.innerSL.range by
      rw [innerSL_range]; exact hx)
    have hc : a ∈ centralizer ({secondDiagonal} : Set SL(3, ZMod 5)) := by
      apply mem_centralizer_singleton_iff.mpr
      apply innerSL_injective
      simpa only [map_mul, ha, centralElement] using mem_centralizer_singleton_iff.mp x.property
    rw [← block_range] at hc
    obtain ⟨b,rfl⟩ := hc
    exact ⟨b,Subtype.ext ha⟩

instance embed_range_normal : embed.range.Normal := by
  rw [embed_range]
  exact inferInstanceAs ((innerPart (ZMod 5)).subgroupOf C).Normal

@[expose] noncomputable def embedEquiv : GL (Fin 2) (ZMod 5) ≃* embed.range :=
  MonoidHom.ofInjective embed_injective

theorem radical_gl : solvableRadical (GL (Fin 2) (ZMod 5)) = center (GL (Fin 2) (ZMod 5)) := by
  let f : GL (Fin 2) (ZMod 5) →* PGL2 (ZMod 5) := ProjGenLinGroup.mk
  let : Finite (PGL2 (ZMod 5)) := Finite.of_surjective f ProjGenLinGroup.mk_surjective
  let : Group.IsSolvable f.ker := by
    rw [show f.ker = center (GL (Fin 2) (ZMod 5)) from ProjGenLinGroup.ker_mk]
    exact Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have h := comap_solvableRadical_eq_of_solvable_ker f ProjGenLinGroup.mk_surjective
  rw [FiveQuotientModel.pgl_radical (ZMod 5) (by simp), MonoidHom.comap_bot, ProjGenLinGroup.ker_mk] at h
  exact h.symm

theorem centralizer_eq_supplement :
    centralizerResidualOvergroup standardSylow centralElement = C :=
  FiveQuotientModel.supplement_eq_centralizer (ZMod 5) (by simp)
    centralElement_mem_inner centralElement_orderOf standardSylow_le_centralizer

abbrev Q := C ⧸ solvableRadical C

noncomputable abbrev q : C →* Q := QuotientGroup.mk' (solvableRadical C)

theorem embed_radical (A : GL (Fin 2) (ZMod 5)) :
    embed A ∈ solvableRadical C ↔ A ∈ center (GL (Fin 2) (ZMod 5)) := by
  change embedEquiv A ∈ (solvableRadical C).subgroupOf embed.range ↔ _
  rw [radical_subgroupOf_normal, ← map_solvableRadical_equiv embedEquiv, radical_gl]
  constructor
  · rintro ⟨B,hB,hBA⟩
    exact embedEquiv.injective hBA ▸ hB
  · intro h
    exact ⟨A,h,rfl⟩

theorem quotient_embed_kernel :
    (q.comp embed).ker = center (GL (Fin 2) (ZMod 5)) := by
  ext A
  change q (embed A) = 1 ↔ _
  exact (QuotientGroup.eq_one_iff (embed A)).trans (embed_radical A)

@[expose] noncomputable def projective : PGL2 (ZMod 5) →* Q :=
  QuotientGroup.lift (center (GL (Fin 2) (ZMod 5))) (q.comp embed)
    (le_of_eq quotient_embed_kernel.symm)

theorem projective_mk (A : GL (Fin 2) (ZMod 5)) :
    projective (ProjGenLinGroup.mk A) = q (embed A) := rfl

theorem projective_injective : Function.Injective projective :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr quotient_embed_kernel.symm

theorem projective_surjective (hmodel : Nonempty (Q ≃* Equiv.Perm (Fin 5))) :
    Function.Surjective projective := by
  let : Finite (PGL2 (ZMod 5)) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  apply ((Nat.bijective_iff_injective_and_card projective).mpr
    ⟨projective_injective, ?_⟩).surjective
  rw [Nat.card_congr hmodel.some.toEquiv, Nat.card_perm, pgl2_card_formula, Nat.card_zmod]
  norm_num [Nat.card_eq_fintype_card]

theorem center_quotient : center Q = ⊥ := by
  apply le_bot_iff.mp
  calc
    center Q ≤ solvableRadical Q := le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a)))
    _ = ⊥ := solvableRadical_quotient_solvableRadical

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Position
