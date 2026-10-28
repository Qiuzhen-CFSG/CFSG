module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStar
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.EvenPointCoreNormal

/-!
# The original nonabelian closure has the full even point-core image

The literal natural quotient sends L₁ to the marked A₄ residual. Normality
in H and commutator generation place U_H in O₂(L₁). Its image cannot be
trivial, since the faithful natural action would then make U_H commute
with its generating seed. The cubic action on the even four-group forces
the image to be the whole point core.

These are the ordinary n=6 quotient conclusions of13.5.14(2), obtained
before any A₅ block or quaternion conclusion. The original ordinary A₆
quotient and13.5.7(b) seed identity remain earlier-source inputs.

Source: Aschbacher–Smith,13.5.14(1–2), printed p.919.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePointCore
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
include d

theorem local_residual_marking (h : D.Hypothesis) (a : alternatingGroup (Fin 6))
    (ha : Section07.NaturalAction.image d D.V₁ = move a.val canonicalLine) :
    (D.L₁.subgroupOf D.L).map (localMap d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.K.map (MulAut.conj a.val).toMonoidHom := by
  rw [SourceStar.original_residual_image d h]
  have he : alternatingGroup (Fin 6) ⊓ flagStabilizer (Section07.NaturalAction.image d D.V₁) =
      L1.map (MulAut.conj a.val).toMonoidHom := by
    rw [ha,flagStabilizer_move,flagStabilizer_line,L1,
      map_inf _ _ _ (MulAut.conj a.val).injective,conjugate_alternating]
    exact inf_comm _ _
  dsimp only
  rw [he, ← map_embedded_pResidual, residual_L1]

theorem closure_image_nontrivial (h : D.Hypothesis) (hUL : D.UH ≤ D.L)
    (hn : ¬ IsMulCommutative D.UH) : (D.UH.subgroupOf D.L).map (localMap d) ≠ ⊥ := by
  intro he
  have hc : D.UH ≤ centralizer (D.V : Set G) := by
    intro u hu v hv
    let ul : D.L := ⟨u,hUL hu⟩
    let vv : D.V := ⟨v,hv⟩
    have hq : localMap d ul = 1 := by
      have hh := mem_map_of_mem (localMap d) (show ul ∈ D.UH.subgroupOf D.L from hu)
      rw [he] at hh
      exact hh
    have hh := d.conjugation ul vv
    change (d.coordinate _).toAdd = naturalRepresentation (Fin 6) (localMap d ul) _ at hh
    rw [hq,map_one] at hh
    have hvv := d.coordinate.injective (Multiplicative.toAdd.injective hh)
    have hx : u*v*u⁻¹=v := congrArg Subtype.val hvv
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  exact hn ((conjugateSpanBy_commutative_iff D.Vplus D.H).mpr
    (h.plus_le.trans (le_centralizer_iff.mp hc)))

theorem closure_image_eq_point_core (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH)
    (a : alternatingGroup (Fin 6))
    (ha : Section07.NaturalAction.image d D.V₁ = move a.val canonicalLine) :
    (D.UH.subgroupOf D.L).map (localMap d) =
      pointCoreEven.map (MulAut.conj a.val).toMonoidHom := by
  let A := (D.UH.subgroupOf D.L).map (localMap d)
  let R := (D.L₁.subgroupOf D.L).map (localMap d)
  have hLL : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  have hr : R = Theory.SpecificGroups.SymmetricSix.BinaryFlags.K.map
      (MulAut.conj a.val).toMonoidHom := local_residual_marking d h a ha
  have hcore : (D.L₁.pCoreIn 2).subgroupOf D.L = (D.L₁.subgroupOf D.L).pCoreIn 2 := by
    apply map_injective D.L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 D.L₁).trans hLL),
      map_pCoreIn_of_injective 2 _ D.L.subtype D.L.subtype_injective,
      map_subgroupOf_eq_of_le hLL]
  have hle : A ≤ pointCoreEven.map (MulAut.conj a.val).toMonoidHom := by
    have hh := map_mono (f := localMap d) (subgroupOf_mono D.L (closure_reduction h hseed hn).2.1)
    rw [hcore, map_pCoreIn_of_ker_isPGroup (localMap d) (SourceStar.local_kernel_two d e)] at hh
    change A ≤ R.pCoreIn 2 at hh
    rw [hr, ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj a.val).injective,
      K_core_eq_pointCoreEven] at hh
    exact hh
  have hnorm : R ≤ normalizer (A : Set (Equiv.Perm (Fin 6))) := by
    have hN : D.L₁.subgroupOf D.L ≤ normalizer (D.UH.subgroupOf D.L : Set D.L) := by
      intro l hl
      apply mem_normalizer_iff.mpr
      intro u
      exact mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H
        ((le_sup_left.trans h.local_le) hl)) u.val
    exact (map_mono hN).trans ((D.UH.subgroupOf D.L).le_normalizer_map (localMap d))
  let c := (MulAut.conj a.val⁻¹).toMonoidHom
  have hc (X : Subgroup (Equiv.Perm (Fin 6))) :
      (X.map (MulAut.conj a.val).toMonoidHom).map c = X := by
    rw [map_map]
    have he : c.comp (MulAut.conj a.val).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change a.val⁻¹*(a.val*x*a.val⁻¹)*(a.val⁻¹)⁻¹=x
      group
    rw [he,map_id]
  have hback : A.map c = pointCoreEven := by
    apply EvenPointCoreNormal.eq_pointCore_of_normalized
    · exact (map_mono hle).trans_eq (hc pointCoreEven)
    · intro hz
      have hb : A = ⊥ := (map_eq_bot_iff_of_injective A (f := c) (MulAut.conj a.val⁻¹).injective).mp hz
      exact closure_image_nontrivial d h (closure_reduction h hseed hn).2.2 hU hb
    · have hh := (map_mono (f := c) hnorm).trans (A.le_normalizer_map c)
      rw [hr,hc] at hh
      exact hh
  apply map_injective (f := c) (MulAut.conj a.val⁻¹).injective
  rw [hback,hc]

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePointCore
end
