module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary.Model
public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.Calculation

/-!
# Binary hexad recognition and transport of the core-square calculation

A calculation in a genuinely isomorphic fixed-hexad extension transfers to the
ambient group through fixedHexadCore_map. The distinguished line is the image
of Z(K); no replacement of this line by the local center is made. The proof
retains the literal central quotient and O2(O²(C_K(u))).

The native section is lifted and its radical identified with the augmentation
core in Binary.Model. The proved residual/core identities in the explicit
model now establish I.2.2(6b), conditional only on the earlier perfectness
restriction and A₆ covering identification retained by the source assembly.

Source: Aschbacher–Smith, I.2.2(6), printed pp.410 and 412, combined
manuscript of 1 March 2004.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
variable {K : Type*} [Group K] [Finite K]

/-- Transport a calculation through an actual model of the fixed hexad extension.
The line N must be the image of the ambient center, not the center of the model. -/
theorem uniqueSquare_of_fixedHexad_model
    (e : (K ⧸ center K) ≃* M22) (u : K)
    (hu : orderOf u = 2) (hun : u ∉ center K)
    {G : Type*} [Group G]
    (f : hexadPreimage e (m22FixedPoints (projection e u)) ≃* G)
    (N : Subgroup G)
    (hN : ((center K).subgroupOf (hexadPreimage e (m22FixedPoints (projection e u)))).map
      f.toMonoidHom = N)
    (hcalc : ∃! v : G,
      (f (fixedHexadElement e u))⁻¹ * v ∈ N ∧
      ∃ x ∈ centralizerResidualCore (f (fixedHexadElement e u)), x ^ 2 = v) :
    HasUniqueCoreSquareLift u := by
  let I := hexadPreimage e (m22FixedPoints (projection e u))
  let t : I := fixedHexadElement e u
  have hcore : (centralizerCore t).map f.toMonoidHom =
      centralizerResidualCore (f t) := map_centralizerResidualCore f t
  have hfiber (v : I) : (f t)⁻¹ * f v ∈ N ↔
      QuotientGroup.mk' (center K) v.val = QuotientGroup.mk' (center K) u := by
    rw [← map_inv, ← map_mul, ← hN]
    change t⁻¹ * v ∈ (((center K).subgroupOf I).map f.toMonoidHom).comap f.toMonoidHom ↔ _
    rw [comap_map_eq_self_of_injective f.injective]
    change u⁻¹ * v.val ∈ center K ↔ _
    exact QuotientGroup.eq.symm.trans eq_comm
  obtain ⟨v, ⟨hv, x, hx, hsq⟩, hvunique⟩ := hcalc
  have hx' : f.symm x ∈ centralizerCore t := by
    have : f (f.symm x) ∈ (centralizerCore t).map f.toMonoidHom := by
      rw [hcore, f.apply_symm_apply]
      exact hx
    change f.symm x ∈ ((centralizerCore t).map f.toMonoidHom).comap f.toMonoidHom at this
    rwa [comap_map_eq_self_of_injective f.injective] at this
  have hxK : (f.symm x).val ∈ centralizerCore u := by
    rw [← fixedHexadCore_map e u hu hun]
    exact mem_map_of_mem I.subtype hx'
  have hsqI : f.symm x ^ 2 = f.symm v := by rw [← map_pow, hsq]
  refine ⟨(f.symm v).val, ⟨?_, (f.symm x).val, hxK, congrArg Subtype.val hsqI⟩, ?_⟩
  · apply (hfiber (f.symm v)).mp
    rwa [f.apply_symm_apply]
  · rintro w ⟨hw, y, hy, hysq⟩
    rw [← fixedHexadCore_map e u hu hun] at hy
    obtain ⟨yI, hyI, rfl⟩ := hy
    change (yI : K) ^ 2 = w at hysq
    let wI : I := yI ^ 2
    have he : f wI = v := by
      apply hvunique
      refine ⟨(hfiber wI).mpr ?_, f yI, ?_, ?_⟩
      · simpa only [wI, Subgroup.coe_pow, hysq] using hw
      · rw [← hcore]
        exact mem_map_of_mem f.toMonoidHom hyI
      · exact (map_pow f yI 2).symm
    have hwval : wI.val = (f.symm v).val :=
      congrArg Subtype.val (f.injective (he.trans (f.apply_symm_apply v).symm))
    exact hysq.symm.trans hwval
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open BinaryPermutation.SixCoreExtension
universe u
variable {K : Type u} [Group K] [Finite K]

/-- I.2.2(6b) from perfectness of the one fixed-hexad preimage used in the proof.
The complement, module recognition, residual and two-core identities are all
discharged. The only other input is the earlier A₆ covering identification. -/
theorem hasUniqueCoreSquareLift_of_perfect_fixedHexad
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 2)
    (hcover : CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6)))
    (u : K) (hu : orderOf u = 2) (hun : u ∉ center K)
    [Group.IsPerfect (hexadPreimage e (m22FixedPoints (projection e u)))] :
    HasUniqueCoreSquareLift u := by
  obtain ⟨hB, hr, _⟩ := centralizer_le_fixedHexad e u hu hun
  obtain ⟨d⟩ := exists_hexadRecognition e hZ hB hcover
  let r : hexadRadical e (m22FixedPoints (projection e u)) := ⟨u, hr⟩
  have hv : BinaryPermutation.coreToNatural (Fin 6) (d.radicalEquiv r).toAdd ≠ 0 :=
    fun h => hun ((d.center_iff r).mpr h)
  have he : d.modelEquiv (fixedHexadElement e u) = vector (d.radicalEquiv r) :=
    d.modelEquiv_radical r
  apply uniqueSquare_of_fixedHexad_model e u hu hun d.modelEquiv centralLine d.modelEquiv_center
  rw [he]
  exact unique_square (d.radicalEquiv r).toAdd hv

/-- Every noncentral involution has the unique square required by I.2.2(6b).
`hperfect` is the earlier odd-index restriction (i); `hcover` is the earlier
A₆ covering input (1). All native hexad and binary-module premises are proved. -/
theorem hasUniqueCoreSquareLift
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 2)
    (hcover : CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6)))
    (hperfect : ∀ (B : Finset (Fin 22)), B ∈ m22Blocks → Group.IsPerfect (hexadPreimage e B))
    (u : K) (hu : orderOf u = 2) (hun : u ∉ center K) : HasUniqueCoreSquareLift u := by
  let := hperfect _ (centralizer_le_fixedHexad e u hu hun).1
  exact hasUniqueCoreSquareLift_of_perfect_fixedHexad e hZ hcover u hu hun

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary
