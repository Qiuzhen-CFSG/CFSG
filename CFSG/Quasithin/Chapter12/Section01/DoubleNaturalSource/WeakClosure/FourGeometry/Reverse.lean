module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry.FaithfulCore
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ReverseCommon

/-!
# The degree-four high-rank first-stage contradiction

The surviving six-dimensional core is pointwise faithful. Since its corank
is below r, the centralizer of the reverse normalizer normalizes the original
orbit. Core faithfulness identifies the two actual action kernels. The
forward kernel has rank three, while the reverse rank-four actor has fixed
rank one, two, or four. This closes the high-rank branch of 12.1.8.
All maps are the literal ambient conjugation actions.
Source: Aschbacher--Smith, 12.1.8, printed p.793 (PDF810).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryNaturalDual
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G}
  [IsElementaryAbelian 2 W]

theorem high_reverse_centralizer_eq
    (S : SourceSetup 4 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) {g : G}
    (C : ConjugateConfiguration W g 1 4)
    (hr : (4 : ℕ∞) ≤ globalR W)
    (hI : 4 ≤ rank (inducedAutomizer W (offenderNormalizer W g)))
    (hp : S.natural ⊓ generatedCore
      (S.representation.comp (inducedAutomizer W (offenderNormalizer W g)).subtype) 2 ≤
      S.fixed (inducedAutomizer W (offenderNormalizer W g) ⊓ componentLayer _))
    (hU : subgroupCorank W
      (W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) ≤ 2) :
    W.map (MulAut.conj g).toMonoidHom ⊓ centralizer
        ((W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) : Set G) =
      offenderNormalizer W g ⊓ centralizer (W : Set G) := by
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let U := W ⊓ normalizer (Wg : Set G)
  let I := inducedAutomizer W (offenderNormalizer W g)
  let := offender_inducedAutomizer_elementary W g
  change subgroupCorank W U ≤ 2 at hU
  have hCN : centralizer (U : Set G) ≤ normalizer (W : Set G) := by
    apply centralizer_le_normalizer_of_corank_lt_globalR (show U ≤ W from inf_le_left)
    apply lt_of_lt_of_le _ hr
    exact_mod_cast (show subgroupCorank W U < 4 by omega)
  apply le_antisymm
  · intro a ha
    have haN := hCN ha.2
    refine ⟨⟨ha.1,haN⟩,?_⟩
    let b : Automizer W := W.normalizerMonoidHom.rangeRestrict ⟨a,haN⟩
    have hb : b = 1 := by
      apply FourGeometry.source_core_faithful S I hI hp
      intro v hv
      rw [hρ] at hv ⊢
      have hvU : (v.toMul : G) ∈ U :=
        C.core_le 2 (by decide) ((ZeroClosure.mem_core_iff I 2 v).mpr hv)
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change a * (v.toMul : G) * a⁻¹ = (v.toMul : G)
      rw [← ha.2 _ hvU, mul_inv_cancel_right]
    intro v hv
    have he := congrArg (fun f : Automizer W => (f.val ⟨v,hv⟩ : G)) hb
    change a * v * a⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro a ha
    exact ⟨ha.1.1, fun u hu => ha.2 u hu.1⟩

theorem reverse_rank_le_four
    (S : SourceSetup 4 (Automizer W) (Additive W)) (g : G)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) :
    rank (inducedAutomizer (W.map (MulAut.conj g).toMonoidHom) A) ≤ 4 := by
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let := inducedAutomizer_elementary Wg A hA
  exact (offender_rank_le_primeRank _).trans
    ((primeRank_equiv 2 (automizerMapEquiv W (MulAut.conj g))).symm.trans_le
      (FourGeometry.source_primeRank_le S))

theorem reverse_fixed_spectrum
    (S : SourceSetup 4 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) (g : G)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
    (hr : 4 ≤ rank (inducedAutomizer (W.map (MulAut.conj g).toMonoidHom) A)) :
    rank (W.map (MulAut.conj g).toMonoidHom ⊓ centralizer (A : Set G)) = 1 ∨
    rank (W.map (MulAut.conj g).toMonoidHom ⊓ centralizer (A : Set G)) = 2 ∨
    rank (W.map (MulAut.conj g).toMonoidHom ⊓ centralizer (A : Set G)) = 4 := by
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  let J := inducedAutomizer Wg A
  let : IsElementaryAbelian 2 J := inducedAutomizer_elementary Wg A hA
  let e := automizerMapEquiv W (MulAut.conj g)
  let I := J.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.map _
  have he : I.map e.toMonoidHom = J := by
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro a
      exact e.apply_symm_apply a
    rw [hcomp, Subgroup.map_id]
  have hcard : Nat.card I = Nat.card J :=
    Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective
  have hI : 4 ≤ rank I := by simpa only [rank,hcard] using hr
  have hs := FourGeometry.source_fixed_spectrum S I hI
  have hd := Transport.fixed_finrank (automizerRepresentation W)
    (automizerRepresentation Wg) e (automizerModuleEquiv W (MulAut.conj g))
    (automizerRepresentation_equivariant W (MulAut.conj g)) I
  rw [he] at hd
  change Module.finrank (ZMod 2) (fixedSpace S.representation I) = 1 ∨
    Module.finrank (ZMod 2) (fixedSpace S.representation I) = 2 ∨
    Module.finrank (ZMod 2) (fixedSpace S.representation I) = 4 at hs
  rw [hρ,hd,← rank_fixed_centralizer A hA] at hs
  exact hs

variable {T : Sylow 2 G} {L V : Subgroup G}

theorem four_first_high_rank_false (B : DoubledBranch T L V 4)
    [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
    (M : B.MarkedAutomizerModel) (hp : B.PureIntersectionCentralizes) {g : G}
    (C : ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 1 4)
    (hg : IsWOffenderAt (componentOrbit V (T : Subgroup G)) T g)
    (hw : globalW (componentOrbit V (T : Subgroup G)) T = 1)
    (hr : (4 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)))
    (hI : 4 ≤ rank (inducedAutomizer (componentOrbit V (T : Subgroup G))
      (offenderNormalizer (componentOrbit V (T : Subgroup G)) g))) : False := by
  let W := componentOrbit V (T : Subgroup G)
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let A := offenderNormalizer W g
  let I := inducedAutomizer W A
  let U := W ⊓ normalizer (Wg : Set G)
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ Wg from inf_le_left)
  let := offender_inducedAutomizer_elementary W g
  have hIr : rank I = 4 := le_antisymm
    ((offender_rank_le_primeRank I).trans (FourGeometry.source_primeRank_le M.setup)) hI
  have hWr : rank W = 8 := four_orbit_rank M.setup
  have hWgr : rank Wg = 8 := by
    change Nat.log 2 (Nat.card (W.map (MulAut.conj g).toMonoidHom)) = 8
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hWr
  obtain ⟨hfix,hU⟩ := four_first_high_rank_profile B M hp C hI
  have hcen := LowRank.four_first_centralizer_eq M.setup M.representation_eq hg hw hr
  have hf : rank (W ⊓ centralizer (A : Set G)) = 2 := by
    rw [rank_fixed_centralizer A (show A ≤ normalizer (W : Set G) from inf_le_right),
      ← M.representation_eq]
    exact hfix
  have he : U ⊓ centralizer (Wg : Set G) = W ⊓ centralizer (A : Set G) := by
    rw [hcen]
    apply le_antisymm
    · exact inf_le_inf inf_le_left le_rfl
    · intro x hx
      exact ⟨⟨hx.1, _root_.centralizer_le_normalizer Wg hx.2⟩,hx.2⟩
  have hUr := rank_add_corank (show U ≤ W from inf_le_left)
  have hJr := rank_add_corank (show U ⊓ centralizer (Wg : Set G) ≤ U from inf_le_left)
  rw [← rank_inducedAutomizer Wg U (show U ≤ normalizer (Wg : Set G) from inf_le_right),he,hf] at hJr
  have hJ : 4 ≤ rank (inducedAutomizer Wg U) := by
    change subgroupCorank W U ≤ 2 at hU
    omega
  have hAr := rank_add_corank (show A ≤ Wg from inf_le_left)
  have hAc := rank_add_corank (show A ⊓ centralizer (W : Set G) ≤ A from inf_le_left)
  rw [← rank_inducedAutomizer W A (show A ≤ normalizer (W : Set G) from inf_le_right),hIr] at hAc
  have hc : subgroupCorank Wg A = 1 := C.corank
  have hK : rank (A ⊓ centralizer (W : Set G)) = 3 := by omega
  have hrev := high_reverse_centralizer_eq M.setup M.representation_eq C hr hI
    (LowRank.first_core_restrictions B M hp C).1 hU
  change Wg ⊓ centralizer (U : Set G) = A ⊓ centralizer (W : Set G) at hrev
  have hs := reverse_fixed_spectrum M.setup M.representation_eq g U inf_le_right hJ
  change rank (Wg ⊓ centralizer (U : Set G)) = 1 ∨
    rank (Wg ⊓ centralizer (U : Set G)) = 2 ∨
    rank (Wg ⊓ centralizer (U : Set G)) = 4 at hs
  rw [hrev,hK] at hs
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
