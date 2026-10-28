module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.Natural
public import Theory.Representation.BinaryPermutation.SevenParabolic.Extension
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightCoordinates
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.BinaryMaps
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.Geometry

/-!
# Source-model applications of the symmetric moved-plane calculations

For the seven-letter case, the existing faithful-extension theorem
constructs the actual overgroup action from the prescribed natural action
of a normal A₇. This includes the case where that subgroup is F*(G).
Only its normality and its actual module coordinates are needed.

For the eight-letter case, the faithful deleted-module homomorphism and
the intrinsic quadratic geometry show that the full split isometry group
is S₈. Its group equivalence and the original split isometry intertwine
the actions. Restricting them to an index-at-most-two subgroup transports
the moved-plane transitivity theorem with its literal subgroup and action.

The quadratic constructions and geometry are reused from the attributed
ATLAS port; see `LICENSES/ATLAS.txt` and the imported modules. The small
conjugate-product premise remains explicit in these reusable model lemmas;
`Symmetric.Source` discharges it from the intrinsic type-a₂ hypotheses.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(4–5), printed p.364 (PDF p.375), and the proof of 6.2.19,
printed p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.Symmetric
open _root_.Equiv BinaryPermutation

theorem seven_extension_rank_ne_two
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (K : Subgroup G) [K.Normal]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (eK : K ≃* alternatingGroup (Fin 7))
    (eV : V ≃ₗ[ZMod 2] core (Fin 7))
    (he : ∀ k : K, ∀ x, eV (ρ k x) =
      alternatingCoreRepresentation (Fin 7) (eK k) (eV x))
    (v : G) (hv : v ≠ 1) (hv2 : v ^ 2 = 1) (hb : SmallConjugateProducts v) :
    Module.finrank (ZMod 2) (movedSpace ρ v) ≠ 2 := by
  obtain ⟨f, hf, hfK, hact⟩ := SevenParabolic.faithful_extension K ρ hρ eK eV he
  let eG := MonoidHom.ofInjective hf
  let eW := eV.trans (coreEquivNatural (Fin 7) (by decide))
  have hA : alternatingGroup (Fin 7) ≤ f.range := by
    intro a ha
    obtain ⟨k, hk⟩ := eK.surjective ⟨a, ha⟩
    refine ⟨k.val, (hfK k).trans ?_⟩
    exact congrArg Subtype.val hk
  have hW (g : G) (x : V) :
      eW (ρ g x) = ((naturalRepresentation (Fin 7)).comp f.range.subtype) (eG g) (eW x) := by
    change coreEquivNatural (Fin 7) (by decide) (eV (ρ g x)) =
      naturalRepresentation (Fin 7) (f g) (coreEquivNatural (Fin 7) (by decide) (eV x))
    rw [hact, coreEquivNatural_equivariant]
  rw [finrank_movedSpace_transport ρ _ eG eW hW v]
  apply seven_rank_ne_two f.range hA (eG v)
  · exact fun h => hv (eG.injective (h.trans eG.map_one.symm))
  · rw [← map_pow, hv2, map_one]
  · exact hb.map eG

open Atlas.Order20160A8

/-- The complete split six-dimensional orthogonal group, with its original action. -/
def splitOrthogonalAction : Representation (ZMod 2) (O_DPlus 3 (ZMod 2))
    (ClassicalOrthogonal.VectorD 3 (ZMod 2)) where
  toFun g := g.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The faithful deleted permutation action exhausts the full split isometry group. -/
theorem orthogonalHom_bijective : Function.Bijective DeletedEight.orthogonalHom := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨DeletedEight.orthogonalHom_injective, le_antisymm ?_ ?_⟩
  · exact Nat.card_le_card_of_injective _ DeletedEight.orthogonalHom_injective
  · have hs : Nat.card (Perm (Fin 8)) = 40320 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [hs]
    exact Geometry.orthogonal_card_le

noncomputable def symmetricOrthogonalEquiv : Perm (Fin 8) ≃* O_DPlus 3 (ZMod 2) :=
  MulEquiv.ofBijective DeletedEight.orthogonalHom orthogonalHom_bijective

/-- The split-space coordinates followed by the actual natural-section quotient map. -/
noncomputable def splitNaturalEquiv :
    ClassicalOrthogonal.VectorD 3 (ZMod 2) ≃ₗ[ZMod 2] natural (Fin 8) :=
  DeletedEight.splitIsometry.toLinearEquiv.trans TerminalOrthogonal.Eight.naturalEquiv

theorem symmetricOrthogonalEquiv_action (p : Perm (Fin 8))
    (x : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
    splitNaturalEquiv
        (splitOrthogonalAction (symmetricOrthogonalEquiv p) x) =
      naturalRepresentation (Fin 8) p (splitNaturalEquiv x) := by
  change TerminalOrthogonal.Eight.naturalEquiv
      (DeletedEight.splitIsometry
        (DeletedEight.splitIsometry.symm
          (DeletedEight.quotientPerm p (DeletedEight.splitIsometry x)))) = _
  rw [DeletedEight.splitIsometry.apply_symm_apply]
  exact TerminalOrthogonal.Eight.naturalEquiv_equivariant p _

theorem split_orthogonal_stabilizerTransitive
    (H : Subgroup (O_DPlus 3 (ZMod 2))) (hH : H.index ≤ 2)
    (v : H) (hv : v ≠ 1) (hv2 : v ^ 2 = 1) (hb : SmallConjugateProducts v)
    (hr : Module.finrank (ZMod 2)
      (movedSpace (splitOrthogonalAction.comp H.subtype) v) = 2) :
    StabilizerTransitive (splitOrthogonalAction.comp H.subtype)
      (movedSpace (splitOrthogonalAction.comp H.subtype) v) := by
  let S := H.comap symmetricOrthogonalEquiv.toMonoidHom
  let eS : S ≃* H := MulEquiv.ofBijective
    (symmetricOrthogonalEquiv.toMonoidHom.subgroupComap H)
    ⟨fun a b h => Subtype.ext (symmetricOrthogonalEquiv.injective (congrArg Subtype.val h)),
      symmetricOrthogonalEquiv.toMonoidHom.subgroupComap_surjective_of_surjective H
        symmetricOrthogonalEquiv.surjective⟩
  let eH : H ≃* S := eS.symm
  let eV := splitNaturalEquiv
  have hi : S.index ≤ 2 := by
    exact (H.index_comap_of_surjective
      (f := symmetricOrthogonalEquiv.toMonoidHom) symmetricOrthogonalEquiv.surjective).le.trans hH
  have he (g : H) (x : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
      eV ((splitOrthogonalAction.comp H.subtype) g x) =
        ((naturalRepresentation (Fin 8)).comp S.subtype) (eH g) (eV x) := by
    have h := symmetricOrthogonalEquiv_action (symmetricOrthogonalEquiv.symm g.val) x
    rw [symmetricOrthogonalEquiv.apply_symm_apply] at h
    have hval : (eH g).val = symmetricOrthogonalEquiv.symm g.val := by
      apply symmetricOrthogonalEquiv.injective
      exact (congrArg Subtype.val (eS.apply_symm_apply g)).trans
        (symmetricOrthogonalEquiv.apply_symm_apply g.val).symm
    change eV (splitOrthogonalAction g.val x) = naturalRepresentation (Fin 8) (eH g).val (eV x)
    rw [hval]
    exact h
  apply stabilizerTransitive_transport _ _ eH eV he v
  apply eight_stabilizerTransitive S hi (eH v)
  · exact fun h => hv (eH.injective (h.trans eH.map_one.symm))
  · rw [← map_pow, hv2, map_one]
  · exact hb.map eH
  · exact (finrank_movedSpace_transport _ _ eH eV he v).symm.trans hr

end Representation.RankTwo.Symmetric
