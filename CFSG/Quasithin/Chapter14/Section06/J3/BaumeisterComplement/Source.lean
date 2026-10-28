module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.Fusion
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.PlaneActors

/-!
# The original cubic kernel has a PGL₂(9) complement

The natural plane complement constructs the independent cubic and both
involution actors in Baumeister's nonfusion argument. The literal PGL₂(9)
quotient excludes fusion, and extraspecial coset fusion forces an abelian
Sylow three-subgroup. Transfer splits the centralizer; Schur–Zassenhaus
extends its derived complement to the full normalizer.

All constructions retain the chosen cubic and the original quotient map.
This completes the splitting step of Lemma 2.4 on the source plane data.
The parabolic model identifications of Lemmas 2.5–2.6 are separate.
Source: Baumeister, A geometry for groups of J₃-type (2007), pp.495–496.
-/

open Subgroup Representation.CentralCubicNaturalFour
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {D : LocalSixteen.Seed G}

/-- Splitting over the same cubic in any actual plane complement; the fusion premise is discharged. -/
theorem normalizer_complement_projective_of_plane_cubic
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (C : Subgroup (normalizer (A : Set G)))
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (s : C) (hsc : s ∈ center C) (hs : orderOf s = 3)
    (e : (centralizer ({((s : normalizer (A : Set G)) : G)} : Set G) ⧸
      cubicKernel ((s : normalizer (A : Set G)) : G)) ≃* alternatingGroup (Fin 6)) :
    let u : G := ((s : normalizer (A : Set G)) : G)
    ∃ (M : Subgroup (normalizer (zpowers u : Set G)))
      (eQ : (normalizer (zpowers u : Set G) ⧸ cubicNormalizerKernel u) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
      (eM : M ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F),
      (cubicNormalizerKernel u).IsComplement' M ∧
      ∀ x : M, eM x = eQ (QuotientGroup.mk' (cubicNormalizerKernel u) x.val) := by
  obtain ⟨q,a,ha⟩ := P.plane_quotient_natural hc A hA hAR
  let f : C ≃* LinearGroup := hC.symm.QuotientMulEquiv.symm.trans q
  have hfa (c : C) (x : A) :
      a (A.normalizerMonoidHom c x) = naturalAction (f c) (a x) := ha c x
  obtain ⟨σ,r,t,hσ,hσout,hr,ht,hrs,hri,htfix⟩ :=
    plane_complement_cubic_actors A C f a hfa s hsc hs
  have hsG : orderOf ((s : normalizer (A : Set G)) : G) = 3 :=
    (orderOf_coe (s : normalizer (A : Set G))).trans ((orderOf_coe s).trans hs)
  exact normalizer_complement_projective_of_involution_actors P hc _ hsG e
    σ hσ hσout r t hr ht hrs hri htfix
end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
