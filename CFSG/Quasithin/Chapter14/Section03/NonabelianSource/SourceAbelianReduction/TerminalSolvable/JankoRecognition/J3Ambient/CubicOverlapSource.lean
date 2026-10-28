module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.FieldSubgroups
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicProjective
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicRecognition
public import Theory.SpecificGroups.Janko3.SourceRecognition.BaumeisterParabolics.Point

/-!
# The literal overlap cubic in the terminal J₃ source

For an actual field-affine embedding `j` constructed in the original plane,
the literal point complement `overlap j` centralizes its literal cubic
`j cubic`. Its order is thirty, so the quotient by the same central cubic
has order divisible by ten. The existing involution-centralizer calculation
and the dihedral recognition proof therefore identify this literal quotient
with `A₆`; the existing cubic-normalizer theorem then identifies its literal
normalizer quotient with `PGL₂(9)`.

This removes the choice mismatch between a cubic selected from a plane
complement and the cubic already present in the actual Singer-field subgroup.
It does not split the central cubic extension or identify the second and third
Baumeister parabolics.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Janko23.J3Recognition.LocalSixteen
open Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

namespace J3Ambient

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem literal_cubic_quotient_ten_divisor
    (j : SingerField.Model →* G) (hj : Function.Injective j) :
    10 ∣ Nat.card (centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic)) := by
  have hsj : orderOf (j cubic) = 3 :=
    (orderOf_injective j hj _).trans cubic_order
  let O := overlap j
  have hO : Nat.card O = 30 := by
    rw [Nat.card_congr (overlapEquiv j hj).toEquiv]
    norm_num [Sporadic.Janko3.SourceRecognition.Seventeen.Complement,
      Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, DihedralGroup.card]
  have hOcentral : O ≤ centralizer ({j cubic} : Set G) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    apply mem_centralizer_singleton_iff.mpr
    exact ((cubic_commutes_complement ⟨y, hy⟩).map j).eq.symm
  have hdiv : 30 ∣ Nat.card (centralizer ({j cubic} : Set G)) := by
    rw [← hO]
    exact card_dvd_of_le hOcentral
  have hq : Nat.card (centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic)) * 3 =
      Nat.card (centralizer ({j cubic} : Set G)) := by
    have hh := (cubicKernel (j cubic)).index_mul_card
    change Nat.card (centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic)) *
      Nat.card (cubicKernel (j cubic)) = _ at hh
    rw [cubicKernel_card (j cubic) hsj] at hh
    exact hh
  obtain ⟨n, hn⟩ := hdiv
  refine ⟨n, ?_⟩
  omega

private theorem alternating_six_of_dihedral_centralizers_of_ten
    {B : Type*} [Group B] [Finite B] (h10 : 10 ∣ Nat.card B)
    (h : ∀ t : B, orderOf t = 2 →
      Nonempty (centralizer ({t} : Set B) ≃* DihedralGroup 4)) :
    Nonempty (B ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := B) 2
    ((by decide : 2 ∣ 10).trans h10)
  let D : DihedralInvolutionCentralizerHypotheses B 3 := {
    two_le := by decide
    z := t
    involution := ⟨by intro h1; simp [h1] at ht, ht ▸ pow_orderOf_eq_one t⟩
    involutions_conjugate := fun u hu => isConj_iff.mp
      (Sporadic.Janko3.SourceRecognition.CentralCubicQuotient.dihedral_centralizers_fusion h u t
        (orderOf_eq_prime hu.2 hu.1) ht)
    centralizer_equiv := h t ht }
  rcases D.recognize_eight with he | he
  · obtain ⟨e⟩ := he
    have hcard : Nat.card B = 168 := by
      rw [Nat.card_congr e.toEquiv]
      exact (Nat.card_congr Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm.toEquiv).trans
        Atlas.Comparisons.Exceptional.sl3Two_card
    rw [hcard] at h10
    norm_num at h10
  · exact he

private theorem literal_cubic_quotient_alternating_six
    {D : Seed G} (hc : Janko23.OneInvolutionClass G)
    (j : SingerField.Model →* G) (hj : Function.Injective j) :
    Nonempty (centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic) ≃*
      alternatingGroup (Fin 6)) := by
  let s : G := j cubic
  have hs : orderOf s = 3 :=
    (orderOf_injective j hj _).trans cubic_order
  have h10 := literal_cubic_quotient_ten_divisor j hj
  have hcent : ∀ v : centralizer ({s} : Set G) ⧸ cubicKernel s,
      orderOf v = 2 →
      Nonempty (centralizer ({v} : Set (centralizer ({s} : Set G) ⧸ cubicKernel s)) ≃*
        DihedralGroup 4) := by
    intro v hv
    exact cubic_quotient_involution_centralizers D.localType hc s hs v hv
  exact alternating_six_of_dihedral_centralizers_of_ten h10 hcent

/-- The literal Singer-field cubic gives the actual `A₆` centralizer quotient
and actual `PGL₂(9)` normalizer quotient. -/
theorem literal_field_cubic_projective
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane)
    (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    Nonempty (centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic) ≃*
      alternatingGroup (Fin 6)) ∧
      Nonempty (normalizer (zpowers (j cubic) : Set G) ⧸
        cubicNormalizerKernel (j cubic) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
  have hA6 := literal_cubic_quotient_alternating_six (D := D) hc j hj.1
  have hs : orderOf (j cubic) = 3 :=
    (orderOf_injective j hj.1 _).trans cubic_order
  obtain ⟨eA6⟩ := hA6
  refine ⟨⟨eA6⟩, ?_⟩
  exact cubic_normalizer_quotient_pgl_nine P hc (j cubic) hs eA6

end J3Ambient

section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)

variable (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hnot hgP hgH hyp hK
include hG hempty hM hu hmany hcard e hne

/-- The original terminal row supplies both quotient identifications for the
literal cubic of each actual field-affine subgroup, with all original plane,
complement, field-action, component and core markings retained. -/
theorem source_single_a5_j3_overlap_cubic_quotients_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Janko23.OneInvolutionClass G ∧
    ∃ (D : Seed G) (P : ReturningPair D)
      (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root),
      F.H = K ∧ F.H = Janko23.involutionCentralizer D.z ∧
      Janko23.ambientCore D.z = F.U ∧
      P.A₁ eR ≠ P.A₂ eR ∧ P.A₁ eR ⊔ P.A₂ eR = P.R ∧ P.A₁ eR ⊓ P.A₂ eR = P.E ∧
      ∀ A : Subgroup G, A = P.A₁ eR ∨ A = P.A₂ eR →
        IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
        ∃ (C : Subgroup (normalizer (A : Set G))) (f : C ≃* LinearGroup) (a : A ≃* Plane),
          (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
          (∀ (c : C) (x : A),
            a (A.normalizerMonoidHom c x) = naturalAction (f c) (a x)) ∧
          ∃ j : SingerField.Model →* G,
            PlaneTransport.FieldEmbedding A C a j ∧
            Nonempty (centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic) ≃*
              alternatingGroup (Fin 6)) ∧
            Nonempty (normalizer (zpowers (j cubic) : Set G) ⧸
              cubicNormalizerKernel (j cubic) ≃*
              GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
  obtain ⟨hc, D, P, eR, hHK, hHz, hcore, hneP, hsup, hinf, hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc, D, P, eR, hHK, hHz, hcore, hneP, hsup, hinf, ?_⟩
  intro A hA
  obtain ⟨hAE, hAc, C, f, a, hC, ha, j, hj⟩ := hfields A hA
  exact ⟨hAE, hAc, C, f, a, hC, ha, j, hj,
    J3Ambient.literal_field_cubic_projective P hc A C a j hj⟩

end Source

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
