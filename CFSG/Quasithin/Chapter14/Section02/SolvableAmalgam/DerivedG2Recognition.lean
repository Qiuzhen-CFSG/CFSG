module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.CubicRecognition
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import ABG.ChapterII.Section2.SylowShapeTransport

/-!
# The original derived-G₂ completion in 14.2.22

The marked amalgam identifies the actual ambient Sylow with the height-two
wreathed Sylow in G₂(2)′. Original local rigidity identifies the first
parabolic with the full centralizer of the Sylow central involution. That
parabolic is solvable. Fong's proved recognition theorem therefore identifies
the entire simple group, and the concrete PSU₃(3) comparison returns the
literal G₂ commutator carrier used in Theorem E.

Source: Aschbacher--Smith14.2.22 and I.4.4, printed pp.989,417; Fong,
Some Sylow subgroups of order32, Journal of Algebra6 (1967), pp.69--76.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.GreenBook ChapterF.SourceAssembly ChapterF.SourceAssembly.Goldschmidt RankTwoAmalgam
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G]

/-- The actual marked pair and full centralizer identify the ambient simple group. -/
theorem derived_g2_recognition [IsSimpleGroup G]
    (T : Sylow 2 G) (H X : Subgroup G)
    (hHX : H ⊓ X = (T : Subgroup G))
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hH : H = centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hm : ExceptionalModels.G2.IsDerivedAmalgam (inclusionAmalgam H X)) :
    Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨m⟩ := hm
  let eT : T ≃* derivedSylow := (MulEquiv.subgroupCongr hHX.symm).trans m.middle
  have hW : ABG.IsWreathedOfHeight T 2 :=
    ABG.wreathed_equiv eT.symm derivedSylow_isWreathedOfHeight
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (hZ ▸ (by decide : 2 ∣ 2))
  have hzG : orderOf (z : G) = 2 := (orderOf_injective Z.subtype Z.subtype_injective z).trans hz
  have hzgen : zpowers (z : G) = Z := eq_of_le_of_card_ge (zpowers_le.mpr z.property) (by
    rw [Nat.card_zpowers,hzG]
    exact hZ.le)
  have hC : centralizer ({(z : G)} : Set G) = H := by
    calc
      _ = centralizer (zpowers (z : G) : Set G) := by
        rw [zpowers_eq_closure,centralizer_closure]
      _ = H := (congrArg (fun K : Subgroup G => centralizer (K : Set G)) hzgen).trans hH.symm
  let : Group.IsSolvable derivedFirst := derivedFirst_isSolvable
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective (f := m.left.toMonoidHom) m.left.injective
  let : Group.IsSolvable (centralizer ({(z : G)} : Set G)) := by rw [hC]; infer_instance
  obtain ⟨e⟩ := Stellmacher.Recognition.FongWreathed.nonempty_equiv_psu3 T hW z hzG
  exact ⟨e.trans Atlas.G2.nonempty_commutator_binary_equiv_psu3.some.symm⟩

/-- Literal Theorem E application after the independent original local rigidity. -/
theorem source_theoremE_of_derived_g2_mark
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc H : Subgroup G}
    (hcard : Nat.card (localModule T M) = 4) (hTM : (T : Subgroup G) ≤ M)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hHX : H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)) = (T : Subgroup G))
    (hH : H = centralizer (centralInvolutions T : Set G))
    (hm : ExceptionalModels.G2.IsDerivedAmalgam
      (inclusionAmalgam H (sourceResidual M Mc ⊔ (T : Subgroup G)))) :
    ClassificationModels.IsTheoremEModel G := by
  let : IsSimpleGroup G := hG.simple
  exact .g2_derived (derived_g2_recognition T H _ hHX
    (plane_centralInvolutions_card T M hTM hcard e) hH hm)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
