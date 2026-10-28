module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.PGLCase

/-!
# The marked PGL2 row retaining its original component

When the quasisimple two-residual is proper and the original common
Sylow subgroup is dihedral of order eight, the source A/C model sieve
forces a prime PSL2 component. The ambient group is PGL2(p), its prime is
eleven or thirteen modulo twenty-four, and the original marked amalgam
is the S4--D24 reflection model, up to interchanging the vertices.
The same selected prime also marks the original two-residual as PSL2(p),
so the component field in the final classification uses the original subgroup.
All model, cover, extension and local marking premises are discharged.

Source: Aschbacher--Smith F.6.18(5), printed pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory GorensteinWalter
open Theory.GroupTheory.RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

theorem source_proper_dihedral_eight_pgl_row_with_component
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ ((pResidual 2 G) ⧸ center (pResidual 2 G)))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : Theory.GroupTheory.IsQuasisimple (pResidual 2 G))
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4)
    (hproper : pResidual 2 G ≠ ⊤) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
      ClassicalGroup.IsPSL (pResidual 2 G) 2 p ∧
      Nonempty (G ≃* PGL2 (ZMod p)) ∧
      (Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
        (MixedEight.amalgam MixedEight.reflectionCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups G₂ (G₂ ⊓ G₁) G₁ inf_le_left inf_le_right)
        (MixedEight.amalgam MixedEight.reflectionCharacter))) := by
  let R := pResidual 2 G
  let : Theory.GroupTheory.IsQuasisimple R := hq
  let : IsSimpleGroup (R ⧸ center R) := Theory.GroupTheory.IsQuasisimple.simple
  let : Nontrivial R := (QuotientGroup.mk'_surjective (center R)).nontrivial
  have hK : IsComponent G R := ⟨(inferInstance : R.Normal).isSubnormal, hq⟩
  have hcore := Noncyclic.twoCore_eq_bot_of_cover e
  obtain ⟨T, hTs⟩ := h.intersection_sylow
  let jT : T ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr hTs.symm).trans eT
  have hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8 := by
    rw [Nat.card_congr eT.toEquiv, DihedralGroup.nat_card]
  have hT8 : Nat.card T = 8 := by rw [Nat.card_congr jT.toEquiv, DihedralGroup.nat_card]
  have hn8 : ¬ 8 ∣ Nat.card R := fun h8 => hproper
    (normal_eq_top_of_sylow_eight_of_eight_dvd T hT8 R (isPGroup_quotient_pResidual 2) h8)
  rcases component_models_of_dihedral_eight hA hC hH e hK T jT with hm | hm | hm | hm
  · obtain ⟨p, f, hp, ho, hf, hf2, hm⟩ := hm
    rcases psl_component_parameters_of_sylow_eight T hT8 (isPGroup_quotient_pResidual 2)
      hp ho hf hf2 hm with ⟨htop, _⟩ | ⟨_, hf1, h8⟩
    · exact (hproper htop).elim
    · subst f
      have hm' : ClassicalGroup.IsPSL R 2 p := by simpa using hm
      have hlarge : 3 < p := by
        obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm'
        let : Group.IsPerfect PSL(2,F) :=
          Group.IsPerfect.ofSurjective (f := j.toMonoidHom) j.surjective
        let : Nontrivial PSL(2,F) := j.symm.surjective.nontrivial
        have hc := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
          (hF ▸ ho) (Group.IsPerfect.not_isSolvable PSL(2,F))
        simpa [hF] using hc
      let : Fact p.Prime := ⟨hp⟩
      exact ⟨p, hp, ho, prime_mod24_of_proper_psl_residual h hcore hT hproper ho h8 hm', hm',
        pgl_prime_of_proper_psl_twoResidual hFstar hproper hlarge hm',
        reflection_amalgam_of_proper_psl_residual h hcore hT hFstar hproper ho hlarge hm'⟩
  · obtain ⟨j⟩ := hm
    apply (hn8 _).elim
    rw [Nat.card_congr j.toEquiv, Atlas.Codes.hexEven_card]
    norm_num
  · obtain ⟨j⟩ := hm
    apply (hn8 _).elim
    rw [Nat.card_congr j.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  · obtain ⟨j⟩ := hm
    apply (hn8 _).elim
    rw [Nat.card_congr j.toEquiv]
    exact (show 8 ∣ Nat.card (alternatingGroup (Fin 7)) by
      rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num).trans
      (Subgroup.card_dvd_of_surjective
        GLS3.Chapter5.OddCentralCovers.tripleSevenProjection
        GLS3.Chapter5.OddCentralCovers.tripleSevenProjection_surjective)

end CFSG.Quasithin.ChapterF.SourceAssembly
