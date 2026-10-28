module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.LinearParameters
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.PrimeExtension

/-!
# The complete ambient model list in the dihedral-eight source branch

The source A/C hypotheses identify the actual quasisimple residual.
Components with Sylow order eight exhaust the ambient two-part and are the
whole group. A proper PSL2 component has elementary Sylow of order four;
the degree restriction forces a prime field, and faithful generalized
Fitting conjugation identifies its ambient extension with PGL2(p).

Thus the original group is PSL2(p^f), f at most two and p^f seven or nine
modulo sixteen, the actual triple cover of A6, PGL2(p) with p three or five
modulo eight, A7, or its actual triple cover. The further source inspection
of the two local vertices supplies the row-specific amalgam markings.

Source: Aschbacher--Smith F.6.18, printed p.310, dihedral-eight paragraph.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

/-- The actual ambient shortlist in F.6.18(5)--(7), with field-degree
and Sylow congruences and no recognition premise. -/
theorem source_dihedral_eight_quasisimple_models
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ ((pResidual 2 G) ⧸ center (pResidual 2 G)))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
      (p ^ f % 16 = 7 ∨ p ^ f % 16 = 9) ∧ ClassicalGroup.IsPSL G 2 (p ^ f)) ∨
    Nonempty (G ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      Nonempty (G ≃* GorensteinWalter.PGL2 (ZMod p))) ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) := by
  let : IsQuasisimple (pResidual 2 G) := hq
  let : IsSimpleGroup ((pResidual 2 G) ⧸ center (pResidual 2 G)) := IsQuasisimple.simple
  let : Nontrivial (pResidual 2 G) := (QuotientGroup.mk'_surjective (center (pResidual 2 G))).nontrivial
  rcases source_dihedral_eight_residual_models hA hC hH e h hq eT with
    hm | hm | hm | hm
  · obtain ⟨p, f, hp, ho, hf, hf2, hm⟩ := hm
    obtain ⟨T, hT⟩ := h.intersection_sylow
    let jT : T ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr hT.symm).trans eT
    have hT8 : Nat.card T = 8 := by rw [Nat.card_congr jT.toEquiv, DihedralGroup.nat_card]
    rcases psl_component_parameters_of_sylow_eight T hT8 (isPGroup_quotient_pResidual 2)
      hp ho hf hf2 hm with ⟨htop, hmod⟩ | ⟨hproper, rfl, hmod⟩
    · let j : G ≃* pResidual 2 G := topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm
      exact .inl ⟨p, f, hp, ho, hf, hf2, hmod, hm.of_mulEquiv j⟩
    · have hm' : ClassicalGroup.IsPSL (pResidual 2 G) 2 p := by simpa using hm
      have hlarge : 3 < p := by
        obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm'
        let : Group.IsPerfect PSL(2,F) :=
          Group.IsPerfect.ofSurjective (f := j.toMonoidHom) j.surjective
        let : Nontrivial PSL(2,F) := j.symm.surjective.nontrivial
        have hlarge := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
          (hF ▸ ho) (Group.IsPerfect.not_isSolvable PSL(2,F))
        simpa [hF] using hlarge
      let : Fact p.Prime := ⟨hp⟩
      exact .inr (.inr (.inl ⟨p, hp, ho, hmod,
        pgl_prime_of_proper_psl_twoResidual hFstar hproper hlarge hm'⟩))
  · exact .inr (.inl hm)
  · exact .inr (.inr (.inr (.inl hm)))
  · exact .inr (.inr (.inr (.inr hm)))

end CFSG.Quasithin.ChapterF.SourceAssembly
