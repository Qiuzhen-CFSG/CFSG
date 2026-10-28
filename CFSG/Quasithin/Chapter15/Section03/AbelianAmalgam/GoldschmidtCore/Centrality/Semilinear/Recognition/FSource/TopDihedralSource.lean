module

public import Mathlib.Algebra.Field.ULift
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.DihedralPSL2
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.SourceRows

/-!
# The full-component dihedral source alternatives

The lower source classification supplies the actual prime-power PSL₂ model,
the hexacode triple cover with both S₄ vertices, or the alternating-seven
model with its compatible rotation-character amalgam. Here these are applied
to the literal Chapter 15 quotient and common Sylow. The rotation model's
normal C₃ × E₄ base and quotient of order two construct its local extension.
The PSL₂ family uses the adequate ambient conclusion, preserving the original
thirteen-row interface separately.

Source: Aschbacher–Smith, F.6.18(6–7), printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open Theory.GroupTheory.RankTwoAmalgam
universe u
private theorem extension_equiv {D E A B : Type*} [Group D] [Group E] [Group A] [Group B]
    (e : D ≃* E) (h : Extension E A B) : Extension D A B := by
  obtain ⟨N, hN, ⟨a⟩, ⟨b⟩⟩ := h
  let := hN
  let M := N.comap e.toMonoidHom
  have he : M.map e.toMonoidHom = N := map_comap_eq_self_of_surjective e.surjective N
  exact ⟨M, inferInstance,
    ⟨((e.subgroupMap M).trans (MulEquiv.subgroupCongr he)).trans a⟩,
    ⟨(QuotientGroup.congr M N e he).trans b⟩⟩

private theorem rotation_extension :
    Extension (CubicFiber.group MixedEight.rotationCharacter) (C 3 × E4) (C 2) := by
  let N := MixedEight.extensionParity.ker
  have hN : Nat.card N = 12 := by
    rw [← Nat.card_congr MixedEight.baseEquiv.toEquiv]
    norm_num [MixedEight.Three, MixedEight.Four, MixedEight.Bit, Nat.card_prod]
  have hG : Nat.card (CubicFiber.group MixedEight.rotationCharacter) = 24 := by
    rw [CubicFiber.card, DihedralGroup.nat_card]
  have hQ : Nat.card (CubicFiber.group MixedEight.rotationCharacter ⧸ N) = 2 := by
    have hc := N.index_mul_card
    rw [hN,hG] at hc
    change N.index = 2
    omega
  exact ⟨N,inferInstance,⟨MixedEight.baseEquiv.symm⟩,
    ⟨mulEquivOfPrimeCardEq hQ (by simp [C])⟩⟩

variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G} {κ : GroupClass.{u}}
theorem top_dihedral_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4)
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G)) (ht : pResidual 2 G = ⊤) :
    AdequateAlternative G₁ G₂ S ∨ AdequateAlternative G₂ G₁ S := by
  let := q.coverGroup
  let := q.coverFinite
  have htop : generalizedFitting G = ⊤ := hF.symm.trans ht
  let : IsQuasisimple (pResidual 2 G) := hq
  let : IsQuasisimple (generalizedFitting G) :=
    IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hF)
  let : IsQuasisimple G :=
    IsQuasisimple.of_mulEquiv ((MulEquiv.subgroupCongr ht).trans topEquiv)
  have hs : Nonempty (S ≃* DihedralGroup 4) :=
    ⟨(MulEquiv.subgroupCongr hS.symm).trans eT⟩
  rcases ChapterF.SourceAssembly.source_top_dihedral_eight_rows
    (hA _) (hC _) q.sqtk q.equiv.symm h hq eT ht with hm | hm | hm
  · obtain ⟨p,f,hp,_,hf,hf2,hmod,F,_,_,hFc,⟨e⟩⟩ := hm
    let field : FieldParameter.{u} :=
      { Carrier := ULift.{u} F
        prime := p
        prime_isPrime := hp
        degree := f
        degree_pos := hf
        card := by simpa using hFc }
    let j : F ≃+* field.Carrier := ULift.ringEquiv.symm
    refine Or.inl (Or.inr ⟨⟨field,hf2,?_,e.trans (Atlas.fieldEquivPSL 2 j),htop,inferInstance,hs⟩⟩)
    simpa only [field, Nat.card_ulift, hFc] using hmod
  · obtain ⟨⟨e⟩,hleft,hright⟩ := hm
    have hc : Nat.card (center G) = 3 := by
      rw [Nat.card_congr (centerCongr e).toEquiv, Representation.Hexacode.even_center_card]
    have hcover : TripleAlternating G 6 :=
      ⟨inferInstance,⟨mulEquivOfPrimeCardEq hc (by simp [C])⟩,
        ⟨(QuotientGroup.congr (center G) _ e (map_center_equiv e)).trans
          Representation.Hexacode.even_quotient_center_equiv⟩⟩
    exact Or.inl (Or.inl (.six (Or.inl hcover) htop inferInstance hs hleft hright))
  · obtain ⟨hm,hpair⟩ := hm
    have hmodel : Nonempty (G ≃* alternatingGroup (Fin 7)) ∨ TripleAlternating G 7 := by
      rcases hm with he | he
      · exact Or.inl he
      · obtain ⟨e⟩ := he
        have hc : Nat.card (center G) = 3 := by
          rw [Nat.card_congr (centerCongr e).toEquiv,
            GLS3.Chapter5.OddCentralCovers.tripleSeven_center_card]
        exact Or.inr ⟨inferInstance,⟨mulEquivOfPrimeCardEq hc (by simp [C])⟩,
          ⟨(QuotientGroup.congr (center G) _ e (map_center_equiv e)).trans
            GLS3.Chapter5.OddCentralCovers.tripleSevenQuotientCenterEquiv⟩⟩
    rcases hpair with hp | hp
    · obtain ⟨e⟩ := hp
      exact Or.inl (Or.inl (.seven hmodel inferInstance hs ⟨e.left⟩
        (extension_equiv e.right rotation_extension)))
    · obtain ⟨e⟩ := hp
      exact Or.inr (Or.inl (.seven hmodel inferInstance hs ⟨e.left⟩
        (extension_equiv e.right rotation_extension)))
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
