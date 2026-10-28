module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.LocalFaithfulness
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import Theory.SpecificGroups.PSL2.CubicFourExclusion
/-!
# The dihedral vertex in the odd-prime component product

The actual first vertex acts faithfully on K. Prime-field automorphism
coverage realizes that action in PGL₂. The two proved mixed D₈ amalgams
leave D₂₄ or the exceptional vertex containing C₃×E₄. The latter cannot
embed in odd PGL₂, so the original vertex is D₂₄.

Source: Aschbacher--Smith F.6.17(2), printed p.309. All local embeddings
come from conjugation on the original selected component; the exceptional
amalgam and its concrete product subgroup are retained literally.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
variable {G₁ G₂ : Subgroup G} {p : ℕ} [Fact p.Prime]

theorem SingleResidualComponent.left_vertex_pgl_embedding (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    (hp : Odd p) (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    ∃ f : G₁ →* PGL2 (ZMod p), Function.Injective f := by
  let K := d.component
  let : K.Normal := d.normal
  obtain ⟨hz,_,⟨j⟩⟩ := prime_psl_component_center_and_outer e d.isComponent hp hm
  obtain ⟨hQK,_,_,hgood,_,_⟩ := d.source_prime_local_models e h hp hm hc
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp (twoCore_le_primeToThreeCore.trans_eq
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e))
  obtain ⟨hd,_⟩ := d.local_disjoint_centralizer h hcore hz hQK hgood hc
  let a : G₁ →* MulAut K := (MulAut.conjNormal : G →* MulAut K).comp G₁.subtype
  have ha : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxC : (x : G) ∈ centralizer (K : Set G) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer K]
      exact hx
    exact Subtype.ext (hd.le_bot ⟨x.property,hxC⟩)
  have hl := prime_psl_component_prime_gt_three d.isComponent hp hm
  have hF : IsOddPrimePower (Nat.card (ZMod p)) := ⟨p,1,Fact.out,hp,by omega,by simp⟩
  let b : PGL2 (ZMod p) ≃* MulAut PSL(2,ZMod p) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 (ZMod p) hF (by simpa using hl))
      ⟨pgl2InnerAutPSL2_injective (ZMod p) hF (by simpa using hl),
        Theory.PSL2.primeField_pgl_coverage hp hl⟩
  exact ⟨b.symm.toMonoidHom.comp ((MulAut.congr j).toMonoidHom.comp a),
    b.symm.injective.comp ((MulAut.congr j).injective.comp ha)⟩


theorem SingleResidualComponent.source_prime_left_dihedral (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    (hp : Odd p) (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    Nonempty (G₁ ≃* DihedralGroup 12) := by
  obtain ⟨f,hf⟩ := d.left_vertex_pgl_embedding e h hp hm hc
  obtain ⟨_,_,hT,hgood,_,_⟩ := d.source_prime_local_models e h hp hm hc
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp (twoCore_le_primeToThreeCore.trans_eq
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e))
  have hT' : Nat.card (G₂ ⊓ G₁ : Subgroup G) = 8 := by rwa [inf_comm]
  rcases h.symm.mixed_eight_cases hcore hgood
    (left_not_characteristic_two_of_cubic h hc) hT' with hi | hi
  · obtain ⟨iso⟩ := hi
    exact ⟨iso.right.trans RankTwoAmalgam.MixedEight.reflectionVertexEquiv⟩
  · obtain ⟨iso⟩ := hi
    let g := f.comp (iso.right.symm.toMonoidHom.comp RankTwoAmalgam.MixedEight.baseHom)
    have hg : Function.Injective g := hf.comp
      (iso.right.symm.injective.comp RankTwoAmalgam.MixedEight.baseHom_injective)
    exact (Theory.PSL2.no_injective_cubic_four_product
      (show IsOddPrimePower (Nat.card (ZMod p)) from ⟨p,1,Fact.out,hp,by omega,by simp⟩)
      g hg).elim
end CFSG.Quasithin.ChapterF.SourceAssembly
