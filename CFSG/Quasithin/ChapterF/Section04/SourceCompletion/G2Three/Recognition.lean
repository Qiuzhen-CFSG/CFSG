module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.G2Three.LocalFixed
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.G2Three.Comparison
public import Theory.GroupTheory.DihedralTorus

/-!
# Recognition of the ternary G₂ parabolic completion

The original order-six involutions give hexagon diameter. The sixth power
of the canonical Weyl rotation therefore lies in the Borel. It centralizes
the ternary torus, hence lies in that torus and is involutory. Both Weyl
reflections consequently centralize it, forcing it to be the identity.
The canonical pair now satisfies the same relation in the given and native
completions. Their paired completion has hexagon diameter, so both coset
covering projections are injective and give the actual group equivalence.

This proves the G₂(3) specialization of Aschbacher–Smith F.4.26, printed
p.288, via the smallness argument of F.3.6 and F.4.8, printed pp.272 and
278. It uses the actual octonion parabolics and whole Borel overlap.
No finiteness, simplicity, group-order or geometry certificate is added
to the original completion and involution hypotheses.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
variable {G : Type*} [Group G] (c : Completion G)
local notation "A" => c.torus (-1) 1
local notation "B" => c.torus 1 (-1)
local notation "α" => GreenBook.LieModels.G2.amalgam (F := ZMod 3)

theorem rotation_six_eq_one (hdiam : ∀v w,c.graph.dist v w≤6) : (c.R*c.S)^6=1 := by
  obtain ⟨b,hb⟩ := c.rotation_six_mem_middle hdiam
  have hBsq : B^2=1 := by
    change (c.middle (nativeTorus 1 (-1)))^2=1
    rw [←map_pow,show (nativeTorus 1 (-1))^2=1 from Subtype.ext TernaryTorus.b_sq,map_one]
  have hAB : Commute A B := by
    have he : Commute (nativeTorus (-1) 1) (nativeTorus 1 (-1)) :=
      Subtype.ext TernaryTorus.ab_commute.eq
    exact he.map c.middle
  have hc := Group.sixth_commutes_of_torus_action c.S c.R A B c.S_sq c.R_sq hBsq hAB
    c.S_A c.S_B c.R_A c.R_B
  have ha : Commute TernaryTorus.a b.val := by
    have he := c.middle_injective (show c.middle (nativeTorus (-1) 1*b)=
        c.middle (b*nativeTorus (-1) 1) from by
      simpa only [map_mul,hb,torus] using hc.1.symm.eq)
    exact congrArg Subtype.val he
  have hbb : Commute TernaryTorus.b b.val := by
    have he := c.middle_injective (show c.middle (nativeTorus 1 (-1)*b)=
        c.middle (b*nativeTorus 1 (-1)) from by
      simpa only [map_mul,hb,torus] using hc.2.symm.eq)
    exact congrArg Subtype.val he
  have ht := TernaryTorus.borel_centralizer_le_torus b.val
    (GreenBook.LieModels.G2.overlap_eq_borel.le b.property) ha hbb
  have hb2 : b^2=1 := Subtype.ext (TernaryTorus.torus_square b.val ht)
  have hq : ((c.R*c.S)^6)^2=1 := by rw [←hb,←map_pow,hb2,map_one]
  have hcref := Group.reflections_commute_sixth c.S c.R c.S_sq c.R_sq hq
  have hS : Commute weylS b.val := by
    have he := c.left_injective (show c.left (nativeS*(α).left b)=
        c.left ((α).left b*nativeS) from by
      simp only [map_mul]
      change c.S*c.middle b=c.middle b*c.S
      rw [hb]
      exact hcref.1.eq)
    exact congrArg Subtype.val he
  have hR : Commute weylR b.val := by
    have he := c.right_injective (show c.right (nativeR*(α).right b)=
        c.right ((α).right b*nativeR) from by
      have hbR : c.right ((α).right b)=(c.R*c.S)^6 :=
        (DFunLike.congr_fun c.compatible b).symm.trans hb
      simpa only [map_mul,hbR,R] using hcref.2.eq)
    exact congrArg Subtype.val he
  have hb1 : b=1 := Subtype.ext (TernaryTorus.torus_weyl_centralizer b.val ht hS hR)
  rw [←hb,hb1,map_one]

/-- The canonical short/long Weyl pair obeys the hexagon relation in every small completion. -/
theorem canonical_weyl_relation (hdiam : ∀v w,c.graph.dist v w≤6) : (c.S*c.R)^6=1 := by
  have hsi : c.S⁻¹=c.S := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using c.S_sq)
  have hri : c.R⁻¹=c.R := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using c.R_sq)
  have h := congrArg Inv.inv (c.rotation_six_eq_one hdiam)
  simpa only [←inv_pow,mul_inv_rev,hsi,hri,inv_one] using h

/-- Native G₂(3) recognition from the literal F.4.26 involution hypotheses. -/
theorem nonempty_mulEquiv_of_orders (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : orderOf s=2) (ht2 : orderOf t=2) (hst : orderOf (s*t)=6) :
    Nonempty (G ≃* Model (ZMod 3)) := by
  have hdiam := (c.hexagon_metric_of_orders s t hs ht hsout htout hs2 ht2 hst).2.1
  exact c.nonempty_mulEquiv_of_matching_involutions modelCompletion nativeS nativeR
    (Subtype.ext weylS_sq) (Subtype.ext weylR_sq) c.S_out c.R_out
    (c.canonical_weyl_relation hdiam) native_SR_six
end CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
