module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.RootFrame
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.SylowAlignment

/-!
# Recovering the root frame from the Sylow and the two Weyl elements

The A-root group is the intrinsic group of central involutions in the Sylow.
For the short F-root group, conjugate by `R S R S R`. Five entries of the
unipotent matrix show that its intersection with the original Sylow contains
only F-root elements. The displayed Weyl word centralizes F, so an automorphism
fixing the Sylow and R, S preserves F as well. Weyl conjugation now recovers
the other six root groups, including the two literal negative simple roots.

The calculation uses no distinct-weight assumption, so includes the field of
order four. Source context: the G₂ automorphism input in Aschbacher--Smith
F.1.12, printed pp.263--264. Coordinate formulas are those of the licensed
ATLAS port (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

public section

open Atlas.SplitOctonion Atlas.G2.Explicit Subgroup
namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
variable {F : Type*} [Field F] [CharP F 2]
private def shortIsolationWeyl : Model F := weylR * weylS * weylR * weylS * weylR

omit [CharP F 2] in
private theorem shortIsolationWeyl_inv :
    (shortIsolationWeyl (F := F))⁻¹ = shortIsolationWeyl := by
  have hr : (weylR : Model F)⁻¹ = weylR := inv_eq_of_mul_eq_one_right (by
    rw [← pow_two, weylR_sq])
  have hs : (weylS : Model F)⁻¹ = weylS := inv_eq_of_mul_eq_one_right (by
    rw [← pow_two, weylS_sq])
  simp only [shortIsolationWeyl, mul_inv_rev, hr, hs, mul_assoc]

private theorem short_isolation {g : Model F} (hg : g ∈ unipotent)
    (hw : MulAut.conj shortIsolationWeyl g ∈ unipotent) :
    g ∈ rootGroup (F := F) 5 := by
  rw [unipotent_eq_range] at hg hw
  obtain ⟨t,rfl⟩ := hg
  obtain ⟨u, hu⟩ := hw
  change unipotentProduct u = shortIsolationWeyl * unipotentProduct t * shortIsolationWeyl⁻¹ at hu
  rw [shortIsolationWeyl_inv] at hu
  have h4 := congrArg (fun g : Model F => g.val (basisVector 0) 2) hu
  have h3 := congrArg (fun g : Model F => g.val (basisVector 0) 4) hu
  have h2 := congrArg (fun g : Model F => g.val (basisVector 0) 5) hu
  have h0 := congrArg (fun g : Model F => g.val (basisVector 0) 6) hu
  have h1 := congrArg (fun g : Model F => g.val (basisVector 1) 2) hu
  simp [shortIsolationWeyl, unipotentProduct, basisVector,
    weylR, weylREquiv, weylRLinear, weylRApply, weylS, weylSEquiv, weylSLinear, weylSApply,
    rootA,rootB,rootC,rootD,rootE,rootF,rootAEquiv,rootBEquiv,rootCEquiv,
    rootDEquiv,rootEEquiv,rootFEquiv,rootALinear,rootBLinear,rootCLinear,
    rootDLinear,rootELinear,rootFLinear,rootAApply,rootBApply,rootCApply,
    rootDApply,rootEApply,rootFApply, CharTwo.neg_eq, CharTwo.sub_eq_add] at h4 h3 h2 h0 h1
  have ht4 : t 4 = 0 := h2.symm
  have ht3 : t 3 = 0 := h3.symm
  have ht2 : t 2 = 0 := h4.symm
  have ht0 : t 0 = 0 := by simpa [ht4, ht3, ht2] using h0.symm
  have ht1 : t 1 = 0 := by simpa [ht4, ht3, ht2, ht0] using h1.symm
  refine ⟨Multiplicative.ofAdd (t 5), ?_⟩
  simp [rootHom, RootDiagonal.root, unipotentProduct, ht0, ht1, ht2, ht3, ht4]
end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage

namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
open LieParabolicSetup SylowParabolicInvariance
variable {F : Type*} [Field F] [CharP F 2]
private theorem shortIsolationWeyl_rootF (t : F) :
    MulAut.conj (shortIsolationWeyl (F := F)) (rootF t) = rootF t := by
  change shortIsolationWeyl * rootF t * shortIsolationWeyl⁻¹ = _
  rw [shortIsolationWeyl_inv]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [shortIsolationWeyl, weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootF, rootFEquiv, rootFLinear, rootFApply, CharTwo.neg_eq, CharTwo.sub_eq_add]

private theorem weylS_rootD (t : F) :
    MulAut.conj (weylS : Model F) (rootD t) = rootC t := by
  change weylS * rootD t * weylS⁻¹ = _
  rw [weylS_inverse]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [weylS, weylSEquiv, weylSLinear, weylSApply,
      rootD, rootDEquiv, rootDLinear, rootDApply,
      rootC, rootCEquiv, rootCLinear, rootCApply, CharTwo.neg_eq, CharTwo.sub_eq_add]
  ring

omit [CharP F 2] in
private theorem rootGroup_map_conj {i j : Fin 8} (w : Model F)
    (h : ∀ t : F, MulAut.conj w (RootDiagonal.root i t) = RootDiagonal.root j t) :
    (rootGroup i).map (MulAut.conj w).toMonoidHom = rootGroup j := by
  ext x
  constructor
  · rintro ⟨_, ⟨t,rfl⟩,rfl⟩
    exact ⟨t, (h t.toAdd).symm⟩
  · rintro ⟨t,rfl⟩
    exact ⟨_, ⟨t,rfl⟩, h t.toAdd⟩

omit [CharP F 2] in
private theorem preserves_conjugate (a : MulAut (Model F)) (w : Model F)
    (hw : a w = w) (H : Subgroup (Model F)) (hH : H.map a.toMonoidHom = H) :
    (H.map (MulAut.conj w).toMonoidHom).map a.toMonoidHom =
      H.map (MulAut.conj w).toMonoidHom := by
  have hc : a.toMonoidHom.comp (MulAut.conj w).toMonoidHom =
      (MulAut.conj w).toMonoidHom.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change a (w*x*w⁻¹) = w*a x*w⁻¹
    rw [map_mul, map_mul, map_inv, hw]
  rw [map_map, hc, ← map_map, hH]

/-- Fixing the standard Sylow and both displayed Weyl elements fixes all eight root groups. -/
theorem root_frame_of_sylow_weyl [Finite F] (a : MulAut (Model F))
    (ha : unipotent.map a.toMonoidHom = unipotent)
    (hR : a weylR = weylR) (hS : a weylS = weylS) : PreservesRootGroups a := by
  have hA : (rootGroup (F := F) 0).map a.toMonoidHom = rootGroup 0 :=
    map_eq_of_centralInvolutions unipotent highestRoot
      highestRoot_iff_centralInvolution a ha
  have hshort : a (shortIsolationWeyl (F := F)) = shortIsolationWeyl := by
    simp only [shortIsolationWeyl, map_mul, hR, hS]
  have hF : (rootGroup (F := F) 5).map a.toMonoidHom = rootGroup 5 := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨t,rfl⟩,rfl⟩
      change a (rootF t.toAdd) ∈ rootGroup 5
      apply short_isolation
      · rw [← ha]
        apply mem_map_of_mem
        simpa [unipotentProduct] using unipotentProduct_mem ![0,0,0,0,0,t.toAdd]
      · have hu : a (MulAut.conj (shortIsolationWeyl (F := F)) (rootF t.toAdd)) ∈ unipotent := by
          rw [shortIsolationWeyl_rootF, ← ha]
          apply mem_map_of_mem
          simpa [unipotentProduct] using unipotentProduct_mem ![0,0,0,0,0,t.toAdd]
        simpa only [MulAut.conj_apply, map_mul, map_inv, hshort] using hu
    · rw [Subgroup.card_map_of_injective a.injective]
  have hAB := rootGroup_map_conj (i := 0) (j := 1) (weylR : Model F) weylR_rootA
  have hBE := rootGroup_map_conj (i := 1) (j := 4) (weylS : Model F) weylS_rootB
  have hFD := rootGroup_map_conj (i := 5) (j := 3) (weylR : Model F) (fun t => by
    change MulAut.conj weylR (rootF t) = rootD t
    rw [← weylR_rootD]
    change (weylR * (weylR * rootD t * weylR⁻¹) * weylR⁻¹ : Model F) = rootD t
    have hRR : (weylR : Model F) * weylR = 1 := by rw [← pow_two, weylR_sq]
    calc
      _ = (weylR * weylR) * rootD t * (weylR * weylR)⁻¹ := by group
      _ = rootD t := by rw [hRR]; simp)
  have hDC := rootGroup_map_conj (i := 3) (j := 2) (weylS : Model F) weylS_rootD
  have hEn := rootGroup_map_conj (i := 4) (j := 6) (weylR : Model F) (fun _ => rfl)
  have hFn := rootGroup_map_conj (i := 5) (j := 7) (weylS : Model F) (fun _ => rfl)
  have hB := hAB ▸ preserves_conjugate a weylR hR (rootGroup 0) hA
  have hE := hBE ▸ preserves_conjugate a weylS hS (rootGroup 1) hB
  have hD := hFD ▸ preserves_conjugate a weylR hR (rootGroup 5) hF
  have hC := hDC ▸ preserves_conjugate a weylS hS (rootGroup 3) hD
  have hnE := hEn ▸ preserves_conjugate a weylR hR (rootGroup 4) hE
  have hnF := hFn ▸ preserves_conjugate a weylS hS (rootGroup 5) hF
  intro i
  fin_cases i
  · exact hA
  · exact hB
  · exact hC
  · exact hD
  · exact hE
  · exact hF
  · exact hnE
  · exact hnF
end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
