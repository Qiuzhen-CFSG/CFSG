module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalCaseFiveGeometry
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianBinaryAmalgam

/-!
# Original CaseFive exclusion without the internal naturality input

The new source geometry retains the actual two fixed planes and original
parabolic. Their literal binary-plane action yields the original contradiction.
The initial natural marking remains part of HigherRankHypothesis; the separate
NaturalReduction4 input formerly passed through this CaseFive argument is
fully discharged by the actual returning-center action.
Source: Aschbacher--Smith 12.9.4, printed pp.859--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual CaseFive branch is impossible from the same-T module rows and
original source hypotheses, without an independent NaturalReduction4 input. -/
theorem nonabelian_caseFive_impossible_of_original_rows
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) : False := by
  obtain ⟨v,C,I,c,hv,hline,hnat,hiZ,hi,hcD,hE,hcE,hd,hPD,hRD,hirr,
    hsplit,hdis,hcA,hfix,hAZ,hDA,hmove,hkernel,hYE,hTY,hTD,hsmall,hsquare,hno4,hnot⟩ :=
    nonabelian_caseFive_binary_geometry_of_original_rows modules h preferred earlier
      F hne g hgP hgH B h5
  let D := I ⊓ centralizer (conjugate F.ZU g : Set G)
  let E := F.Vi 2 ⊔ D
  let A := E ⊓ Section08.centerIn (F.I₂ L)
  let P := componentPlanePreimage F C v
  let Y := P ⊔ F.I₂ L
  let W := F.Vi 2
  let : IsElementaryAbelian 2 E := hE
  let := h.chosen.elementary
  let := F.binaryPlane_elementary
  let := F.localKernel_tilde_seed_elementary
  have hAE : A ≤ E := inf_le_left
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAE
  have hWA : W ≤ centralizer (A : Set G) := by
    exact le_centralizer_iff.mp ((inf_le_right.trans (centerIn_le_centralizer _)).trans
      (centralizer_le (((F.le_seed 2).trans (le_conjugateSpanBy V F.H)).trans
        (le_conjugateSpanBy F.U (F.P L)))))
  obtain ⟨k₀,hk₀⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting W A hdis hWA
  let k : W × A ≃* E := k₀.trans (MulEquiv.subgroupCongr hsplit.symm)
  have hk (w : W) (a : A) : (k (w,a) : G) = (w:G)*(a:G) := hk₀ w a
  let f : Y →* MulAut E := E.normalizerMonoidHom.comp (inclusion hYE)
  let ρ : Y →* MulAut (W × A) := (MulAut.congr k.symm).toMonoidHom.comp f
  have hρ (y : Y) (w : W) (a : A) :
      (k (ρ y (w,a)) : G) = (y:G)*((w:G)*(a:G))*(y:G)⁻¹ := by
    change (k (k.symm (f y (k (w,a)))) : G) = _
    rw [k.apply_symm_apply]
    change (y:G)*(k (w,a):G)*(y:G)⁻¹ = _
    rw [hk]
  have hker : f.ker = (centralizer (E : Set G)).subgroupOf Y := by
    rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  have hρpow (y : Y) (m : ℕ) : ρ y ^ m = 1 ↔ (y:G)^m ∈ centralizer (E : Set G) := by
    rw [←map_pow]
    change (MulAut.congr k.symm) (f (y^m)) = 1 ↔ _
    rw [←map_one (MulAut.congr k.symm),(MulAut.congr k.symm).injective.eq_iff]
    change y^m ∈ f.ker ↔ _
    rw [hker]
    rfl
  have hn (y : Y) (hy : ρ y ^ 4 = 1) : ρ y ^ 2 = 1 :=
    (hρpow y 2).mpr (hno4 y y.property ((hρpow y 4).mp hy))
  obtain ⟨_,e,he⟩ := nonabelian_binary_extension_kernel h earlier F hne g hgP hgH hsplit
  have hfull : ∀ a : MulAut W, ∃ y : Y, ρ y = a.prodCongr (MulEquiv.refl A) := by
    intro a
    obtain ⟨i,hi⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L))
      (e.symm (F.binaryPlaneLabel (by decide) a))
    refine ⟨⟨i,mem_sup_right i.property⟩,?_⟩
    apply MulEquiv.ext
    rintro ⟨w,a₀⟩
    apply k.injective
    apply Subtype.ext
    rw [hρ]
    change _ = (k (a w,a₀):G)
    have hea : (F.binaryPlaneLabel (by decide)).symm (e (QuotientGroup.mk i)) = a := by
      change QuotientGroup.mk i = _ at hi
      rw [hi,e.apply_symm_apply,MulEquiv.symm_apply_apply]
    rw [hk,he,hea]
  obtain ⟨_,hUsquare⟩ := F.localKernel_commutator_squares h.source.simpleQTKE L _ (by decide)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)
  have hUT : F.U ≤ (T : Subgroup G) := F.binary_U_le_sylow (by decide) hUsquare
  have hspan := F.U_eq_plane_span L (by decide) h.chosen.normalizes
    (F.localKernel_irreducible L (by decide) h.chosen.normalizes (fun _ => ⟨h.naturalMarking⟩))
  obtain ⟨b,hb,hbnot⟩ := Set.not_subset.mp (F.binary_U_not_centralizes_plane hspan hne)
  let bY : Y := ⟨b,hTY (hUT hb)⟩
  let σ : MulAut W := W.normalizerMonoidHom ⟨b,F.invariant 2 (hUT hb)⟩
  have hbρ : ρ bY = σ.prodCongr (MulEquiv.refl A) := by
    apply MulEquiv.ext
    rintro ⟨w,a⟩
    apply k.injective
    apply Subtype.ext
    rw [hρ]
    change _ = (k (σ w,a):G)
    rw [hk]
    have hba : b*(a:G)*b⁻¹ = a := mul_inv_eq_iff_eq_mul.mpr
      ((centerIn_le_centralizer _ a.property.2) b (le_conjugateSpanBy F.U (F.P L) hb))
    change b*((w:G)*(a:G))*b⁻¹ = (b*(w:G)*b⁻¹)*(a:G)
    calc
      b*((w:G)*(a:G))*b⁻¹ = (b*(w:G)*b⁻¹)*(b*(a:G)*b⁻¹) := by group
      _ = _ := by rw [hba]
  have hσ : σ ≠ 1 := by
    intro hh
    apply hbnot
    intro w hw
    have hh' := congrArg (fun a : MulAut W => (a ⟨w,hw⟩ : G)) hh
    change b*w*b⁻¹ = w at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzpoint : z ∈ F.Vi 1 := hpoint.symm ▸ mem_zpowers z
  let zW : W := ⟨z,F.monotone (by decide : 1 ≤ 2) hzpoint⟩
  have hzW : zW ≠ 1 := fun hh => hz (congrArg Subtype.val hh)
  have hσz : σ zW = zW := by
    apply Subtype.ext
    change b*z*b⁻¹ = z
    apply mul_inv_eq_iff_eq_mul.mpr
    exact ((normalizer_le_centralizer_of_card_two (F.Vi 1)
      (by simpa using F.card 1 (by decide))) (F.invariant 1 (hUT hb)) z hzpoint).symm
  have hPU := nonabelian_caseFive_parabolic_commutes_binary_seed h earlier F hne
    g hgP hgH B h5 C v hv hline c hnat hiZ hi
  have hcomm (p : G) (hp : p ∈ P) : Commute (ρ ⟨p,mem_sup_left hp⟩) (ρ bY) := by
    have hCE := hPU (commutator_mem_commutator hp hb)
    have hf : f ⁅(⟨p,mem_sup_left hp⟩ : Y),bY⁆ = 1 := by
      change ⁅(⟨p,mem_sup_left hp⟩ : Y),bY⁆ ∈ f.ker
      rw [hker]
      exact hCE
    have hh := congrArg (MulAut.congr k.symm) hf
    have hh' : ρ ⁅(⟨p,mem_sup_left hp⟩ : Y),bY⁆ = 1 := by
      simpa only [ρ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_one] using hh
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hh'
    change _ * _ = _ * _
    exact hh'
  apply hnot
  apply le_normalizer_iff.mpr
  intro p hp w hw
  have hh := BinaryPlaneCentralizer.product_plane_preserved
    (by simpa using F.card 2 (by decide)) hcA ρ hn hfull bY σ hbρ hσ zW hzW hσz
    ⟨p,mem_sup_left hp⟩ (hcomm p hp) ⟨w,hw⟩
  have heval := hρ ⟨p,mem_sup_left hp⟩ ⟨w,hw⟩ 1
  rw [hk,hh] at heval
  change _ * 1 = p * (w * 1) * p⁻¹ at heval
  simp only [mul_one] at heval
  rw [←heval]
  exact (ρ ⟨p,mem_sup_left hp⟩ (⟨w,hw⟩,1)).1.property

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
