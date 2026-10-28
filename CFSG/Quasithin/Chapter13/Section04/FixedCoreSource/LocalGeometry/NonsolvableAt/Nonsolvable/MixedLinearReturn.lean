module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedLinearCommutator
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedLinearIndices
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedLinearStability
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedPlaneReturn
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearReturn
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedPlaneReturn

/-!
# The mixed conjugator and the two core commutators: structure at the original group

Weak closure of the distinguished fixed involution, together with the
already constructed containment Ω₁Z(T) ≤ V, controls N_G(T). Sylow
conjugacy now returns the original mixed conjugator g to M. The original
plane action then returns that same g to L₂T, so V₀ᵍ=V₀.

Both literal fixed groups equal [V,V₀]. The two cores centralize their
own modules and normalize the other, which gives [O₂(M),V₀] ≤ V and
[O₂(H₀),V] ≤ V₀. These are the inputs to the ensuing block argument.
The block and socle exclusions, product case of 13.4.16, graph and final
offender contradiction remain with the nonsolvable source assembly.
All earlier-source premises retain their producers; the original fusion
premise is not inferred from nonsolvability at a single escaping point.
Source: Aschbacher--Smith 13.4.15, printed p.912, refs/quasithin.pdf.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/MixedLinearReturn` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem sylow_return_at (M : Subgroup G) (hT : (T : Subgroup G) ≤ M)
    (hN : normalizer (T : Set G) ≤ M) (g : G)
    (hg : (T : Subgroup G).conjBy g ≤ M) : g ∈ M := by
  have hg' : ((g • T : Sylow 2 G) : Subgroup G) ≤ M := hg
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq M ((g • T).subtype hg') (T.subtype hT)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hn
  have hh : n.val * g ∈ normalizer (T : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hn)
  have hm := M.mul_mem (M.inv_mem n.property) (hN hh)
  simpa only [inv_mul_cancel_left] using hm

/-- The full omega-center containment and original normalizer fusion
control the Sylow normalizer through the distinguished fixed line. -/
theorem sylow_normalizer_of_omega_in_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let K : Subgroup (T : Subgroup G) :=
    (omega₁ (G := center (T : Subgroup G)) (p := 2)).map (center (T : Subgroup G)).subtype
  let _ : (omega₁ (G := center (T : Subgroup G)) (p := 2)).Characteristic :=
    omega₁_characteristic (center (T : Subgroup G))
  let _ : K.Characteristic := inferInstance
  have hn : normalizer (T : Set G) ≤ normalizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    normalizer_le_normalizer_characteristic_image (T : Subgroup G) K
  exact hn.trans (normalizer_fixed_line_section_at h structural D m hfusion _ hZV
    (LocalGeometry.fixed_le_original_omegaCenter_at h structural D m))


open Chapter14.Section03.FaithfulSource Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

/-- The same original mixed conjugator returns to M and L₂T. The orbit
module is fixed, and both core commutators lie in the opposite module,
as required before the block argument of source 13.4.15. -/
theorem original_linear_pair_mixed_return_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ → g ∈ normalizer (L : Set G) ∧ g ∈ B ∧ U.conjBy g = U ∧
        ⁅V,U⁆ = V ⊓ centralizer (U : Set G) ∧
        ⁅V,U⁆ = U ⊓ centralizer (V : Set G) ∧
        ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,U⁆ ≤ V ∧
        ⁅(A ⊔ B).pCoreIn 2,V⁆ ≤ U := by
  let X := A ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hUX : U ≤ X := conjugateSpanBy_le (hZT.trans hTX) X.le_normalizer
  have hXU : X ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hBM : B ≤ normalizer (L : Set G) := by
    rw [hB]
    exact inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hkernel := Amalgam.original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB
  have hUcore : U ≤ X.pCoreIn 2 := by
    have hh := map_mono (f := X.subtype) hkernel.1.le_pCore
    rwa [map_subgroupOf_eq_of_le hUX] at hh
  have hUT : U ≤ (T : Subgroup G) := by
    exact fun u hu => pCore_isPGroup.le_sylow_of_normal (T.subtype hTX)
      (hkernel.1.le_pCore (show (⟨u,hUX hu⟩ : X) ∈ U.subgroupOf X from hu))
  have hUR : U ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 X).to_le hUcore) (hUT.trans hTB) (le_sup_right.trans hXU)
  have hN := sylow_normalizer_of_omega_in_core_at h structural D m hZV hfusion
  dsimp only
  intro g h₁ h₂ hm
  have hBg := original_linear_pair_mixed_normalizer_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 hlin W hW hTW hB hfusion
    g h₁ h₂ hm
  have hgM := sylow_return_at (normalizer (L : Set G)) D.sylow_normalizes_component hN g
    ((map_mono hTB).trans hBg)
  have hi := ((original_linear_pair_mixed_indices_and_centralizers_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 hlin hBM).2
    g h₁ h₂ hm).2.1
  have hgB : g ∈ B := by
    rw [hB]
    exact original_plane_radical_return_at h structural D m eL W hW hTW U
      (hB ▸ hUR) g (hM ▸ hgM) (hB ▸ h₁) hi
  have hUg : U.conjBy g = U := mem_normalizer_iff_map_conj_eq.mp
    (hXU (mem_sup_right hgB))
  obtain ⟨hcV,hcU,_,_⟩ := original_linear_pair_mixed_commutator_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 hlin W hW hTW hB
    g h₁ h₂ hm
  change ⁅V,U.conjBy g⁆ = _ at hcV hcU
  rw [hUg] at hcV hcU
  have hQU : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (U : Set G) := by
    apply le_trans _ (hTX.trans hXU)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hUQ : U ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (hUT.trans le_sup_right).trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hQX : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] using
      pCoreIn_le_sylow X (T.subtype hTX)
  have hQV : X.pCoreIn 2 ≤ normalizer (V : Set G) :=
    hQX.trans (D.sylow_normalizes_component.trans (normalizer_component_le_module_at h structural D m))
  have hVQ : V ≤ normalizer (X.pCoreIn 2 : Set G) :=
    (D.le_sylow.trans hTX).trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  refine ⟨hgM,hgB,hUg,hcV,hcU,?_,?_⟩
  · have hh : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,U⁆ ≤ U ⊓ centralizer (V : Set G) :=
      le_inf (le_normalizer_iff_commutator_le_right.mp hQU)
        ((le_normalizer_iff_commutator_le_left.mp hUQ).trans D.core_centralizes)
    exact hh.trans (hcU.symm.le.trans (hcV.le.trans inf_le_left))
  · have hh : ⁅X.pCoreIn 2,V⁆ ≤ V ⊓ centralizer (U : Set G) :=
      le_inf (le_normalizer_iff_commutator_le_right.mp hQV)
        ((le_normalizer_iff_commutator_le_left.mp hVQ).trans
          (hkernel.2.2.1.symm.le.trans inf_le_right))
    exact hh.trans (hcV.symm.le.trans (hcU.le.trans inf_le_left))
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
