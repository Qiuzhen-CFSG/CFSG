module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedLinearCommutator
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedLinearIndices
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearStability
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearCommutator

/-!
# Stabilization of the mixed commutator by the conjugate parabolic: structure at the original group

The original linear quotient has order 168, the parabolic has index seven,
and its radical has index six. Retaining the actual centralizer kernel
therefore gives |R₂:C_R₂(V₀)|=4. In a noncommuting reciprocal pair V has
this same action index on V₀ᵍ, so its image fills the image of R₂ᵍ.
Consequently [R₂ᵍ,V₀ᵍ]=[V,V₀ᵍ], and (L₂T)ᵍ normalizes this subgroup.

The original fixed generator is weakly closed in every subgroup of V
containing it, using the same earlier normalizer-fusion premise retained
by Terminal. Since the mixed commutator contains C_V(L), this puts the
actual conjugate (L₂T)ᵍ in M=N_G(L). Fusion retains its existing earlier
source producer and final discharge with the fixed-core assembly.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/MixedLinearStability` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

open Stellmacher Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

omit [Finite G] in
private theorem conjugation_image_card_at (A U : Subgroup G)
    (hAU : A ≤ normalizer (U : Set G)) :
    Nat.card (U.normalizerMonoidHom.comp (inclusion hAU)).range =
      (centralizer (U : Set G)).relIndex A := by
  let f := U.normalizerMonoidHom.comp (inclusion hAU)
  have hk : f.ker = (centralizer (U : Set G)).subgroupOf A := by
    ext a
    change inclusion hAU a ∈ U.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  rw [←index_ker,hk]
  rfl

private theorem commutator_eq_of_equal_action_index_at
    (A R U : Subgroup G) (hAR : A ≤ R) (hRU : R ≤ normalizer (U : Set G))
    (hi : (centralizer (U : Set G)).relIndex A =
      (centralizer (U : Set G)).relIndex R) : ⁅R,U⁆ = ⁅A,U⁆ := by
  let f := U.normalizerMonoidHom.comp (inclusion hRU)
  let a := U.normalizerMonoidHom.comp (inclusion (hAR.trans hRU))
  have hle : a.range ≤ f.range := by
    rintro y ⟨x,rfl⟩
    exact ⟨inclusion hAR x,rfl⟩
  have hr : a.range = f.range := eq_of_le_of_card_ge hle (by
    rw [conjugation_image_card_at,conjugation_image_card_at,hi])
  apply le_antisymm ?_ (commutator_mono hAR le_rfl)
  apply commutator_le.mpr
  intro r hrR u hu
  have hh : f ⟨r,hrR⟩ ∈ a.range := hr.symm ▸ (show f ⟨r,hrR⟩ ∈ f.range from ⟨⟨r,hrR⟩,rfl⟩)
  obtain ⟨b,hb⟩ := hh
  have he := congrArg (fun t : MulAut U => (t ⟨u,hu⟩).val) hb
  change b.val*u*b.val⁻¹ = r*u*r⁻¹ at he
  have hc : ⁅r,u⁆ = ⁅b.val,u⁆ := by
    simp only [commutatorElement_def]
    rw [←he]
  rw [hc]
  exact commutator_mem_commutator b.property hu

omit [Finite G] in
private theorem centralizer_index_conjugate_at (A B : Subgroup G) (g : G) :
    (centralizer (A.conjBy g : Set G)).relIndex (B.conjBy g) =
      (centralizer (A : Set G)).relIndex B := by
  change (centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
    (B.map (MulAut.conj g).toMonoidHom) = _
  rw [coe_map, MulEquiv.coe_toMonoidHom,
    ← Theory.GroupTheory.map_centralizer_equiv (A : Set G) (MulAut.conj g)]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

/-- The actual conjugate plane parabolic preserves the mixed commutator.
Its whole radical has exactly the same action as V on the conjugate module. -/
theorem original_linear_pair_mixed_stability_at
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
    (hBM : B ≤ normalizer (L : Set G)) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ →
      ⁅(B.pCoreIn 2).conjBy g,U.conjBy g⁆ = ⁅V,U.conjBy g⁆ ∧
      B.conjBy g ≤ normalizer (⁅V,U.conjBy g⁆ : Subgroup G) := by
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
  have hindex := original_linear_pair_radical_index h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hlin
  have hBU : B ≤ normalizer (U : Set G) := le_sup_right.trans (le_normalizer_conjugateSpanBy _ _)
  have hBR : B ≤ normalizer (B.pCoreIn 2 : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  dsimp only
  intro g h₁ h₂ hm
  obtain ⟨_,hh⟩ := original_linear_pair_mixed_indices_and_centralizers_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 hlin hBM
  have hi := (hh g h₁ h₂ hm).1
  have hBgU : B.conjBy g ≤ normalizer (U.conjBy g : Set G) :=
    (map_mono hBU).trans (U.le_normalizer_map (MulAut.conj g).toMonoidHom)
  have hBgR : B.conjBy g ≤ normalizer ((B.pCoreIn 2).conjBy g : Set G) :=
    (map_mono hBR).trans ((B.pCoreIn 2).le_normalizer_map (MulAut.conj g).toMonoidHom)
  have hc := commutator_eq_of_equal_action_index_at V ((B.pCoreIn 2).conjBy g) (U.conjBy g)
    h₂ ((map_mono (pCoreIn_le 2 B)).trans hBgU)
    (hi.trans ((centralizer_index_conjugate_at U (B.pCoreIn 2) g).trans hindex).symm)
  refine ⟨hc,?_⟩
  intro b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [←hc,map_commutator,mem_normalizer_iff_map_conj_eq.mp (hBgR hb),
    mem_normalizer_iff_map_conj_eq.mp (hBgU hb)]

/-- The distinguished fixed involution is weakly closed in every subgroup
of V containing it, using the retained original normalizer-fusion input. -/
theorem normalizer_fixed_line_section_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (Y : Subgroup G) (hYV : Y ≤ V) (hZY : V ⊓ centralizer (L : Set G) ≤ Y) :
    normalizer (Y : Set G) ≤ normalizer (L : Set G) := by
  intro x hx
  have hzY := hZY ⟨m.constant.property,m.constant_fixed⟩
  have hz : MulAut.conj x m.constant.val ∈ V := hYV
    ((mem_normalizer_iff.mp hx m.constant.val).mp hzY)
  obtain ⟨n,hn,he⟩ := hfusion m.constant m.constant_ne_one _ hz
    (isConj_iff.mpr ⟨x,rfl⟩)
  have hnM : n ∈ normalizer (L : Set G) :=
    (normalizer_component_eq_module_at h structural D m).symm ▸ hn
  have hnz := (normalizer_component_le_fixed_centralizer_at h structural D m hnM)
    m.constant.val ⟨m.constant.property,m.constant_fixed⟩
  have hfix : MulAut.conj n m.constant.val = m.constant.val :=
    mul_inv_eq_iff_eq_mul.mpr hnz.symm
  rw [hfix] at he
  rw [←fixed_generator_centralizer_at h structural D m
    ⟨m.constant.property,m.constant_fixed⟩
    (fun hh => m.constant_ne_one (Subtype.ext hh))]
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he.symm)

/-- The weak-closure step in the original mixed linear pair puts the actual
conjugate L₂T in M. The fusion premise is the same earlier input retained
by the terminal source consumer. -/
theorem original_linear_pair_mixed_normalizer_at
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
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ → B.conjBy g ≤ normalizer (L : Set G) := by
  dsimp only
  intro g h₁ h₂ hm
  obtain ⟨hfixed,_,_,hZ⟩ := original_linear_pair_mixed_commutator_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 hlin W hW hTW hB
    g h₁ h₂ hm
  have hBM : B ≤ normalizer (L : Set G) := by
    rw [hB]
    exact inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hst := (original_linear_pair_mixed_stability_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 hlin hBM
    g h₁ h₂ hm).2
  exact hst.trans (normalizer_fixed_line_section_at h structural D m hfusion _
    (hfixed.le.trans inf_le_left) hZ)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
