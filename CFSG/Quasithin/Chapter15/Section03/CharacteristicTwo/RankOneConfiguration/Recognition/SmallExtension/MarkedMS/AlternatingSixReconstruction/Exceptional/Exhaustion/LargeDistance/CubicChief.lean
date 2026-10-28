module
public import Theory.Representation.BinaryOffender.EvenLift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCover
public import Theory.GroupAction.SymmetricSixChiefBudget.Quotient

/-!
# The cubic branch's chief-factor budget

A nontrivial simple binary action kills Q. The original component's normal
subgroup dichotomy then puts its kernel inside E; if the component acted
trivially, the two-group quotient would force the simple action to be trivial.
The even-lift displacement theorem gives cost at least two on every
noncentral chief factor, including those detecting E/Q. The fixed-index
product inequality bounds the number of such factors by one when the index
is at most eight. Jordan–Hölder then gives the residual dichotomy modulo Z.

The final theorem uses [V,Q], with Q the actual two-core, while the marked
S₆ action retains kernel E. CubicCentrality applies it to the literal graph
radius, discharging the index premise with CubicRadius. The required
restricted-actor commutator control and terminal exclusions remain in
qt-e-ms-small-a6-reconstruction.
Source: MS93 (5.2)(i)--(ii), printed pp.914--915. The quotient and chief-series
transports adapt Theory.GroupAction.SymmetricSixChiefBudget.Quotient.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open NoncentralChiefRefinement NoncentralChiefRefinement.SymmetricSixBudget
open scoped IsMulCommutative
universe u v
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "π" => CubicAction.projection h e hz hk

/-- Every nontrivial simple binary action retains the original even-involution cost,
including simple actions on which the cubic center is visible. -/
theorem simple_fixedCodim_lower {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) M W)
    [IsIrreducible ρ] (hne : ρ ≠ 1) (A : Subgroup M)
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map π) :
    2 ≤ fixedCodim ρ A := by
  have hQ : pCore 2 M ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  have hker : ρ.ker ≤ (π).ker := by
    rw [CubicAction.projection_kernel]
    rcases normal_over_core_dichotomy h e ρ.ker hQ with hE | hK
    · exact hE
    · exfalso
      have hres : pResidual 2 M ≤ ρ.ker := h.relative_residual ▸ hK
      let σ := quotientOfLEKer ρ (pResidual 2 M) hres
      let : IsIrreducible σ := (quotientOfLEKer_irreducible_iff ρ _ hres).mpr inferInstance
      have ht := normal_p_subgroup_le_ker σ ⊤
        ((isPGroup_quotient_pResidual 2).to_subgroup ⊤)
      apply hne
      ext g w
      exact LinearMap.congr_fun (ht (mem_top (QuotientGroup.mk' (pResidual 2 M) g))) w
  obtain ⟨x,hx,hxa⟩ := haA
  have hl := EvenLift.fixedCodim_lower π (CubicEven.projection_surjective h e hz hk)
    ρ hker x (hxa ▸ heven) (hxa ▸ ha)
  have hf := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr hx))
  have h₁ := fixedCodim_add_finrank ρ (zpowers x)
  have h₂ := fixedCodim_add_finrank ρ A
  omega

private theorem quotient_simple_fixedCodim_lower
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (f : M →* H) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ] (hne : ρ ≠ 1)
    (A : Subgroup M) (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map π) :
    2 ≤ fixedCodim ρ (A.map f) := by
  let : IsIrreducible (ρ.comp f) := (irreducible_comp_surjective_iff f hf ρ).mpr inferInstance
  have hn : ρ.comp f ≠ 1 := by
    intro he
    apply hne
    ext g w
    obtain ⟨x,rfl⟩ := hf g
    exact LinearMap.congr_fun (congrArg (fun τ => τ x) he) w
  have hl := simple_fixedCodim_lower h e hz hk (ρ.comp f) hn A a ha heven haA
  unfold fixedCodim at hl ⊢
  rwa [Representation.BinaryOffender.fixedSpace_comp_map ρ f A] at hl

private theorem quotient_simple_group_fixedIndex_lower
    {H W : Type*} [Group H] [Group W] [Finite W] [IsElementaryAbelian 2 W]
    [MulDistribMulAction H W] [Nontrivial W]
    (f : M →* H) (hf : Function.Surjective f)
    (A : Subgroup M) (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map π)
    (hirr : ∀ D : Subgroup W, (∀ g : H, ∀ w : W, w ∈ D → g • w ∈ D) →
      D = ⊥ ∨ D = ⊤)
    (hne : ¬ ∀ g : H, ∀ w : W, g • w = w) :
    4 ≤ (FixedPoints.subgroup (A.map f) W).index := by
  classical
  let ρ := Representation.ofElementaryAbelianAction (A := H) (G := W) (p := 2)
  let : IsIrreducible ρ := by
    rw [Representation.IsIrreducible, isSimpleOrder_iff]
    refine ⟨inferInstance, ?_⟩
    intro U
    let D : Subgroup W := AddSubgroup.toSubgroup' U.toSubmodule.toAddSubgroup
    rcases hirr D (fun g w hw => U.apply_mem_toSubmodule g hw) with hd | hd
    · left
      apply bot_unique
      intro v hv
      have hh : v.toMul ∈ D := hv
      rw [hd, Subgroup.mem_bot] at hh
      exact hh
    · right
      apply top_unique
      intro v _
      have hv : v.toMul ∈ D := by rw [hd]; trivial
      exact hv
  have hnρ : ρ ≠ 1 := by
    intro he
    apply hne
    intro g w
    exact congrArg (fun τ : Representation (ZMod 2) H (Additive W) => τ g (Additive.ofMul w)) he
  have hl := quotient_simple_fixedCodim_lower h e hz hk f hf ρ hnρ A a ha heven haA
  have hfix : fixedSpace (ρ.comp (A.map f).subtype) ⊤ = fixedSpace ρ (A.map f) := by
    ext v
    constructor
    · intro hv g
      exact hv ⟨g, mem_top g⟩
    · intro hv g
      exact hv g.val
  have hc := fixed_subgroup_index (ρ.comp (A.map f).subtype)
  rw [fixedCodim, hfix] at hc
  have hg : AddSubgroup.toSubgroup' (fixedSpace ρ (A.map f)).toAddSubgroup =
      FixedPoints.subgroup (A.map f) W := by ext w; rfl
  rw [hg] at hc
  rw [hc]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl

/-- On every literal quotient, index at most eight permits at most one
noncentral binary chief factor. The actual cubic kernel is retained. -/
theorem quotient_noncentralCount_le_one {H : Type*} [Group H] [Finite H]
    (f : M →* H) (hf : Function.Surjective f)
    (U : Subgroup H) [U.Normal] (hU : IsPGroup 2 U)
    (A : Subgroup M) (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map π)
    (hindex : (centralizer (A.map f : Set H)).relIndex U ≤ 8)
    (s : SeriesOn U) : s.noncentralCount ≤ 1 := by
  apply count_le_one_of_index s (A.map f) _ hindex
  intro i hi
  let := s.factor_elementary hU i
  let := s.factor_nontrivial i
  let μ : MulDistribMulAction H (s.Factor i) := MulDistribMulAction.compHom _ (s.action i)
  let := μ
  exact quotient_simple_group_fixedIndex_lower h e hz hk f hf A a ha heven haA
    (s.factor_irreducible i) (fun ht => hi ((s.central_iff_action i).mpr ht))

/-- The unique-chief-layer consequence modulo the original Z, for any normal
subgroup of the original two-group. No elementary or split quotient is assumed. -/
theorem residual_dichotomy_modulo
    (V Z : Subgroup M) [V.Normal] [Z.Normal] (_hZV : Z ≤ V)
    (hV : IsPGroup 2 V) (A : Subgroup M)
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map π)
    (hindex : (centralizerModulo V A Z).relIndex V ≤ 8)
    (X : Subgroup M) [X.Normal] (hXV : X ≤ V) :
    ⁅X,pResidual 2 M⁆ ≤ Z ∨ ⁅V,pResidual 2 M⁆ ≤ X ⊔ Z := by
  let f := QuotientGroup.mk' Z
  let : (V.map f).Normal := Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective Z)
  let : (X.map f).Normal := Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective Z)
  have hi : (centralizer (A.map f : Set (M ⧸ Z))).relIndex (V.map f) ≤ 8 := by
    rwa [centralizerModulo_relIndex_eq] at hindex
  obtain ⟨s⟩ := SeriesOn.exists_series (V.map f)
  have hs := quotient_noncentralCount_le_one h e hz hk f (QuotientGroup.mk'_surjective Z)
    (V.map f) (hV.map f) A a ha heven haA hi s
  have hh : ⁅X.map f,pResidual 2 (M ⧸ Z)⁆ = ⊥ ∨
      ⁅V.map f,pResidual 2 (M ⧸ Z)⁆ ≤ X.map f := by
    by_cases hz : s.noncentralCount = 0
    · right
      have hp : IsPGroup 2 s.series.last.val := by rw [s.last_eq]; exact hV.map f
      have ht := s.series.residual_commutator_le_head_of_central_steps hp
        (s.noncentralCount_eq_zero_iff.mp hz)
      rw [s.last_eq,s.head_eq] at ht
      exact ht.trans bot_le
    · exact s.residual_dichotomy_of_count_one (hV.map f) (by omega) (X.map f) (map_mono hXV)
  have hres : (pResidual 2 M).map f = pResidual 2 (M ⧸ Z) := map_pResidual_quotient 2 Z
  rcases hh with hh | hh
  · left
    have hm : (⁅X,pResidual 2 M⁆).map f ≤ ⊥ := by rw [map_commutator,hres,hh]
    have ht := map_le_iff_le_comap.mp hm
    simpa only [MonoidHom.comap_bot,f,QuotientGroup.ker_mk'] using ht
  · right
    have hm : (⁅V,pResidual 2 M⁆).map f ≤ X.map f := by rwa [map_commutator,hres]
    have ht := map_le_iff_le_comap.mp hm
    simpa only [comap_map_eq,f,QuotientGroup.ker_mk'] using ht

/-- Source (5.2)'s alternative uses Q, the actual two-core, while the marked
six-letter action still has kernel E with E/Q of order three. -/
theorem core_commutator_residual_dichotomy_of_index
    (V Z : Subgroup M) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ pCore 2 M)
    (A : Subgroup M) (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map π)
    (B : Subgroup M) (hc : ⁅V ⊓ B,A⁆ ≤ Z) (hindex : B.relIndex V ≤ 8) :
    ⁅⁅V,pCore 2 M⁆,pResidual 2 M⁆ ≤ Z ∨
      ⁅V,pResidual 2 M⁆ ≤ ⁅V,pCore 2 M⁆ ⊔ Z :=
  residual_dichotomy_modulo h e hz hk V Z hZV (pCore_isPGroup.to_le hV) A a ha heven haA
    ((centralizerModulo_relIndex_le_of_commutator V A Z B hc).trans hindex)
    ⁅V,pCore 2 M⁆ (commutator_le_left _ _)

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
