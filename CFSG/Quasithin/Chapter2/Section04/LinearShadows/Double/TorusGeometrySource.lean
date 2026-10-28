module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.TorusGeometry
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.BorelSource

/-!
# The original double-linear torus after its fixed subgroup vanishes

The initial Borel torus and original C.5 setup retain their literal Sylow
intersections and conjugate modules. Triviality of the common fixed group
removes the central factor, identifies both block cores, and supplies the
faithful actions, maximal torus kernels, and fixed outside conjugator used
in the new local subgroup on printed p.540.

Source: Aschbacher–Smith, proof of 2.4.7, printed p.540.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearDouble
open ChapterC.Section05.ConjugateSource LinearShadows.Double
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

structure TorusGeometryData {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}
    (c : DoubleLinearSourceSetup d M₀ n)
    (b : PairedBorelData M ((d.S : Subgroup d.H).map d.H.subtype)
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
      (d.block.map d.H.subtype) c.second d.H n) (x : G) where
  central_factor :
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (((d.block.map d.H.subtype) ⊔ c.second : Subgroup G) : Set G) = ⊥
  core : twoCore d.H = sourceModule (d.block.map d.H.subtype) ⊔ sourceModule c.second
  span :
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) =
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ (d.block.map d.H.subtype)) ⊔
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ c.second)
  blocks_disjoint : Disjoint (d.block.map d.H.subtype) c.second
  disjoint : Disjoint
    (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ (d.block.map d.H.subtype))
    (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ c.second)
  nontrivial_first :
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ (d.block.map d.H.subtype) ≠ ⊥
  nontrivial_second :
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ c.second ≠ ⊥
  faithful_first : Function.Injective
    ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      (d.block.map d.H.subtype)).normalizerMonoidHom.comp (inclusion b.first.normalizes_sylow))
  faithful_second : Function.Injective
    ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      c.second).normalizerMonoidHom.comp (inclusion b.second.normalizes_sylow))
  cross_first : c.second ≤ centralizer
    (((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      (d.block.map d.H.subtype)) ⊔ b.first.torus : Subgroup G) : Set G)
  cross_second : (d.block.map d.H.subtype) ≤ centralizer
    (((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      c.second) ⊔ b.second.torus : Subgroup G) : Set G)
  fixes_first_torus : x ∈ normalizer (b.first.torus : Set G)
  fixes_second_torus : x ∈ normalizer (b.second.torus : Set G)
  fixes_first_sylow : x ∈ normalizer
    ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      (d.block.map d.H.subtype) : Subgroup G) : Set G)
  fixes_second_sylow : x ∈ normalizer
    ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      c.second : Subgroup G) : Set G)
  moved_second : c.second.map (MulAut.conj x⁻¹).toMonoidHom ≠ c.second
  kernels : ∀ A : Subgroup G, A ≤ b.torus →
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (A : Set G) ≠ ⊥ → A ≤ b.first.torus ∨ A ≤ b.second.torus
  centerless_first : center (d.block.map d.H.subtype) = ⊥
  centerless_second : center c.second = ⊥
  core_first : pCore 2 (d.block.map d.H.subtype) = ChapterC.blockU (d.block.map d.H.subtype)
  core_second : pCore 2 c.second = ChapterC.blockU c.second

private theorem second_noncommuting {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}
    (c : DoubleLinearSourceSetup d M₀ n)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    ¬ (sourceModule c.second).map (MulAut.conj c.x⁻¹).toMonoidHom ≤
      centralizer (sourceModule c.second : Set G) := by
  let := c.field₁_field
  let := c.field₂_field
  have hex : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = c.second := by
    obtain ⟨s,hs,he⟩ := c.exchange
    exact ⟨⟨s,hSM hs⟩,hs,he⟩
  exact RankOne.second_noncommuting (c.marked₁.fourModuleSourceInputs c.commutes
    c.marked₂.module_le M₀ ((d.S : Subgroup d.H).map d.H.subtype) c.x c.x_mem
    (c.original.R_normal c.x_mem) hi c.permutes hex c.noncommuting)

/-- All post-fixed-point conclusions on the literal original two blocks and
Borel torus. The parent torus construction supplies the fixed-zero premise
and preserves the two specified conjugate modules of its outside element. -/
theorem source_torus_geometry
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    {M₀ : Subgroup G} {n : ℕ} (c : DoubleLinearSourceSetup d M₀ n)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀) (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (b : PairedBorelData M ((d.S : Subgroup d.H).map d.H.subtype)
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
      (d.block.map d.H.subtype) c.second d.H n)
    (hfixed : Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (b.torus : Set G) = ⊥)
    (hbound₁ : pCore 2 (d.block.map d.H.subtype) ≤
      ChapterC.blockU (d.block.map d.H.subtype) ⊔ center (d.block.map d.H.subtype))
    (hbound₂ : pCore 2 c.second ≤ ChapterC.blockU c.second ⊔ center c.second)
    (hQdec : twoCore d.H = (sourceModule (d.block.map d.H.subtype) ⊔ sourceModule c.second) ⊔
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (((d.block.map d.H.subtype) ⊔ c.second : Subgroup G) : Set G)))
    (x : G)
    (hxR : x ∈ normalizer (Stellmacher.elementaryAbelianMaxJ
      ((d.S : Subgroup d.H).map d.H.subtype) : Set G))
    (hxD : x ∈ normalizer (b.torus : Set G))
    (hxU₁ : (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom =
      (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj c.x⁻¹).toMonoidHom)
    (hxU₂ : (sourceModule c.second).map (MulAut.conj x⁻¹).toMonoidHom =
      (sourceModule c.second).map (MulAut.conj c.x⁻¹).toMonoidHom) :
    Nonempty (TorusGeometryData c b x) := by
  let := c.field₁_field
  let := c.field₂_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let L₁ := d.block.map d.H.subtype
  let L₂ := c.second
  let R₁ := R ⊓ L₁
  let R₂ := R ⊓ L₂
  let D₁ := b.first.torus
  let D₂ := b.second.torus
  have hD₁ : D₁ ≤ L₁ := b.first.le_intersection.trans inf_le_right
  have hD₂ : D₂ ≤ L₂ := b.second.le_intersection.trans inf_le_right
  have hD : b.torus ≤ L₁ ⊔ L₂ := sup_le (hD₁.trans le_sup_left) (hD₂.trans le_sup_right)
  have hP₁ : (b.first.sylow : Subgroup L₁).map L₁.subtype ≤ R := b.first.sylow_eq.le.trans inf_le_left
  have hP₂ : (b.second.sylow : Subgroup L₂).map L₂.subtype ≤ R := b.second.sylow_eq.le.trans inf_le_left
  have hc : L₁ ≤ centralizer (L₂ : Set G) := le_centralizer_iff.mp c.commutes
  have hz₁ := short_center_eq_bot_of_fixed_zero L₁ L₂ R b.torus
    c.marked₁.short b.first.sylow hP₁ c.commutes hD hfixed
  have hz₂ := short_center_eq_bot_of_fixed_zero L₂ L₁ R b.torus
    c.marked₂.short b.second.sylow hP₂ hc (by simpa only [sup_comm] using hD) hfixed
  change pCore 2 L₁ ≤ ChapterC.blockU L₁ ⊔ center L₁ at hbound₁
  change pCore 2 L₂ ≤ ChapterC.blockU L₂ ⊔ center L₂ at hbound₂
  have hcore₁ : pCore 2 L₁ = ChapterC.blockU L₁ :=
    le_antisymm (by simpa only [hz₁,sup_bot_eq] using hbound₁) ChapterC.blockU_le_core
  have hcore₂ : pCore 2 L₂ = ChapterC.blockU L₂ :=
    le_antisymm (by simpa only [hz₂,sup_bot_eq] using hbound₂) ChapterC.blockU_le_core
  have hC : R ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) = ⊥ := by
    apply bot_unique
    rw [←hfixed]
    exact inf_le_inf_left R (centralizer_le hD)
  have hspan : R = R₁ ⊔ R₂ := by
    have hh := (source_decomposition d hG T hST c hL hSM hMT hi).1
    change R = (R₁ ⊔ R₂) ⊔ (R ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G)) at hh
    simpa only [hC,sup_bot_eq] using hh
  have hQ : twoCore d.H = sourceModule L₁ ⊔ sourceModule L₂ := by
    change twoCore d.H = (sourceModule L₁ ⊔ sourceModule L₂) ⊔
      (R ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G)) at hQdec
    simpa only [hC,sup_bot_eq] using hQdec
  have hdis := commuting_blocks_disjoint L₁ L₂ R b.torus c.marked₁.short
    b.first.sylow hP₁ c.commutes hD hfixed
  have hR₁ne : R₁ ≠ ⊥ := fun he =>
    short_sylow_ne_bot L₁ c.marked₁.short b.first.sylow (b.first.sylow_eq.trans he)
  have hR₂ne : R₂ ≠ ⊥ := fun he =>
    short_sylow_ne_bot L₂ c.marked₂.short b.second.sylow (b.second.sylow_eq.trans he)
  have hfree₁ := centerless_sylow_odd_free L₁ D₁ R₁ hL hcore₁ hz₁
    b.first.sylow b.first.sylow_eq hD₁ b.first.odd
  have hfree₂ := centerless_sylow_odd_free L₂ D₂ R₂ c.second_type hcore₂ hz₂
    b.second.sylow b.second.sylow_eq hD₂ b.second.odd
  have hRcomm : R₁ ≤ centralizer (R₂ : Set G) :=
    inf_le_right.trans (hc.trans (centralizer_le inf_le_right))
  have hfix₂ : R ⊓ centralizer (D₂ : Set G) = R₁ := by
    rw [hspan]
    exact paired_torus_fixed_space R₁ R₂ D₂ hRcomm
      (inf_le_right.trans (hc.trans (centralizer_le hD₂))) b.second.nontrivial hfree₂
  have hfix₁ : R ⊓ centralizer (D₁ : Set G) = R₂ := by
    rw [hspan,sup_comm]
    exact paired_torus_fixed_space R₂ R₁ D₁ (le_centralizer_iff.mp hRcomm)
      (inf_le_right.trans (c.commutes.trans (centralizer_le hD₁))) b.first.nontrivial hfree₁
  have hmax : ∀ A : Subgroup G, A ≤ b.torus → R ⊓ centralizer (A : Set G) ≠ ⊥ →
      A ≤ D₁ ∨ A ≤ D₂ := by
    intro A hA hne
    apply paired_torus_kernel_dichotomy L₁ L₂ R₁ R₂ D₁ D₂ hdis hc
      inf_le_right inf_le_right hD₁ hD₂ hfree₁ hfree₂ A hA
    rwa [←hspan]
  have hDne : D₁ ≠ D₂ := by
    intro he
    apply b.first.nontrivial
    have hd : Disjoint D₁ D₂ := b.disjoint
    rw [←he] at hd
    exact disjoint_self.mp hd
  have hU : sourceModule L₁ ≤ R₁ :=
    (map_mono (ChapterC.blockU_le_core.trans (fitting_pCore_le_sylow b.first.sylow))).trans_eq b.first.sylow_eq
  have hnc : ¬ (sourceModule L₁).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule L₁ : Set G) :=
    hxU₁ ▸ c.noncommuting
  have hx := fixed_torus_factors_of_noncommuting R b.torus R₁ R₂ D₁ D₂ (sourceModule L₁)
    hR₁ne hR₂ne hU (le_centralizer_iff.mp hRcomm) le_sup_left le_sup_right
    (b.first.card.trans b.second.card.symm) hDne hfix₁ hfix₂ hmax x hxR hxD hnc
  have hmove : L₂.map (MulAut.conj x⁻¹).toMonoidHom ≠ L₂ := by
    intro he
    have hnc₂ := second_noncommuting c hSM hi
    apply hnc₂
    rw [←hxU₂]
    change (RankOne.U L₂).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U L₂ : Set G)
    rw [RankOne.U_map_equiv,he]
    let := c.marked₂.elementary
    exact le_centralizer _
  exact ⟨{
    central_factor := hC, core := hQ, span := hspan, blocks_disjoint := hdis,
    disjoint := hdis.mono inf_le_right inf_le_right,
    nontrivial_first := hR₁ne, nontrivial_second := hR₂ne,
    faithful_first := short_odd_sylow_faithful L₁ D₁ R₁ c.marked₁.short
      b.first.sylow b.first.sylow_eq hD₁ b.first.odd b.first.normalizes_sylow,
    faithful_second := short_odd_sylow_faithful L₂ D₂ R₂ c.marked₂.short
      b.second.sylow b.second.sylow_eq hD₂ b.second.odd b.second.normalizes_sylow,
    cross_first := c.commutes.trans (centralizer_le (sup_le inf_le_right hD₁)),
    cross_second := hc.trans (centralizer_le (sup_le inf_le_right hD₂)),
    fixes_first_torus := hx.1, fixes_second_torus := hx.2.1,
    fixes_first_sylow := hx.2.2.1, fixes_second_sylow := hx.2.2.2,
    moved_second := hmove, kernels := hmax, centerless_first := hz₁,
    centerless_second := hz₂, core_first := hcore₁, core_second := hcore₂ }⟩

end CFSG.Quasithin.Chapter2.LinearDouble
