module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.PositiveKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Offenders
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import CFSG.Quasithin.Chapter10.SourceThompsonNormalization

/-!
# Original binary-three normalizer actors

The natural quotient of the original moved group is a central cover with
its literal conjugation coordinates. Central-cover rigidity shows that every
common normalizer of L and [V,L] acts on [V,L] through L. Consequently J(T)
acts through L, and in the positive-kernel row every common-normalizer image
has the sharp offender bound. These are the actual actions used in the
omega-center argument of Aschbacher--Smith 10.2.8, printed p.749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The marked natural quotient gives a central cover of the original moved group. -/
theorem moved_cover (hmodel : BinaryThreeNatural D) :
    ∃ (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
      (σ : Representation (ZMod 2) BinaryLinearThree.Group (Additive (⁅D.fullModule,L⁆ : Subgroup G)))
      (p : σ.IntertwiningMap BinaryLinearThree.W),
      OneCohomology.IsCover p ∧
      (∀ (l : L) (w : Additive (⁅D.fullModule,L⁆ : Subgroup G)),
        ((σ (e (QuotientGroup.mk' (pCore 2 L) l)) w).toMul : G) =
          l * w.toMul * (l : G)⁻¹) ∧
      (∀ w : Additive (⁅D.fullModule,L⁆ : Subgroup G),
        p w=0 ↔ (w.toMul : G) ∈ sourceMovedFixed D) := by
  obtain ⟨e,⟨c⟩⟩ := hmodel
  let W := ⁅D.fullModule,L⁆
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨σ,hσ⟩ := BinaryConjugationSection.exists_action_of_central_kernel
    L W (normalizer_commutator_ge_right _ _) π hπ (by
      intro l hl
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        (e.injective (hl.trans e.map_one.symm))
      exact centralizer_le hWV (source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp)))
  obtain ⟨p,hp,hpcoord⟩ := c.exists_cover_of_fully_moved (specialLinearNatural 3) π hπ σ hσ
    inf_le_right (source_full_moved_eq_commutator D)
  refine ⟨e,σ,p,hp,hσ,?_⟩
  intro w
  rw [hpcoord w]
  exact c.coordinates_eq_one_iff w.toMul

/-- A common normalizer of the component and its actual moved factor acts on
that factor by an element of the same component. -/
theorem common_normalizer_acts_through_component (hmodel : BinaryThreeNatural D)
    {n : G} (hnL : n ∈ normalizer (L : Set G))
    (hnW : n ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ∃ l ∈ L, ∀ w ∈ ⁅D.fullModule,L⁆, n*w*n⁻¹ = l*w*l⁻¹ := by
  obtain ⟨e,σ,p,hp,hσ,hker⟩ := moved_cover D hmodel
  let W := ⁅D.fullModule,L⁆
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let α := W.normalizerMonoidHom ⟨n,hnW⟩
  change ∀ (l : L) (w : Additive W),
    ((σ (π l) w).toMul : G) = l*w.toMul*(l : G)⁻¹ at hσ
  let E : Additive W ≃ₗ[ZMod 2] Additive W := LinearEquiv.ofBijective
    (α.toMonoidHom.toAdditive.toZModLinearMap 2) α.bijective
  have hE (w : Additive W) : ((E w).toMul : G)=n*w.toMul*n⁻¹ := rfl
  have hk : ∀ w, p w=0 → p (E w)=0 := by
    intro w hw
    apply (hker _).mpr
    rw [hE]
    exact (mem_normalizer_iff.mp (source_original_moved_fixed_normalizer D ⟨hnL,hnW⟩)
      (w.toMul : G)).mp ((hker w).mp hw)
  have hnorm : ∀ g, ∃ h, ∀ w, E (σ g w)=σ h (E w) := by
    intro g
    obtain ⟨l,rfl⟩ := hπ g
    let k : L := ⟨n*l*n⁻¹,(mem_normalizer_iff.mp hnL l).mp l.property⟩
    refine ⟨π k,fun w => ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hE,hσ,hσ,hE]
    change n*((l : G)*w.toMul*(l : G)⁻¹)*n⁻¹ =
      (n*l*n⁻¹)*(n*w.toMul*n⁻¹)*(n*l*n⁻¹)⁻¹
    group
  obtain ⟨g,hg⟩ := OneCohomology.SLThreeCentralExtension.normalizing_equiv_eq_action
    p hp E hk hnorm
  obtain ⟨l,rfl⟩ := hπ g
  refine ⟨l,l.property,fun w hw => ?_⟩
  have he := congrArg (fun z : Additive W => (z.toMul : G)) (hg (Additive.ofMul ⟨w,hw⟩))
  rw [hE,hσ] at he
  exact he

/-- The original Thompson subgroup acts through L on its moved factor. -/
theorem thompson_le_linear_actor (hmodel : BinaryThreeNatural D) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
      L ⊔ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  intro n hn
  have hnL := D.thompson_normalizes_component hn
  have hnW : n ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
        (le_normalizer_componentOrbit L T (hJT hn))),
      mem_normalizer_iff_map_conj_eq.mp hnL]
  obtain ⟨l,hl,hact⟩ := common_normalizer_acts_through_component D hmodel hnL hnW
  have hc : l⁻¹*n ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    intro w hw
    have he := hact w hw
    have hh : (l⁻¹*n)*w*(l⁻¹*n)⁻¹ = w := by
      calc
        _ = l⁻¹*(n*w*n⁻¹)*l := by group
        _ = w := by rw [he]; group
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hm := (L ⊔ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)).mul_mem
    ((show L ≤ L ⊔ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) from le_sup_left) hl)
    ((show centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      L ⊔ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) from le_sup_right) hc)
  simpa only [mul_inv_cancel_left] using hm

/-- The actual faithful action of any common normalizer has no strong offender
in the positive-kernel row. -/
theorem common_normalizer_not_strong (hmodel : BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥) (H : Subgroup G)
    (hHL : H ≤ normalizer (L : Set G))
    (hHW : H ≤ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ¬ IsStrongFFModule (ChapterD.UniqueFactor.imageRepresentation H ⁅D.fullModule,L⁆ hHW) := by
  obtain ⟨e,σ,p,hp,hσ,_⟩ := moved_cover D hmodel
  let W := ⁅D.fullModule,L⁆
  let τ := ChapterD.UniqueFactor.imageRepresentation H W hHW
  apply OneCohomology.SLThreeCentralExtension.covered_action_not_strong σ p hp τ
    (ChapterD.UniqueFactor.imageRepresentation_injective H W hHW)
  · intro a
    obtain ⟨n,hn⟩ := a.property
    obtain ⟨l,hl,hact⟩ := common_normalizer_acts_through_component D hmodel
      (hHL n.property) (hHW n.property)
    refine ⟨e (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩),?_⟩
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ]
    have he : ((τ a w).toMul : G) = (n : G)*w.toMul*(n : G)⁻¹ := by
      change ((a.val w.toMul : W) : G) = _
      rw [←hn]
      rfl
    exact he.trans (hact w.toMul w.toMul.property)
  · have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at hh
    have hc : Nat.card (Additive W)=16 := moved_card_eq_sixteen D hmodel hne
    rw [hc] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2))
      (hh.symm.trans (by decide : 16=2^4))
end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
