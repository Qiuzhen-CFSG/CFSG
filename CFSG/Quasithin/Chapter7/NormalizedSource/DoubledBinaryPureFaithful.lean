module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFixed
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureIntersection
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.MaximalAction
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.CharacteristicCentralizerFusion
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddCore

/-!
# Faithfulness at the original H1 pure line

The singular-free component fixed subgroup contains the actual pure line.
If its order exceeded four, its pointwise automizer would be trivial.
The proved moving-element consequence of E.6.11, via E.6.12, would then
force r = 1, contradicting the original r ≥ 3. This proves the required
small fixed-subgroup bound without an extra normal-seven input.

The plane residual lifts a cubic fixing precisely the paired plane, so
it has no fixed points on the moved complement. Its kernel on the same
ordinary component is normalized by this residual and disjoint from the
pure line. The fixed-subgroup bound makes that kernel have order at most
two. An order-two normalized subgroup is centralized, so the fixed-point
calculation eliminates it.

NonFFSourceDoubledBinaryPureFaithful applies these statements to the actual
offender, pure line and minimal H1 component. H centralizes only the line;
no paired-plane centralization or identification of the two moved groups
is used. Source: Aschbacher–Smith 7.7.3, printed pp.705–706, and
E.6.11–12, printed pp.249–250, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFaithful
open ChapterE BinaryLinearThree NaturalDual DoubledBinaryPlanes DoubledBinaryLocalCore
open DoubledBinaryIntersection DoubledBinaryOddCore DoubledBinaryInnerAction
open DoubledBinaryComponentGeometry DoubledBinaryPureFixed DoubledBinaryPlaneQuotient
variable {G : Type*} [_root_.Group G] [Finite G]

/-- The H1 fixed subgroup has order at most four. The actual E.6.11
moving-element theorem discharges the centralizer obstruction. -/
theorem component_fixed_card_le_four
    (W₀ Z M K : Subgroup G) [IsElementaryAbelian 2 W₀] (T : Sylow 2 G)
    (h61 : Section06.HypothesisE61 KnownSimple.IsKnownSimple T M W₀)
    (hr : 1 < globalR W₀)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))
    (hMN : M ≤ normalizer (W₀ : Set G)) (hZW : Z ≤ W₀)
    (hZK : Z ≤ centralizer (K : Set G)) (hZ : Z ≠ ⊥)
    (hp : (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).2 = 0) ∨
      (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).1 = 0))
    (hs : ∀ w : Additive W₀, (w.toMul : G) ∈ centralizer (K : Set G) → ¬ IsSingular (E w))
    (hKM : ¬ K ≤ M) : Nat.card (W₀ ⊓ centralizer (K : Set G) : Subgroup G) ≤ 4 := by
  by_contra! hc
  let X := W₀ ⊓ centralizer (K : Set G)
  have hZX : Z ≤ X := le_inf hZW hZK
  have hX : X ≠ ⊥ := fun he => hZ (le_bot_iff.mp (he ▸ hZX))
  have hcent := large_pure_singularFree_centralizer W₀ X Z M E a hcov hMN
    inf_le_left hZX hZ hp (fun w hw => hs w hw.2) hc
  have hesc : ¬ centralizer (X : Set G) ≤ M := by
    intro hh
    exact hKM ((le_centralizer_iff.mp (show X ≤ centralizer (K : Set G) from inf_le_right)).trans hh)
  obtain ⟨_,_,_,_,_,he⟩ := h61.hyperplane_escape_of_maximal_action
    (fun U hU hmax hn => Section06.maximal_escape_action_knownSimple h61 hU hmax hn)
    hX (show X ≤ W₀ from inf_le_left) hcent hesc
  rw [he] at hr
  exact (lt_irrefl (1 : ℕ∞)) hr

/-- The fixed subgroup of the literal plane residual is contained in the
original paired plane, by lifting its fixed-point-free cubic on the complement. -/
theorem pairedPlane_residual_fixed_le
    (W₀ L : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G))
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1) :
    W₀ ⊓ centralizer (localResidual L (ambientPlane W₀ E v f) : Set G) ≤
      ambientPlane W₀ E v f := by
  let U := ambientPlane W₀ E v f
  let C := L ⊓ centralizer (U : Set G)
  let R := localResidual L U
  let qC : C →* pairFixer v f := (q.comp (inclusion inf_le_left)).codRestrict _
    (fun c => (component_plane_fixer W₀ L hLN q E hE v f ⟨c,c.property.1⟩).mp c.property.2)
  have hqC : Function.Surjective qC := by
    intro g
    obtain ⟨l,hl⟩ := hq g
    refine ⟨⟨l,l.property,?_⟩,Subtype.ext hl⟩
    exact (component_plane_fixer W₀ L hLN q E hE v f l).mpr (hl.symm ▸ g.property)
  obtain ⟨g,hg,hgv,hgf,hfix⟩ := pairedPlane_cubic v f hfv
  let a : pairFixer v f := ⟨g,hgv,hgf⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext hg
  have haR : a ∈ pResidual 2 (pairFixer v f) := mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one ha3))
  rw [← map_pResidual_of_surjective 2 qC hqC] at haR
  obtain ⟨r,hr,he⟩ := haR
  let l : L := ⟨r,r.property.1⟩
  have hl : q l = g := congrArg Subtype.val he
  have hrR : (l : G) ∈ R := mem_map_of_mem C.subtype hr
  intro x hx
  let w : Additive W₀ := Additive.ofMul ⟨x,hx.1⟩
  have hw : automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w = w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * x * (l : G)⁻¹ = x
    rw [hx.2 l hrR,mul_inv_cancel_right]
  have hh := hE l w
  rw [hw,hl] at hh
  exact ⟨w.toMul,hfix _ hh.symm,rfl⟩

/-- The small H1 fixed subgroup makes the rank-four plane actor faithful.
The plane residual normalizes the same ordinary component and has no fixed
points on its moved subgroup. -/
theorem pairedPlane_component_faithful
    (W₀ L Z H K : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G))
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (hZU : Z ≤ ambientPlane W₀ E v f) (hZ : Nat.card Z = 2)
    (hZK : Z ≤ centralizer (K : Set G))
    (hRH : localResidual L Z ≤ H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : IsComponentIn K H)
    (hsmall : Nat.card (W₀ ⊓ centralizer (K : Set G) : Subgroup G) ≤ 4) :
    ⁅W₀,localResidual L (ambientPlane W₀ E v f)⁆ ⊓ centralizer (K : Set G) = ⊥ := by
  let U := ambientPlane W₀ E v f
  let R := localResidual L U
  let A := ⁅W₀,R⁆
  let X := A ⊓ centralizer (K : Set G)
  have hRW : R ≤ normalizer (W₀ : Set G) := (map_subtype_le _).trans (inf_le_left.trans hLN)
  have hAW : A ≤ W₀ := le_normalizer_iff_commutator_le_left.mp hRW
  have hZW : Z ≤ W₀ := hZU.trans (ambientPlane_le_orbit W₀ E v f)
  have hdis := pairedPlane_residual_disjoint W₀ L hLN q E hE v f hfv
  have hd : Disjoint Z X := hdis.mono hZU inf_le_left
  have hnorm : X ≤ normalizer (Z : Set G) := (inf_le_left.trans hAW).trans
    (((le_centralizer W₀).trans (centralizer_le hZW)).trans (Subgroup.centralizer_le_normalizer _))
  have hcount := card_sup_eq_mul_of_normalizes_of_disjoint Z X hnorm hd
  rw [hZ] at hcount
  have hle : Z ⊔ X ≤ W₀ ⊓ centralizer (K : Set G) :=
    sup_le (le_inf hZW hZK) (le_inf (inf_le_left.trans hAW) inf_le_right)
  have hc := (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)).trans hsmall
  rw [hcount] at hc
  by_cases hbot : X = ⊥
  · exact hbot
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hXone : Nat.card X ≠ 1 := fun hh => hbot (card_eq_one.mp hh)
  have hXtwo : Nat.card X = 2 := by omega
  have hRZ : R ≤ localResidual L Z :=
    embedded_pResidual_mono 2 (inf_le_inf_left L (centralizer_le hZU))
  have hRNK := residual_normalizes_component H R K hH.stronglyQuasithin hK
    (hRZ.trans hRH) (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G)))
  have hRNX : R ≤ normalizer (X : Set G) :=
    (le_inf (normalizer_commutator_ge_right W₀ R)
      (hRNK.trans (normalizer_le_normalizer_centralizer K))).trans inf_normalizer_le_normalizer_inf
  have hXR : X ≤ centralizer (R : Set G) :=
    le_centralizer_iff.mp (hRNX.trans (normalizer_le_centralizer_of_card_two X hXtwo))
  have hXU : X ≤ U := (le_inf (inf_le_left.trans hAW) hXR).trans
    (pairedPlane_residual_fixed_le W₀ L hLN q hq E hE v f hfv)
  exact le_bot_iff.mp ((le_inf hXU (show X ≤ A from inf_le_left)).trans hdis.eq_bot.le)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFaithful
