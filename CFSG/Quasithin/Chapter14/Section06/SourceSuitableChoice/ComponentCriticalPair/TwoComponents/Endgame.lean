module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.PlacedSelection
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Symmetry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.PureCentralizer
public import Theory.Representation.PSL3Two.NaturalDualEmbeddedSections
public import Theory.Representation.PSL3Two.InnerCoordinates
public import Theory.Representation.PSL3Two.PairedNaturalDual.ComponentAction
public import Theory.Representation.BinaryConjugationSection.Relabel
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# The two-component Sylow contradiction from the paired marking

Proper alignment makes both components normal. The literal inner-action
preimage therefore has index at most two in Mc. Pulling the two three-spaces
back under the original U/Z coordinates supplies the natural and dual
sections, with a surjective SL₃(2) actor. The rank-two actor and index-two
denominator place the opposite point in one of these supports; their point
centralizers contradict the already proved common-centralizer Sylow bound.

Only the genuine earlier component and simultaneous support markings remain
inputs. Their construction belongs to qt-e-suitable-component-marking using
qt-e-suitable-component-supports; final suitable choice belongs to
qt-e-suitable-existence. Source: Aschbacher--Smith 14.6.24(3), p.1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The placed endpoint is impossible under the actual paired component
marking. Natural sections, their actor and index are constructed here. -/
theorem source_placedEndpoint_false_of_paired_supports
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (K Kplus : Subgroup G)
    (p : PlacedEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) K Kplus)
    (hKM : K ≤ Mc) (hKplusM : Kplus ≤ Mc)
    (hcomp : (K.subgroupOf Mc).IsCComponent)
    (hcompPlus : (Kplus.subgroupOf Mc).IsCComponent)
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (N : Subgroup (Source.Hstar Mc)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : Source.Hstar Mc,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (κ₁ κ₂ : BinaryLinearThree.Group →* N)
    (hκrange₁ : (N.subtype.comp κ₁).range = Source.starImage Mc K)
    (hκrange₂ : (N.subtype.comp κ₂).range = Source.starImage Mc Kplus)
    (hl₁ : ∀ k, m.left (κ₁ k) = MulAut.conj k)
    (hr₁ : ∀ k, m.right (κ₁ k) = 1)
    (hl₂ : ∀ k, m.left (κ₂ k) = 1)
    (hr₂ : ∀ k, m.right (κ₂ k) = MulAut.conj k)
    (hpair : ∀ J : Subgroup Mc, J.IsCComponent →
      J = K.subgroupOf Mc ∨ J = Kplus.subgroupOf Mc)
    (hZ₁ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hZ₂ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆)
    (hS₁ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ = m.rightEmbedding.range)
    (hK : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.leftEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.rightEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (a : N) (ha : m.left a ∉ MulAut.innerSubgroup BinaryLinearThree.Group)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eKplus : (Kplus ⧸ pCore 2 Kplus) ≃* BinaryLinearThree.Group) : False := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  let h : D.Hypothesis := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  let U := D.UH
  let Ug := p.endpoint.conjugate U
  let q := QuotientGroup.mk' (pCore 2 Mc)
  have hp := source_placedEndpoint_proper_alignment
    hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
    hcross c N m hN hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
    hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha
  have hs := source_placedEndpoint_strict_comparison
    hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
    hcross c N m hN hspan hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
    hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha eK eKplus
  have hNt : N = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Mc) x
    rw [hN]
    constructor
    · have hy := (normal_subgroupOf_iff_le_normalizer hKM).mp hp.2.2.1 y.property
      change y ∈ (normalizer (K : Set G)).subgroupOf Mc at hy
      rwa [hK] at hy
    · have hy := (normal_subgroupOf_iff_le_normalizer hKplusM).mp hp.2.2.2.1 y.property
      change y ∈ (normalizer (Kplus : Set G)).subgroupOf Mc at hy
      rwa [hKplus] at hy
  let β : Mc →* N := q.codRestrict N (fun x => hNt ▸ mem_top (q x))
  have hβ : Function.Surjective β := by
    intro x
    obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (pCore 2 Mc) x.val
    exact ⟨y,Subtype.ext hy⟩
  let α := m.left.comp β
  let A := innerPreimage Mc α
  let f := innerActor Mc α
  have hAH : A ≤ Mc := innerPreimage_le Mc α
  have hUA : U ≤ A := by
    intro u hu
    have huH := h.UH_le_H hu
    apply (mem_innerPreimage Mc α ⟨u,huH⟩).mpr
    have hqu : q ⟨u,huH⟩ = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      have hQ : (Mc.pCoreIn 2).subgroupOf Mc = pCore 2 Mc :=
        comap_map_eq_self_of_injective Mc.subtype_injective _
      rw [←hQ]
      exact h.UH_le_QH hu
    have hb : β ⟨u,huH⟩ = 1 := Subtype.ext hqu
    change m.left (β ⟨u,huH⟩) ∈ MulAut.innerSubgroup BinaryLinearThree.Group
    rw [hb,map_one]
    exact one_mem _
  have hf : Function.Surjective f := by
    apply innerActor_surjective Mc α
    rintro _ ⟨g,rfl⟩
    obtain ⟨x,hx⟩ := hβ (κ₁ g)
    exact ⟨x,by change m.left (β x) = _; rw [hx,hl₁]⟩
  have hemb (x : Mc) (v : Space) :
      (ρ.comp q) x (m.leftEmbedding v) = m.leftEmbedding (autAction (α x) v) :=
    m.left_intertwines (β x) v
  obtain ⟨Wn,Wd,hWn,hWd,⟨cn⟩,⟨cd⟩,_,_⟩ := exists_natural_dual_sections
    c α m.leftEmbedding m.left_injective hemb hAH hUA f (conj_innerActor Mc α)
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  let r := quadraticEndpointOfComparison h p.endpoint hb rfl c p.comparison
  have hfaith := f9_section_faithful D h (criticalSection h c)
  have hAN : Source.starImage Mc Ug ≤ N := by rw [hNt]; exact le_top
  have hk₂ : Function.Injective (N.subtype.comp κ₂) :=
    N.subtype_injective.comp (m.right_component_injective κ₂ hr₂)
  have hc₂ (n : N) (k : BinaryLinearThree.Group) :
      (N.subtype.comp κ₂) (m.right n k) =
        (n : Source.Hstar Mc) * (N.subtype.comp κ₂) k * (n : Source.Hstar Mc)⁻¹ :=
    congrArg N.subtype (m.right_component_covariance (hfaith.comp N.subtype_injective) κ₂ hl₂ hr₂ n k)
  have hr := source_actor_rank_and_inner_of_point_support
    hG T hempty hM hunique hmany hcard e hab c r N m hAN K Kplus
    p.normalizes_right p.point_support hKplusM hcompPlus hcross
    (N.subtype.comp κ₂) hk₂ hκrange₂ hc₂
  have hUgH : Ug ≤ Mc := p.endpoint.large_le hb
  have hUgA : Ug ≤ A := by
    intro x hx
    apply (mem_innerPreimage Mc α ⟨x,hUgH hx⟩).mpr
    apply hr.2.2
    exact mem_map_of_mem m.left (show β ⟨x,hUgH hx⟩ ∈
      (Source.starImage Mc Ug).subgroupOf N from mem_map_of_mem q hx)
  have hmap : (Ug.subgroupOf Mc).map α =
      ((Source.starImage Mc Ug).subgroupOf N).map m.left := by
    change (Ug.subgroupOf Mc).map (m.left.comp β) = _
    rw [←map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact mem_map_of_mem q hy
    · intro hx
      obtain ⟨y,hy,he⟩ := hx
      exact ⟨y,hy,Subtype.ext he⟩
  have hrank : rank ((Ug.subgroupOf A).map f) = 2 := by
    calc
      _ = rank ((Ug.subgroupOf Mc).map α) := innerActor_image_rank Mc α Ug hUgA
      _ = rank (((Source.starImage Mc Ug).subgroupOf N).map m.left) := congrArg rank hmap
      _ = rank (Source.starImage Mc Ug) := hr.1.symm
      _ = 2 := p.actor_rank_eq_two_of_strict_comparison hs
  let π := (BinaryLinear.OuterCyclic.slEquivLinear 3).toMonoidHom.comp f
  have hnrep : BinaryLinearThree.W.comp f =
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π := by
    apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro v
    rfl
  have hdrep : BinaryLinearThree.W.dual.comp f =
      Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π) := by
    apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro v
    change φ (BinaryLinearThree.W ((f x)⁻¹) v) = φ (BinaryLinearThree.W (f x⁻¹) v)
    rw [map_inv f x]
  have hπrank : 2 ≤ rank ((Ug.subgroupOf A).map π) := by
    change 2 ≤ rank ((Ug.subgroupOf A).map
      ((BinaryLinear.OuterCyclic.slEquivLinear 3).toMonoidHom.comp f))
    rw [←map_map,rank_map_injective _ (BinaryLinear.OuterCyclic.slEquivLinear 3).injective,hrank]
  have hplace := source_point_in_natural_or_dual_of_strict_comparison
    hG T hempty hM hunique hmany hcard e hab K Kplus p A Wn Wd π
    (hnrep ▸ cn) (hdrep ▸ cd) hUgA hWn hWd hs hπrank
  have impossible (V : Subgroup G) (f' : A →* BinaryLinearThree.Group)
      (hf' : Function.Surjective f')
      (cv : BinaryConjugationSection A V (centralInvolutions T) (BinaryLinearThree.W.comp f')) :
      ¬ p.endpoint.conjugate (centralInvolutions T) ≤ V :=
    source_placedEndpoint_point_not_le_natural_support
      hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
      hcross c N m hN hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
      hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha eK eKplus A V hAH
      (innerPreimage_relIndex_dvd_two Mc α) f' hf' cv
  rcases hplace with hn | hd
  · exact impossible Wn f hf cn hn
  · let fd := BinaryLinearThree.AutomorphismAction.graph.toMonoidHom.comp f
    have hfd : Function.Surjective fd := BinaryLinearThree.AutomorphismAction.graph.surjective.comp hf
    let cdual := cd.relabel f BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm
    exact impossible Wd fd hfd cdual hd
/-- Both terminal component-pair alternatives are excluded from the simultaneous
source markings, with endpoint selection and every local section discharged. -/
theorem source_no_paired_components
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (K Kplus : Subgroup G)
    (hKM : K ≤ Mc) (hKplusM : Kplus ≤ Mc)
    (hcomp : (K.subgroupOf Mc).IsCComponent)
    (hcompPlus : (Kplus.subgroupOf Mc).IsCComponent)
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    (hcrossRev : ⁅⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆,K⁆ = ⊥)
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (N : Subgroup (Source.Hstar Mc)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : Source.Hstar Mc,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (κ₁ κ₂ : BinaryLinearThree.Group →* N)
    (hκrange₁ : (N.subtype.comp κ₁).range = Source.starImage Mc K)
    (hκrange₂ : (N.subtype.comp κ₂).range = Source.starImage Mc Kplus)
    (hl₁ : ∀ k, m.left (κ₁ k) = MulAut.conj k)
    (hr₁ : ∀ k, m.right (κ₁ k) = 1)
    (hl₂ : ∀ k, m.left (κ₂ k) = 1)
    (hr₂ : ∀ k, m.right (κ₂ k) = MulAut.conj k)
    (hpair : ∀ J : Subgroup Mc, J.IsCComponent →
      J = K.subgroupOf Mc ∨ J = Kplus.subgroupOf Mc)
    (hZ₁ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hZ₂ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆)
    (hS₁ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ = m.rightEmbedding.range)
    (hK : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.leftEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.rightEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (a b : N) (ha : m.left a ∉ MulAut.innerSubgroup BinaryLinearThree.Group)
    (hb : m.right b ∉ MulAut.innerSubgroup BinaryLinearThree.Group)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eKplus : (Kplus ⧸ pCore 2 Kplus) ≃* BinaryLinearThree.Group) : False := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  have hfaith := f9_section_faithful _ h (criticalSection h c)
  let m' : Paired.Marking (ρ.comp N.subtype) := {
    left := m.right
    right := m.left
    leftEmbedding := m.rightEmbedding
    rightEmbedding := m.leftEmbedding
    left_injective := m.right_injective
    right_injective := m.left_injective
    disjoint := m.disjoint.symm
    span := by rw [sup_comm m.rightEmbedding.range m.leftEmbedding.range]; exact m.span
    left_intertwines := m.right_intertwines
    right_intertwines := m.left_intertwines }
  have hi₁ : Function.Injective (N.subtype.comp κ₁) :=
    N.subtype_injective.comp (m'.right_component_injective κ₁ hl₁)
  have hi₂ : Function.Injective (N.subtype.comp κ₂) :=
    N.subtype_injective.comp (m.right_component_injective κ₂ hr₂)
  have he₁ (n : N) (k : BinaryLinearThree.Group) :
      (N.subtype.comp κ₁) (m.left n k) =
        (n : Source.Hstar Mc) * (N.subtype.comp κ₁) k * (n : Source.Hstar Mc)⁻¹ :=
    congrArg N.subtype (m'.right_component_covariance
      (hfaith.comp N.subtype_injective) κ₁ hr₁ hl₁ n k)
  have he₂ (n : N) (k : BinaryLinearThree.Group) :
      (N.subtype.comp κ₂) (m.right n k) =
        (n : Source.Hstar Mc) * (N.subtype.comp κ₂) k * (n : Source.Hstar Mc)⁻¹ :=
    congrArg N.subtype (m.right_component_covariance
      (hfaith.comp N.subtype_injective) κ₂ hl₂ hr₂ n k)
  have hp := source_placedEndpoint_of_paired_supports
    hG T hempty hM hunique hmany hcard e hab c N m hN hspan hperm
    K Kplus hKM hKplusM hcomp hcompPlus hK hKplus hZ₁ hZ₂ hS₁ hS₂ hcross hcrossRev
    (N.subtype.comp κ₁) (N.subtype.comp κ₂) hi₁ hi₂ hκrange₁ hκrange₂ he₁ he₂
  change Nonempty (PlacedEndpoint h K Kplus) ∨ Nonempty (PlacedEndpoint h Kplus K) at hp
  rcases hp with hp | hp
  · obtain ⟨p⟩ := hp
    exact source_placedEndpoint_false_of_paired_supports
      hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
      hcross c N m hN hspan hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
      hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha eK eKplus
  · obtain ⟨p⟩ := hp
    have hN' : N = subspaceStabilizer ρ m'.leftEmbedding.range ⊓
        subspaceStabilizer ρ m'.rightEmbedding.range := by
      exact hN.trans (inf_comm _ _)
    have hspan' : m'.leftEmbedding.range ⊔ m'.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤ := by
      change m.rightEmbedding.range ⊔ m.leftEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤
      rw [sup_comm m.rightEmbedding.range m.leftEmbedding.range]
      exact hspan
    have hperm' (x : Source.Hstar Mc) :
        (m'.leftEmbedding.range.map (ρ x) = m'.leftEmbedding.range ∧
          m'.rightEmbedding.range.map (ρ x) = m'.rightEmbedding.range) ∨
        (m'.leftEmbedding.range.map (ρ x) = m'.rightEmbedding.range ∧
          m'.rightEmbedding.range.map (ρ x) = m'.leftEmbedding.range) :=
      (hperm x).imp And.symm And.symm
    exact source_placedEndpoint_false_of_paired_supports
      hG T hempty hM hunique hmany hcard e hab Kplus K p hKplusM hKM hcompPlus hcomp
      hcrossRev c N m' hN' hspan' hperm' κ₂ κ₁ hκrange₂ hκrange₁ hr₂ hl₂ hr₁ hl₁
      (fun J hJ => (hpair J hJ).symm) hZ₂ hZ₁ hS₂ hS₁ hKplus hK b hb eKplus eK
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
