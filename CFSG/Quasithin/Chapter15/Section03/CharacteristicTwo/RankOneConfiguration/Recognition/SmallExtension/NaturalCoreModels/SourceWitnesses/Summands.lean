module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Generation
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Actual natural summands in the abelian small core

Whole-core coordinates embed one or two natural copies into the ambient group.
Transitivity on nonzero columns proves their irreducibility for actual
conjugation. The parabolic cubic moves each copy; its commutators belong to
the source residual because the core normalizes that residual. Thus each copy
meets Y₊ nontrivially, which is sufficient for conjugate generation of Q.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.NaturalCoreModels.SourceWitnesses
open CentralCover CentralCover.LinearModels LinearThree

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {L : Subgroup G} {ρ : Representation (ZMod 2) SL V}

private def copyMap (m : FullCenter L ρ) (f : Space →ₗ[ZMod 2] V) :
    Multiplicative Space →* G :=
  (coreCenter L).subtype.comp
    (m.equiv.symm.toMonoidHom.comp f.toAddMonoidHom.toMultiplicative)

private theorem copyMap_injective (m : FullCenter L ρ) (f : Space →ₗ[ZMod 2] V)
    (hf : Function.Injective f) : Function.Injective (copyMap m f) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply hf
  have hh := congrArg (fun z : coreCenter L => (m.equiv z).toAdd)
    (show m.equiv.symm (Multiplicative.ofAdd (f x.toAdd)) =
      m.equiv.symm (Multiplicative.ofAdd (f y.toAdd)) from Subtype.ext h)
  simpa using hh

private theorem copyMap_conjugate (m : FullCenter L ρ) (f : Space →ₗ[ZMod 2] V)
    (he : ∀ a v, f (natural a v) = ρ a (f v)) (l : L) (v : Space) :
    (l : G) * copyMap m f (Multiplicative.ofAdd v) * (l : G)⁻¹ =
      copyMap m f (Multiplicative.ofAdd (natural (m.actor l) v)) := by
  have hh : centerConjugate L l (m.equiv.symm (Multiplicative.ofAdd (f v))) =
      m.equiv.symm (Multiplicative.ofAdd (f (natural (m.actor l) v))) := by
    apply m.equiv.injective
    rw [m.action]
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, he]
    rfl
  exact congrArg Subtype.val hh

private theorem copyMap_normalized (m : FullCenter L ρ) (f : Space →ₗ[ZMod 2] V)
    (he : ∀ a v, f (natural a v) = ρ a (f v)) :
    L ≤ normalizer ((copyMap m f).range : Set G) := by
  intro l hl
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Multiplicative.ofAdd (natural (m.actor ⟨l, hl⟩) v.toAdd),
      (copyMap_conjugate m f he ⟨l, hl⟩ v.toAdd).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨Multiplicative.ofAdd (natural (m.actor ⟨l⁻¹, L.inv_mem hl⟩) v.toAdd), ?_⟩
    rw [← copyMap_conjugate m f he ⟨l⁻¹, L.inv_mem hl⟩ v.toAdd,
      ofAdd_toAdd, hv]
    simp only [inv_inv]
    group

private theorem copyMap_irreducible (m : FullCenter L ρ)
    (f : Space →ₗ[ZMod 2] V)
    (he : ∀ a v, f (natural a v) = ρ a (f v))
    (N : Subgroup G) (hNW : N ≤ (copyMap m f).range)
    (hLN : L ≤ normalizer (N : Set G)) : N = ⊥ ∨ N = (copyMap m f).range := by
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  apply le_antisymm hNW
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
    by_contra! h
    exact hN (eq_bot_iff.mpr (fun x hx => mem_bot.mpr (h x hx)))
  obtain ⟨v, rfl⟩ := hNW hx
  have hv : v.toAdd ≠ 0 := by
    intro h
    have hv1 : v = 1 := congrArg Multiplicative.ofAdd h
    exact hx1 (by rw [hv1, map_one])
  rintro z ⟨w, rfl⟩
  by_cases hw : w.toAdd = 0
  · have hw1 : w = 1 := congrArg Multiplicative.ofAdd hw
    rw [hw1, map_one]
    exact N.one_mem
  obtain ⟨a, ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    v.toAdd w.toAdd hv hw
  obtain ⟨l, hl⟩ := m.actor_surjective a
  have hn := ((mem_normalizer_iff.mp (hLN l.property)) (copyMap m f v)).mp hx
  have hc := copyMap_conjugate m f he l v.toAdd
  simp only [ofAdd_toAdd] at hc
  rw [hc, hl] at hn
  change natural a v.toAdd = w.toAdd at ha
  simpa only [ha, ofAdd_toAdd] using hn

private theorem copyMap_meets [Finite G] {κ : GroupClass} {d : LocalData G}
    {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c)
    (m : FullCenter c.L ρ) (f : Space →ₗ[ZMod 2] V) (hf : Function.Injective f)
    (he : ∀ a v, f (natural a v) = ρ a (f v))
    (hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map m.actor) :
    (copyMap m f).range ⊓ d.Yplus ≠ ⊥ := by
  obtain ⟨l, hlY, hl⟩ := hr
  let v : Space := ![1, 0, 0]
  let q := copyMap m f (Multiplicative.ofAdd v)
  let w := ⁅(l : G), q⁆
  have hqW : q ∈ (copyMap m f).range := ⟨_, rfl⟩
  have hqQ : q ∈ extensionCore c.L :=
    (show q ∈ coreCenter c.L from (m.equiv.symm (Multiplicative.ofAdd (f v))).property).1
  have hwW : w ∈ (copyMap m f).range :=
    (le_normalizer_iff_commutator_le_right.mp (copyMap_normalized m f he))
      (commutator_mem_commutator l.property hqW)
  have hwY : w ∈ d.Yplus := by
    exact (le_normalizer_iff_commutator_le_left.mp
      (ContainedCoreModels.core_normalizes_yplus s))
      (commutator_mem_commutator hlY hqQ)
  have hw1 : w ≠ 1 := by
    intro hz
    have hconj : (l : G) * q * (l : G)⁻¹ = q :=
      mul_inv_eq_one.mp hz
    have hcoord := (copyMap_injective m f hf)
      ((copyMap_conjugate m f he l v).symm.trans hconj)
    have hvfix : natural planeRotation v = v := by
      simpa only [hl, toAdd_ofAdd] using congrArg Multiplicative.toAdd hcoord
    exact (by decide : natural planeRotation (![1, 0, 0] : Space) ≠ ![1, 0, 0]) hvfix
  intro hz
  exact hw1 (mem_bot.mp (hz ▸ (show w ∈ (copyMap m f).range ⊓ d.Yplus from ⟨hwW, hwY⟩)))

private theorem core_abelian (m : AbelianCore L ρ) :
    IsMulCommutative (extensionCore L) := by
  apply le_centralizer_iff_isMulCommutative.mp
  rw [← m.center_eq]
  exact inf_le_right.trans (centralizer_le inf_le_left)

/-- A whole natural core is generated by its actual intersection with Y₊. -/
theorem one_generation [Finite G] {κ : GroupClass} {d : LocalData G}
    {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c)
    (m : AbelianCore c.L natural)
    (hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map m.fullCenter.actor) :
    extensionCore c.L ≤ localSpan (extensionCore c.L ⊓ d.Yplus) c.L := by
  let f : Space →ₗ[ZMod 2] Space := LinearMap.id
  let W := (copyMap m.fullCenter f).range
  have hW : W = extensionCore c.L := by
    apply le_antisymm
    · rintro x ⟨v, rfl⟩
      exact (m.fullCenter.equiv.symm v).property.1
    · intro x hx
      let z : coreCenter c.L := ⟨x, m.center_eq.symm ▸ hx⟩
      exact ⟨m.fullCenter.equiv z, congrArg Subtype.val (m.fullCenter.equiv.symm_apply_apply z)⟩
  exact core_le_span_of_irreducible_cover d c (fun _ : Unit => W)
    (by rw [← hW]; exact le_iSup (fun _ : Unit => W) ())
    (fun _ => hW.le) (fun _ => copyMap_normalized m.fullCenter f (fun _ _ => rfl))
    (fun _ => copyMap_irreducible m.fullCenter f (fun _ _ => rfl))
    (fun _ => copyMap_meets s m.fullCenter f Function.injective_id (fun _ _ => rfl) hr)

/-- Both actual coordinate copies use one quotient actor and together generate Q. -/
theorem two_generation [Finite G] {κ : GroupClass} {d : LocalData G}
    {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c)
    (m : AbelianCore c.L (natural.prod natural))
    (hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map m.fullCenter.actor) :
    extensionCore c.L ≤ localSpan (extensionCore c.L ⊓ d.Yplus) c.L := by
  let f : Bool → Space →ₗ[ZMod 2] (Space × Space) := fun b =>
    if b then LinearMap.inr (ZMod 2) Space Space else LinearMap.inl (ZMod 2) Space Space
  have hf : ∀ b, Function.Injective (f b) := by
    intro b
    cases b
    · exact fun _ _ h => congrArg Prod.fst h
    · exact fun _ _ h => congrArg Prod.snd h
  have he : ∀ b a v, f b (natural a v) = (natural.prod natural) a (f b v) := by
    intro b a v
    cases b <;> simp [f]
  let W : Bool → Subgroup G := fun b => (copyMap m.fullCenter (f b)).range
  have hWQ : ∀ b, W b ≤ extensionCore c.L := by
    intro b x hx
    obtain ⟨v, rfl⟩ := hx
    exact (m.fullCenter.equiv.symm (Multiplicative.ofAdd (f b v.toAdd))).property.1
  have hcover : extensionCore c.L ≤ ⨆ b, W b := by
    intro x hx
    let z : coreCenter c.L := ⟨x, m.center_eq.symm ▸ hx⟩
    let v := (m.fullCenter.equiv z).toAdd
    have h₀ : copyMap m.fullCenter (f false) (Multiplicative.ofAdd v.1) ∈ ⨆ b, W b :=
      le_iSup W false ⟨_, rfl⟩
    have h₁ : copyMap m.fullCenter (f true) (Multiplicative.ofAdd v.2) ∈ ⨆ b, W b :=
      le_iSup W true ⟨_, rfl⟩
    have hh := (⨆ b, W b).mul_mem h₀ h₁
    have heq : copyMap m.fullCenter (f false) (Multiplicative.ofAdd v.1) *
        copyMap m.fullCenter (f true) (Multiplicative.ofAdd v.2) = x := by
      change ((m.fullCenter.equiv.symm (Multiplicative.ofAdd (v.1, 0)) : coreCenter c.L) : G) *
        ((m.fullCenter.equiv.symm (Multiplicative.ofAdd (0, v.2)) : coreCenter c.L) : G) = x
      rw [← Subgroup.coe_mul, ← map_mul]
      have hv : Multiplicative.ofAdd (v.1, 0) * Multiplicative.ofAdd (0, v.2) =
          m.fullCenter.equiv z := by
        apply Multiplicative.toAdd.injective
        change (v.1, 0) + (0, v.2) = v
        simp
      rw [hv, MulEquiv.symm_apply_apply]
    exact heq ▸ hh
  exact core_le_span_of_irreducible_cover d c W hcover hWQ
    (fun b => copyMap_normalized m.fullCenter (f b) (he b))
    (fun b => copyMap_irreducible m.fullCenter (f b) (he b))
    (fun b => copyMap_meets s m.fullCenter (f b) (hf b) (he b) hr)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.NaturalCoreModels.SourceWitnesses
