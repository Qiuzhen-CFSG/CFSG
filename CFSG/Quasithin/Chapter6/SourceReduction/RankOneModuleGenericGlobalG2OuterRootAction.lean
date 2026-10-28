module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2RootNormalization
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterCentralizer
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow

/-!
# The original torus normalizer's six-root action and centralizer bound

Conjugation by the original Sylow actor gives compatible automorphisms of
both source parabolics. Transport through the same amalgam isomorphism
preserves the actual split torus, using its whole-overlap marking. The model
root-normalization calculation then constructs all six additive root actions.
No automorphism of the full G₂ model or independent root action is assumed.

For the actual outer involution this discharges the previous root-action
premise: |C_S(t)| ≤ q³ and |C_T(t)| < q⁴. The existential application keeps
the original marked Hall torus and the order-two field action on the literal
right quotient. The Chapter 12 companion supplies the chosen-module consumers.
Ambient Sylow placement in C_G(t), hence the even-degree conclusion S=T,
remains a separate source obligation, as do exhaustive comparison, original
uniqueness and completion recognition.

Source: Aschbacher–Smith F.4.37–38, printed pp.293–294, and 5.3.3, p.659
(`refs/quasithin.pdf`). The internal import reuses the checked inverse-Sylow
map in this proof family without changing its public boundary.
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem source_parabolics_normalized
    {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (i : Fin 2) :
    (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i : Set G) := by
  have hS := sylow_normalizes_sourceS hTL hTH
  have hK (j : Fin 2) : (T : Subgroup G) ≤ normalizer (![L,residual H] j : Set G) := by
    fin_cases j
    · exact hTL
    · exact hTH.trans (le_normalizer_residual H)
  have hB (j : Fin 2) : (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.borel (![L,residual H] j) (sourceS L H) : Set G) := by
    have hi := (le_inf hS (hK j)).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hK j) (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_inf (hK i) hS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (hB (ChapterF.Source.other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
private theorem torus_action_map
    {M : Type*} [Group M] [Finite M] (P : Subgroup G) (Q E : Subgroup M)
    (e : P ≃* Q) (D : Subgroup G) (t : G)
    (htP : t ∈ normalizer (P : Set G)) (htD : t ∈ normalizer (D : Set G))
    (hmark : ∀ x : P, x.val∈D ↔ (e x).val∈E) :
    (E.subgroupOf Q).map
      (MulAut.congr e (P.normalizerMonoidHom ⟨t,htP⟩)).toMonoidHom = E.subgroupOf Q := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    have hd : (e.symm x).val ∈ D := (hmark _).mpr (by simpa only [e.apply_symm_apply] using (show x.val∈E from hx))
    have htd := (mem_normalizer_iff.mp htD _).mp hd
    exact (hmark (P.normalizerMonoidHom ⟨t,htP⟩ (e.symm x))).mp htd
  · rw [card_map_of_injective (MulAut.congr e (P.normalizerMonoidHom ⟨t,htP⟩)).injective]

/-- The actual torus normalizer acts separately on all six roots through the
same compatible parabolic comparison. No full-model automorphism is assumed. -/
theorem Preparation.g2_torus_normalizer_root_action
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (htD : t.val ∈ normalizer (D : Set G)) :
    ∃ ρ : Fin 6 → F ≃+ F, ∀ v : Fin 6 → F,
      t.val * (e.right.symm ⟨unipotentProduct v,
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem v))⟩).val * t.val⁻¹ =
      (e.right.symm ⟨unipotentProduct (fun i => ρ i (v i)),
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩).val := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  have hC := (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)).ge
  have htor : splitTorus (K := F) ≤ parabolic₁ ⊓ parabolic₂ :=
    le_inf (le_sup_right.trans borel_le_parabolic₁) (le_sup_right.trans borel_le_parabolic₂)
  have hmr (x : P) : x.val∈D ↔ (e.right x).val∈splitTorus := by
    constructor
    · intro hx
      let y : (Q ⊓ P : Subgroup G) := ⟨x.val,hC (hD hx)⟩
      have he := congrArg Subtype.val (e.right_commutes y)
      change (e.right x).val=(e.middle y).val at he
      rw [he]
      exact (hmark y).mp hx
    · intro hx
      let y : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨(e.right x).val,htor hx⟩
      have he := congrArg Subtype.val (e.symm.right_commutes y)
      change (e.right.symm (e.right x)).val = (e.middle.symm y).val at he
      rw [e.right.symm_apply_apply] at he
      rw [he]
      exact (hmark _).mpr (by simpa only [e.middle.apply_symm_apply] using hx)
  have hml (x : Q) : x.val∈D ↔ (e.left x).val∈splitTorus := by
    constructor
    · intro hx
      let y : (Q ⊓ P : Subgroup G) := ⟨x.val,hC (hD hx)⟩
      have he := congrArg Subtype.val (e.left_commutes y)
      change (e.left x).val=(e.middle y).val at he
      rw [he]
      exact (hmark y).mp hx
    · intro hx
      let y : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨(e.left x).val,htor hx⟩
      have he := congrArg Subtype.val (e.symm.left_commutes y)
      change (e.left.symm (e.left x)).val = (e.middle.symm y).val at he
      rw [e.left.symm_apply_apply] at he
      rw [he]
      exact (hmark _).mpr (by simpa only [e.middle.apply_symm_apply] using hx)
  have htP := source_parabolics_normalized h.sylow_normalizes hTH 1 t.property
  have htQ := source_parabolics_normalized h.sylow_normalizes hTH 0 t.property
  let b := MulAut.congr e.right (P.normalizerMonoidHom ⟨t.val,htP⟩)
  let c := MulAut.congr e.left (Q.normalizerMonoidHom ⟨t.val,htQ⟩)
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  have hUS := source_g2_inverse_sylow_image d h hTH e
  have hUP : unipotent (K := F) ≤ parabolic₁ := le_sup_left.trans borel_le_parabolic₁
  let eU : unipotent (K := F) ≃* sourceS L H :=
    ((subgroupOfEquivOfLe hUP).symm.trans
      (equivMapOfInjective (unipotent.subgroupOf parabolic₁) f hf)).trans
        (MulEquiv.subgroupCongr hUS)
  let τ : normalizer (sourceS L H : Set G) :=
    ⟨t.val,sylow_normalizes_sourceS h.sylow_normalizes hTH t.property⟩
  let cS := (sourceS L H).normalizerMonoidHom τ
  let a : MulAut (unipotent (K := F)) := MulAut.congr eU.symm cS
  have he (x : unipotent (K := F)) : eU (a x)=cS (eU x) := eU.apply_symm_apply _
  have hb (x : unipotent (K := F)) :
      (b ⟨x.val,hUP x.property⟩).val = (a x).val := by
    suffices b ⟨x.val,hUP x.property⟩ = ⟨(a x).val,hUP (a x).property⟩ from congrArg Subtype.val this
    apply e.right.symm.injective
    change e.right.symm (e.right _) = _
    rw [e.right.symm_apply_apply]
    apply Subtype.ext
    change t.val*(e.right.symm ⟨x.val,hUP x.property⟩).val*t.val⁻¹ =
      (e.right.symm ⟨(a x).val,hUP (a x).property⟩).val
    exact (congrArg Subtype.val (he x)).symm
  have hagree (x : unipotent (K := F)) :
      (e.right.symm ⟨x.val,hUP x.property⟩).val =
      (e.left.symm ⟨x.val,borel_le_parabolic₂ (mem_sup_left x.property)⟩).val := by
    let z : ChapterF.GreenBook.LieModels.G2.overlap (F := F) :=
      ⟨x.val,hUP x.property,borel_le_parabolic₂ (mem_sup_left x.property)⟩
    exact (congrArg Subtype.val (e.symm.right_commutes z)).trans
      (congrArg Subtype.val (e.symm.left_commutes z)).symm
  have hc (x : unipotent (K := F)) :
      (c ⟨x.val,borel_le_parabolic₂ (mem_sup_left x.property)⟩).val = (a x).val := by
    suffices c ⟨x.val,borel_le_parabolic₂ (mem_sup_left x.property)⟩ =
        ⟨(a x).val,borel_le_parabolic₂ (mem_sup_left (a x).property)⟩ from congrArg Subtype.val this
    apply e.left.symm.injective
    change e.left.symm (e.left _) = _
    rw [e.left.symm_apply_apply]
    apply Subtype.ext
    change t.val*(e.left.symm ⟨x.val,_⟩).val*t.val⁻¹ = (e.left.symm ⟨(a x).val,_⟩).val
    rw [←hagree,←hagree]
    exact (congrArg Subtype.val (he x)).symm
  have hbD := torus_action_map P parabolic₁ splitTorus e.right D t.val htP htD hmr
  have hcD := torus_action_map Q parabolic₂ splitTorus e.left D t.val htQ htD hml
  have hq : 2 < Nat.card F := by
    rw [(d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  obtain ⟨ρ,hρ⟩ := G2OuterRootNormalization.root_actions hq a b c hb hc hbD hcD
  refine ⟨ρ,?_⟩
  intro v
  have hact : a (unipotentEquiv v)=unipotentEquiv (fun i => ρ i (v i)) := Subtype.ext (hρ v)
  have hh := congrArg Subtype.val (he (unipotentEquiv v))
  rw [hact] at hh
  exact hh.symm

/-- The marked outer involution has fewer than q⁴ centralizing elements in T.
The original parabolic actions discharge the earlier root-action premise. -/
theorem Preparation.g2_outer_involution_centralizer_lt
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2) (htS : t.val ∉ sourceS L H)
    (htD : t.val ∈ normalizer (D : Set G)) :
    Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ Nat.card F^3 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < Nat.card F^4 := by
  obtain ⟨ρ,hρ⟩ := d.g2_torus_normalizer_root_action h hH.1.1.2 hp F e hD hmark t htD
  exact d.g2_outer_involution_centralizer_lt_of_root_action h hH hp F e hD hmark t ht2 htS htD ρ hρ

/-- If S is proper in T, the same marked torus supplies an actual outer
involution with its order-two quotient field action and strict centralizer
bound. This is not yet a Sylow assertion for the ambient centralizer. -/
theorem Preparation.g2_exists_outer_involution_small_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hne : sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus) ∧
      ∃ eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F,
      ∃ t : T, orderOf t=2 ∧ t.val ∉ sourceS L H ∧
        t.val ∈ normalizer (D : Set G) ∧ orderOf (residualSylowFieldAction hH.1.1.2 eR t)=2 ∧
        Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ Nat.card F^3 ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < Nat.card F^4 := by
  obtain ⟨D,hD,hHall,hmark,eR,t,ht,htS,htD,hσ⟩ :=
    d.g2_exists_outer_involution h hH.1.1.2 hp F e hne
  exact ⟨D,hD,hHall,hmark,eR,t,ht,htS,htD,hσ,
    d.g2_outer_involution_centralizer_lt h hH hp F e hD hmark t ht htS htD⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
