module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticMaximal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizerAction
public import Theory.GroupTheory.Amalgam.AutomorphismTransport
public import Theory.SpecificGroups.SymplecticFour.SourceNormalizerExtension

/-!
# Faithful full-middle actions on the marked symplectic pair

The original full common normalizer D = N_G(L) ∩ N_G(O²(H)) normalizes
both pure source parabolics: it normalizes both local factors and their
common Sylow, hence their local Borels. Conjugation therefore acts on the
literal pure amalgam, including its whole overlap. Its kernel centralizes
the original factor join, whose ambient centralizer is already proved trivial.

Transport through the same three comparison maps gives a faithful native
marked-pair action in either orientation. On the entire pure common Borel
this is exactly the native inner action. Faithfulness gives the converse:
no other element of D induces a Borel-inner marked action.

The native restriction map is injective. If each value of the constructed
marked action belongs to its image, the unique lift is a faithful,
diagram-preserving native action with exactly the pure common Borel as
its inner preimage. This pointwise extendibility hypothesis remains open;
these conditional lifting lemmas do not construct the full-normalizer
extension or prove its ambient order bound. No recognition of the factor
join is used. Both orientations and the field-four case are retained.

Source: Aschbacher–Smith 5.3.1–2, printed pp.658–659, and Definition F.4.3,
p.274 of `refs/quasithin.pdf`. This supplies the marked action and exact
middle intersection for the remaining simultaneous native extension step.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G]

private theorem normalizes_source_parabolic
    {N S : Subgroup G} {J : Fin 2 → Subgroup G}
    (hNS : N ≤ normalizer (S : Set G))
    (hNJ : ∀ i, N ≤ normalizer (J i : Set G)) (i : Fin 2) :
    N ≤ normalizer (ChapterF.Source.parabolic J S i : Set G) := by
  have hb (j : Fin 2) : N ≤ normalizer (ChapterF.Source.borel (J j) S : Set G) := by
    have hi := (le_inf hNS (hNJ j)).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hNJ j) (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_inf (hNJ i) hNS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (hb (ChapterF.Source.other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

private def conjugationPair (P Q N : Subgroup G)
    (hP : N ≤ normalizer (P : Set G)) (hQ : N ≤ normalizer (Q : Set G)) :
    N →* RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right) where
  toFun g :=
    { left := P.normalizerMonoidHom (inclusion hP g)
      middle := (P ⊓ Q).normalizerMonoidHom
        (inclusion ((le_inf hP hQ).trans inf_normalizer_le_normalizer_inf) g)
      right := Q.normalizerMonoidHom (inclusion hQ g)
      left_commutes _ := Subtype.ext rfl
      right_commutes _ := Subtype.ext rfl }
  map_one' := by
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> simp
  map_mul' a b := by
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> simp [mul_assoc]

variable [Finite G]

/-- The full common normalizer acts faithfully on the exact pure source amalgam. -/
theorem Preparation.symplectic_source_middle_action
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    ∃ ρ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
      RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)),
      Function.Injective ρ ∧
      (∀ g x, ((ρ g).left x).val = g.val * x.val * g.val⁻¹) ∧
      (∀ g x, ((ρ g).middle x).val = g.val * x.val * g.val⁻¹) ∧
      (∀ g x, ((ρ g).right x).val = g.val * x.val * g.val⁻¹) := by
  let N := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  have hl := d.symplectic_normalizer_local_conditions h hH hp F hm hF he
  have hsL : sourceS L H ≤ L := (d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he) 0
  have hs : sourceS L H = (T : Subgroup G) ⊓ L :=
    (inf_eq_left.mpr hsL).symm.trans d.left_intersection
  have hNS : N ≤ normalizer (sourceS L H : Set G) := by
    rw [hs, hl.normalizer_eq_middle]
    exact le_rfl
  have hNP (i : Fin 2) : N ≤ normalizer (P i : Set G) := by
    apply normalizes_source_parabolic hNS
    intro j
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right
  let ρ := conjugationPair (P 0) (P 1) N (hNP 0) (hNP 1)
  refine ⟨ρ, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  apply ρ.ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  have heq : ρ g = 1 := hg
  have hcP : g.val ∈ centralizer (P 0 : Set G) ∧ g.val ∈ centralizer (P 1 : Set G) := by
    constructor
    · intro x hx
      have hh := congrArg (fun a => ((a.left ⟨x,hx⟩ : P 0) : G)) heq
      change g.val*x*g.val⁻¹=x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro x hx
      have hh := congrArg (fun a => ((a.right ⟨x,hx⟩ : P 1) : G)) heq
      change g.val*x*g.val⁻¹=x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hLP : L ≤ P 0 := le_sup_left.trans le_sup_left
  have hKP : residual H ≤ P 1 := le_sup_left.trans le_sup_left
  have hc : L ⊔ residual H ≤ centralizer ({g.val} : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hcP.1 x (hLP hx))
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hcP.2 x (hKP hx))
  have hgC : g.val ∈ centralizer ((L ⊔ residual H : Subgroup G) : Set G) := by
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (hc hx))
  rw [normalizer_pair_centralizer_eq_bot hl] at hgC
  exact Subtype.ext (mem_bot.mp hgC)

/-- A faithful whole-middle action transported through the same three comparison maps.
This is an action on the marked amalgam, not yet on a native completion. -/
structure SymplecticMarkedMiddleAction (L K S : Subgroup G)
    {U V Y : Type*} [Group U] [Group V] [Group Y] (β : RankTwoAmalgam U V Y) where
  comparison : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) β
  middle_le : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
    ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) ≤
      normalizer (L : Set G) ⊓ normalizer (K : Set G)
  action : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
    RankTwoAmalgam.Iso β β
  faithful : Function.Injective action
  left_conjugation : ∀ g x,
    (comparison.left.symm ((action g).left x)).val =
      g.val * (comparison.left.symm x).val * g.val⁻¹
  middle_conjugation : ∀ g x,
    (comparison.middle.symm ((action g).middle x)).val =
      g.val * (comparison.middle.symm x).val * g.val⁻¹
  right_conjugation : ∀ g x,
    (comparison.right.symm ((action g).right x)).val =
      g.val * (comparison.right.symm x).val * g.val⁻¹

omit [Finite G] in
private theorem transported_middle_action {L K S : Subgroup G}
    (hC : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) ≤
        normalizer (L : Set G) ⊓ normalizer (K : Set G))
    (ρ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
      RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (sourceParabolicAmalgam ![L,K] S))
    (hf : Function.Injective ρ)
    (hl : ∀ g x, ((ρ g).left x).val = g.val * x.val * g.val⁻¹)
    (hm : ∀ g x, ((ρ g).middle x).val = g.val * x.val * g.val⁻¹)
    (hr : ∀ g x, ((ρ g).right x).val = g.val * x.val * g.val⁻¹)
    {U V Y : Type*} [Group U] [Group V] [Group Y] {β : RankTwoAmalgam U V Y}
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) β) :
    Nonempty (SymplecticMarkedMiddleAction L K S β) := by
  let σ := (RankTwoAmalgam.automorphismConjEquiv e).toMonoidHom.comp ρ
  refine ⟨⟨e, hC, σ, (RankTwoAmalgam.automorphismConjEquiv e).injective.comp hf, ?_, ?_, ?_⟩⟩
  · intro g x
    change (e.left.symm (e.left ((ρ g).left (e.left.symm x)))).val = _
    rw [e.left.symm_apply_apply]
    exact hl g _
  · intro g x
    change (e.middle.symm (e.middle ((ρ g).middle (e.middle.symm x)))).val = _
    rw [e.middle.symm_apply_apply]
    exact hm g _
  · intro g x
    change (e.right.symm (e.right ((ρ g).right (e.right.symm x)))).val = _
    rw [e.right.symm_apply_apply]
    exact hr g _

/-- The original full common normalizer embeds in the automorphism group of
one of the two oriented native marked pairs. Every endpoint and middle action
is the transported original conjugation, and the exponent remains n. -/
theorem Preparation.symplectic_native_middle_action
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧
      (Nonempty (SymplecticMarkedMiddleAction L (residual H) (sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
       Nonempty (SymplecticMarkedMiddleAction L (residual H) (sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) := by
  refine ⟨(d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1, ?_⟩
  obtain ⟨ρ, hf, hl, hm', hr⟩ := d.symplectic_source_middle_action h hH hp F hm hF he
  have hf11 := d.hypothesisF11 h hH.1.1.2
  have hC : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G) ≤
        normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
    rw [ChapterF.Source.lemma_F_1_3_6 hf11]
    exact le_inf (hf11.commonBorel_normalizes_local 0) (hf11.commonBorel_normalizes_local 1)
  rcases he with he | he
  · obtain ⟨e⟩ := he
    exact Or.inl (transported_middle_action hC ρ hf hl hm' hr e)
  · obtain ⟨e⟩ := he
    exact Or.inr (transported_middle_action hC ρ hf hl hm' hr e)

namespace SymplecticMarkedMiddleAction
open Theory.SpecificGroups.SymplecticFour
variable {L K S : Subgroup G} {F : Type*} [Field F]

omit [Finite G] in
/-- On the entire pure common Borel, the transported action is the native
inner action, including the Cartan elements. -/
theorem native_inner_action
    (a : SymplecticMarkedMiddleAction L K S
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F))
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    a.action (inclusion a.middle_le b) =
      SourceNormalizerExtension.restriction
        (SourceNormalizerExtension.innerBorel (a.comparison.middle b)) := by
  apply RankTwoAmalgam.Iso.ext
  · apply MulEquiv.ext
    intro x
    have hx : a.comparison.left.symm ((a.action (inclusion a.middle_le b)).left x) =
        (sourceParabolicAmalgam ![L,K] S).left b * a.comparison.left.symm x *
          ((sourceParabolicAmalgam ![L,K] S).left b)⁻¹ :=
      Subtype.ext (a.left_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg a.comparison.left hx
    simp only [map_mul, map_inv, a.comparison.left_commutes,
      a.comparison.left.apply_symm_apply] at hh
    apply Subtype.ext
    change ((a.action (inclusion a.middle_le b)).left x).val =
      (a.comparison.middle b).val * x.val * (a.comparison.middle b).val⁻¹
    exact congrArg Subtype.val hh
  · apply MulEquiv.ext
    intro x
    have hx : a.comparison.middle.symm ((a.action (inclusion a.middle_le b)).middle x) =
        b * a.comparison.middle.symm x * b⁻¹ :=
      Subtype.ext (a.middle_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg a.comparison.middle hx
    simp only [map_mul, map_inv, a.comparison.middle.apply_symm_apply] at hh
    apply Subtype.ext
    change ((a.action (inclusion a.middle_le b)).middle x).val =
      (a.comparison.middle b).val * x.val * (a.comparison.middle b).val⁻¹
    exact congrArg Subtype.val hh
  · apply MulEquiv.ext
    intro x
    have hx : a.comparison.right.symm ((a.action (inclusion a.middle_le b)).right x) =
        (sourceParabolicAmalgam ![L,K] S).right b * a.comparison.right.symm x *
          ((sourceParabolicAmalgam ![L,K] S).right b)⁻¹ :=
      Subtype.ext (a.right_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg a.comparison.right hx
    simp only [map_mul, map_inv, a.comparison.right_commutes,
      a.comparison.right.apply_symm_apply] at hh
    apply Subtype.ext
    change ((a.action (inclusion a.middle_le b)).right x).val =
      (a.comparison.middle b).val * x.val * (a.comparison.middle b).val⁻¹
    exact congrArg Subtype.val hh

omit [Finite G] in
/-- No further element of the full common normalizer induces a Borel-inner
marked action. This preserves the whole pure overlap exactly. -/
theorem native_inner_action_iff
    (a : SymplecticMarkedMiddleAction L K S
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F))
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    a.action g ∈ (SourceNormalizerExtension.restriction.comp
      (SourceNormalizerExtension.innerBorel (F := F))).range ↔
      g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓
        ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := by
  constructor
  · rintro ⟨c, hc⟩
    let b := a.comparison.middle.symm c
    have he : a.action (inclusion a.middle_le b) = a.action g := by
      rw [a.native_inner_action]
      dsimp only [b]
      rw [a.comparison.middle.apply_symm_apply]
      exact hc
    have hv := congrArg Subtype.val (a.faithful he)
    exact hv ▸ b.property
  · intro hg
    let b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := ⟨g.val,hg⟩
    exact ⟨a.comparison.middle b, (a.native_inner_action b).symm⟩

omit [Finite G] in
/-- On the entire pure common Borel, the transported action is the native
inner action, including the Cartan elements. -/
theorem native_inner_action_reverse
    (a : SymplecticMarkedMiddleAction L K S
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    a.action (inclusion a.middle_le b) =
      SourceNormalizerExtension.reverseRestriction
        (SourceNormalizerExtension.innerBorel (a.comparison.middle b)) := by
  apply RankTwoAmalgam.Iso.ext
  · apply MulEquiv.ext
    intro x
    have hx : a.comparison.left.symm ((a.action (inclusion a.middle_le b)).left x) =
        (sourceParabolicAmalgam ![L,K] S).left b * a.comparison.left.symm x *
          ((sourceParabolicAmalgam ![L,K] S).left b)⁻¹ :=
      Subtype.ext (a.left_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg a.comparison.left hx
    simp only [map_mul, map_inv, a.comparison.left_commutes,
      a.comparison.left.apply_symm_apply] at hh
    apply Subtype.ext
    change ((a.action (inclusion a.middle_le b)).left x).val =
      (a.comparison.middle b).val * x.val * (a.comparison.middle b).val⁻¹
    exact congrArg Subtype.val hh
  · apply MulEquiv.ext
    intro x
    have hx : a.comparison.middle.symm ((a.action (inclusion a.middle_le b)).middle x) =
        b * a.comparison.middle.symm x * b⁻¹ :=
      Subtype.ext (a.middle_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg a.comparison.middle hx
    simp only [map_mul, map_inv, a.comparison.middle.apply_symm_apply] at hh
    apply Subtype.ext
    change ((a.action (inclusion a.middle_le b)).middle x).val =
      (a.comparison.middle b).val * x.val * (a.comparison.middle b).val⁻¹
    exact congrArg Subtype.val hh
  · apply MulEquiv.ext
    intro x
    have hx : a.comparison.right.symm ((a.action (inclusion a.middle_le b)).right x) =
        (sourceParabolicAmalgam ![L,K] S).right b * a.comparison.right.symm x *
          ((sourceParabolicAmalgam ![L,K] S).right b)⁻¹ :=
      Subtype.ext (a.right_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg a.comparison.right hx
    simp only [map_mul, map_inv, a.comparison.right_commutes,
      a.comparison.right.apply_symm_apply] at hh
    apply Subtype.ext
    change ((a.action (inclusion a.middle_le b)).right x).val =
      (a.comparison.middle b).val * x.val * (a.comparison.middle b).val⁻¹
    exact congrArg Subtype.val hh

omit [Finite G] in
/-- No further element of the full common normalizer induces a Borel-inner
marked action. This preserves the whole pure overlap exactly. -/
theorem native_inner_action_iff_reverse
    (a : SymplecticMarkedMiddleAction L K S
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    a.action g ∈ (SourceNormalizerExtension.reverseRestriction.comp
      (SourceNormalizerExtension.innerBorel (F := F))).range ↔
      g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓
        ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := by
  constructor
  · rintro ⟨c, hc⟩
    let b := a.comparison.middle.symm c
    have he : a.action (inclusion a.middle_le b) = a.action g := by
      rw [a.native_inner_action_reverse]
      dsimp only [b]
      rw [a.comparison.middle.apply_symm_apply]
      exact hc
    have hv := congrArg Subtype.val (a.faithful he)
    exact hv ▸ b.property
  · intro hg
    let b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := ⟨g.val,hg⟩
    exact ⟨a.comparison.middle b, (a.native_inner_action_reverse b).symm⟩

omit [Finite G] in
/-- If every marked action extends natively, the lift is faithful and its
full inner preimage is exactly the pure common Borel. Extendibility remains
an explicit unresolved premise, not an assertion of source 5.3.2. -/
theorem native_lift_of_extendible [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (a : SymplecticMarkedMiddleAction L K S
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F))
    (hlift : ∀ g, a.action g ∈ (SourceNormalizerExtension.restriction (F := F)).range) :
    ∃ σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
        SourceNormalizerExtension.flagAutomorphisms F,
      Function.Injective σ ∧ SourceNormalizerExtension.restriction.comp σ = a.action ∧
      (∀ g, DiagramAutomorphisms.PreservesDiagram (σ g).val) ∧
      ∀ g, (σ g).val ∈ (MulAut.conj : Sp F →* MulAut (Sp F)).range ↔
        g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓
          ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := by
  obtain ⟨σ, hσ, _⟩ := SourceNormalizerExtension.existsUnique_lift a.action hlift
  have hs (g) : SourceNormalizerExtension.restriction (σ g) = a.action g :=
    congrArg (fun f => f g) hσ
  refine ⟨σ, ?_, hσ, fun g => SourceNormalizerExtension.flag_preservesDiagram (σ g), ?_⟩
  · exact SourceNormalizerExtension.lift_injective a.action a.faithful σ hσ
  · intro g
    constructor
    · rintro ⟨x, hx⟩
      have hb : x ∈ Theory.SpecificGroups.SymplecticFour.borel (F := F) := (SourceNormalizerExtension.inner_flag_iff hF hn x).mp (by
        rw [hx]
        exact (σ g).property)
      have he : SourceNormalizerExtension.innerBorel (⟨x,hb⟩ : borel (F := F)) = σ g :=
        Subtype.ext hx
      apply (a.native_inner_action_iff g).mp
      refine ⟨⟨x,hb⟩, ?_⟩
      change SourceNormalizerExtension.restriction (SourceNormalizerExtension.innerBorel ⟨x,hb⟩) = _
      rw [he, hs]
    · intro hg
      obtain ⟨b, hb⟩ := (a.native_inner_action_iff g).mpr hg
      have he : SourceNormalizerExtension.innerBorel b = σ g :=
        SourceNormalizerExtension.restriction_injective (hb.trans (hs g).symm)
      exact ⟨b.val, congrArg Subtype.val he⟩

omit [Finite G] in
/-- If every marked action extends natively, the lift is faithful and its
full inner preimage is exactly the pure common Borel. Extendibility remains
an explicit unresolved premise, not an assertion of source 5.3.2. -/
theorem native_lift_of_extendible_reverse [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (a : SymplecticMarkedMiddleAction L K S
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)
    (hlift : ∀ g, a.action g ∈ (SourceNormalizerExtension.reverseRestriction (F := F)).range) :
    ∃ σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
        SourceNormalizerExtension.flagAutomorphisms F,
      Function.Injective σ ∧ SourceNormalizerExtension.reverseRestriction.comp σ = a.action ∧
      (∀ g, DiagramAutomorphisms.PreservesDiagram (σ g).val) ∧
      ∀ g, (σ g).val ∈ (MulAut.conj : Sp F →* MulAut (Sp F)).range ↔
        g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓
          ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := by
  obtain ⟨σ, hσ, _⟩ := SourceNormalizerExtension.existsUnique_reverse_lift a.action hlift
  have hs (g) : SourceNormalizerExtension.reverseRestriction (σ g) = a.action g :=
    congrArg (fun f => f g) hσ
  refine ⟨σ, ?_, hσ, fun g => SourceNormalizerExtension.flag_preservesDiagram (σ g), ?_⟩
  · intro x y hxy
    apply a.faithful
    exact (hs x).symm.trans ((congrArg SourceNormalizerExtension.reverseRestriction hxy).trans (hs y))
  · intro g
    constructor
    · rintro ⟨x, hx⟩
      have hb : x ∈ Theory.SpecificGroups.SymplecticFour.borel (F := F) := (SourceNormalizerExtension.inner_flag_iff hF hn x).mp (by
        rw [hx]
        exact (σ g).property)
      have he : SourceNormalizerExtension.innerBorel (⟨x,hb⟩ : borel (F := F)) = σ g :=
        Subtype.ext hx
      apply (a.native_inner_action_iff_reverse g).mp
      refine ⟨⟨x,hb⟩, ?_⟩
      change SourceNormalizerExtension.reverseRestriction (SourceNormalizerExtension.innerBorel ⟨x,hb⟩) = _
      rw [he, hs]
    · intro hg
      obtain ⟨b, hb⟩ := (a.native_inner_action_iff_reverse g).mpr hg
      have he : SourceNormalizerExtension.innerBorel b = σ g :=
        SourceNormalizerExtension.reverseRestriction_injective (hb.trans (hs g).symm)
      exact ⟨b.val, congrArg Subtype.val he⟩

end SymplecticMarkedMiddleAction

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
