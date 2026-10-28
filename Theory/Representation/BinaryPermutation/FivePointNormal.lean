module
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.FirstCohomologyNormalRestriction
public import Theory.Representation.FirstCohomologyDuality.Indecomposable
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer
public import Theory.Alternating.Aut
public import Theory.Representation.BinaryPermutation.FiveInvariantHyperplane
public import Theory.Representation.BinaryPermutation.FiveSylowSingular
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Normal subgroups and invariant hyperplanes of the full five-point action

A faithful permutation group containing the marked normal A₅ has trivial
centralizer of that A₅. Consequently every nontrivial normal subgroup
contains it. Restriction to this normal A₅, self-duality of the natural
binary module and its vanishing first cohomology give vanishing dual H¹
for every such normal subgroup.

A Sylow-invariant hyperplane has trivial pointwise fixer: the possible
nontrivial fixer would force a nonsingular Sylow-fixed vector, whereas
all A₅ Sylow-fixed vectors are singular. Both statements retain the
literal component marking and the coordinates of the full action.

Source: Aschbacher–Smith, §B.3, I.1.5–6 and the A₅ branch of
14.3.15, printed pp.408,994.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
namespace BinaryPermutation.FivePointNormal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  (L : Subgroup G) [L.Normal] (e : L ≃* alternatingGroup (Fin 5))
  (p : G →* Equiv.Perm (Fin 5)) (hp : Function.Injective p)
  (he : ∀ l : L, p l = (e l).val)
  (c : V ≃ₗ[ZMod 2] natural (Fin 5))
  (hc : ∀ a v, c (ρ a v) = naturalRepresentation (Fin 5) (p a) (c v))

omit [Finite G] [L.Normal] in
include hp he in
theorem centralizer_eq_bot : centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  intro a ha
  apply mem_bot.mpr
  apply hp
  rw [map_one]
  apply mem_bot.mp
  rw [←GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)]
  intro b hb
  obtain ⟨l,hl⟩ := e.surjective ⟨b,hb⟩
  have hlp : p l = b := (he l).trans (congrArg Subtype.val hl)
  rw [←hlp,←map_mul,←map_mul]
  exact congrArg p (mem_centralizer_iff.mp ha l l.property)

omit [Finite G] in
include hp he in
theorem le_normal (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : L ≤ N := by
  let : IsSimpleGroup L := e.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hna : ¬ IsMulCommutative L := Group.IsPerfect.not_isMulCommutative L
  exact simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot L hna
    (centralizer_eq_bot L e p hp he) N hN

omit [Finite G] in
include hc he hp in
theorem normal_dual_H1_zero (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    Module.finrank (ZMod 2) (H1 (Representation.dual (ρ.comp N.subtype))) = 0 := by
  have hLN := le_normal L e p hp he N hN
  let φ : alternatingGroup (Fin 5) →* N := (inclusion hLN).comp e.symm.toMonoidHom
  have hφ : φ.range = L.subgroupOf N := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact (e.symm b).property
    · intro ha
      refine ⟨e ⟨a.val,ha⟩,?_⟩
      apply Subtype.ext
      change (e.symm (e ⟨a.val,ha⟩) : G) = a.val
      exact congrArg Subtype.val (e.symm_apply_apply ⟨a.val,ha⟩)
  let : φ.range.Normal := hφ ▸ inferInstance
  let r := Representation.dual (ρ.comp N.subtype)
  let σ := alternatingNaturalRepresentation (Fin 5)
  let E := c.symm.dualMap.trans (naturalDualEquiv (Fin 5)).symm
  have hE (a : alternatingGroup (Fin 5)) (f : Module.Dual (ZMod 2) V) :
      E ((r.comp φ) a f) = σ a (E f) := by
    apply (naturalDualEquiv (Fin 5)).injective
    dsimp only [E, LinearEquiv.trans_apply]
    rw [LinearEquiv.apply_symm_apply]
    change c.symm.dualMap ((r.comp φ) a f) = naturalDualEquiv (Fin 5)
      (naturalRepresentation (Fin 5) a.val (E f))
    rw [naturalDualEquiv_equivariant]
    change c.symm.dualMap ((r.comp φ) a f) = σ.dual a (naturalDualEquiv (Fin 5) (E f))
    rw [show naturalDualEquiv (Fin 5) (E f) = c.symm.dualMap f from
      (naturalDualEquiv (Fin 5)).apply_symm_apply _]
    apply LinearMap.ext
    intro w
    change f (ρ ((φ a).val⁻¹) (c.symm w)) = f (c.symm (σ a⁻¹ w))
    congr 1
    apply c.injective
    rw [hc,c.apply_symm_apply,c.apply_symm_apply]
    change naturalRepresentation (Fin 5) (p ((e.symm a).val⁻¹)) w = _
    rw [map_inv,he,e.apply_symm_apply]
    rfl
  let hEq := H1Congr (r.comp φ) σ (MulEquiv.refl _) E hE
  have hdim : Module.finrank (ZMod 2) (H1 (r.comp φ)) = 0 :=
    hEq.finrank_eq.trans alternatingFive_natural_finrank_H1
  let : Module.Finite (ZMod 2) (H1 (r.comp φ)) := Module.Finite.equiv hEq.symm
  let : Subsingleton (H1 (r.comp φ)) := Module.finrank_zero_iff.mp hdim
  have hσ : fixed σ = ⊥ :=
    Representation.BinaryOffender.invariants_eq_bot_of_faithful_irreducible σ
      (fun _ _ hh => Subtype.ext (naturalRepresentation_injective (Fin 5) (by decide) hh))
      (alternatingNatural_isIrreducible (by decide))
  have hfix : fixed (r.comp φ) = ⊥ := by
    apply bot_unique
    intro f hf
    have hh : E f ∈ fixed σ := by
      intro a
      exact (hE a f).symm.trans (congrArg E (hf a))
    have hz : E f = 0 := hσ.le hh
    exact E.injective (hz.trans (map_zero E).symm)
  let := H1_subsingleton_of_normal_range r φ hfix
  exact Module.finrank_zero_of_subsingleton
end BinaryPermutation.FivePointNormal

public noncomputable section
open Subgroup Module Representation
namespace BinaryPermutation.FivePointNormal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
/-- The pointwise fixer of a Sylow-invariant hyperplane is trivial in the
faithful five-point action containing the marked alternating subgroup. -/
theorem hyperplane_fixer_eq_one
    (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [L.Normal] (e : L ≃* alternatingGroup (Fin 5))
    (p : G →* Equiv.Perm (Fin 5)) (hp : Function.Injective p)
    (he : ∀ l : L, p l = (e l).val)
    (c : V ≃ₗ[ZMod 2] core (Fin 5))
    (hc : ∀ a v, c (ρ a v) = coreRepresentation (Fin 5) (p a) (c v))
    (R : Sylow 2 G) (W : Submodule (ZMod 2) V) (hd : finrank (ZMod 2) W = 3)
    (hW : ∀ a ∈ R, ∀ w ∈ W, ρ a w ∈ W)
    (a : G) (ha : ∀ w ∈ W, ρ a w = w) : a = 1 := by
  let W' := (W.map c.toLinearMap).toAddSubgroup.toSubgroup
  have hcard : Nat.card W' = 8 := by
    change Nat.card (W.map c.toLinearMap) = 8
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,c.finrank_map_eq,hd]
    decide
  have hstable : ∀ b ∈ (R : Subgroup G).map p, ∀ w ∈ W',
      Multiplicative.ofAdd (coreRepresentation (Fin 5) b w.toAdd) ∈ W' := by
    rintro b ⟨b,hb,rfl⟩ w ⟨u,hu,heu⟩
    change coreRepresentation (Fin 5) (p b) w.toAdd ∈ W.map c.toLinearMap
    refine ⟨ρ b u,hW b hb u hu,?_⟩
    exact (hc b u).trans (congrArg (coreRepresentation (Fin 5) (p b)) heu)
  have hfix : ∀ w ∈ W', coreRepresentation (Fin 5) (p a) w.toAdd = w.toAdd := by
    rintro w ⟨u,hu,heu⟩
    rw [←heu]
    exact (hc a u).symm.trans (congrArg c (ha u hu))
  rcases FiveInvariantHyperplane.fixed_hyperplane_dichotomy
    ((R : Subgroup G).map p : Set (Equiv.Perm (Fin 5))) W' hcard hstable (p a) hfix
    with hid | ⟨w,hw,hfixed⟩
  · exact hp (hid.trans (map_one p).symm)
  · obtain ⟨P,hP⟩ := R.exists_subgroupOf_eq_of_normal L
    let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
    apply (hw (FiveSylowSingular.fixed_singular S w ?_)).elim
    rintro b ⟨l,hl,rfl⟩
    have hlR : l.val ∈ R := by
      change l ∈ (R : Subgroup G).subgroupOf L
      rwa [←hP]
    change coreRepresentation (Fin 5) (e l).val w = w
    rw [←he l]
    exact hfixed (p l.val) (mem_map_of_mem p hlR)
end BinaryPermutation.FivePointNormal
