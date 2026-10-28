module
public import CFSG.Quasithin.ChapterG.Section11.Catalogue
public import Theory.Representation.BinaryPermutation.SevenParabolic
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightCoordinates
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison
public import Theory.Alternating.Aut

/-!
# The nontrivial smaller actor and the two permutation rows

The natural A₇ row is incompatible with the original G.10 geometry when
its smaller actor is nontrivial. Transport to the actual seven-point action
identifies the invariant form and preserves the literal actor quotient;
the existing complementary-plane calculation gives the contradiction.

For the split six-dimensional row, the faithful S₈ comparison constructs
a normal, self-centralizing A₈ with its actual deleted permutation action.
The HS source consumer uses its point stabilizer to exclude this row.
No exhaustive G.11 recognition or strict-D hypothesis is assumed.

The split comparison is adapted from the rank-two source calculation in
`ComponentCatalogueLargeActorDegreesFive`, now for an arbitrary action.
Source: Aschbacher--Smith, 12.8.13(6--8), G.11.2(4--5), and 14.3.24,
printed pp.855--857,364,1000.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
open Representation.BinaryOffender BinaryPermutation.SevenParabolic
private theorem binary_rank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Group.rank A = finrank (ZMod 2) (Additive A) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply le_antisymm (IsElementaryAbelian.rank_le_finrank (p := 2) A)
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hc]
  exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))

/-- A nontrivial smaller actor excludes the literal natural A₇ row. -/
theorem not_caseFour_of_smaller_ne_bot
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X Z : Subgroup G}
    [IsElementaryAbelian 2 X]
    (h : Section10.Hypothesis ρ B v W X (Z.subgroupOf X))
    (hZX : Z ≤ X) (hZ : Z ≠ ⊥) : ¬ CaseFour ρ := by
  rintro ⟨hd,eK,eV,he⟩
  let K := generalizedFitting G
  obtain ⟨f,hf,hfK,hact⟩ := faithful_extension K ρ h.faithful eK eV he
  have hAlt : alternatingGroup (Fin 7) ≤ f.range := by
    intro a ha
    obtain ⟨k,hk⟩ := eK.surjective ⟨a,ha⟩
    exact ⟨k,by rw [hfK,hk]⟩
  have hform (u w : V) : B u w = pairing (eV u) (eV w) :=
    marked_form_eq K ρ eK eV he B h.nondegenerate (fun k => h.preserves k) u w
  have hv : eV v ≠ 0 := fun hh => h.point_ne_zero (eV.injective (hh.trans eV.map_zero.symm))
  have hmapFix : (fixedSpace ρ X).map eV.toLinearMap = fixedSpace (action.comp f) X := by
    ext w
    obtain ⟨u,rfl⟩ := eV.surjective w
    rw [Submodule.mem_map_equiv,eV.symm_apply_apply]
    constructor
    · intro hu x
      change action (f x) (eV u) = eV u
      rw [← hact]
      exact congrArg eV (hu x)
    · intro hu x
      apply eV.injective
      change eV (ρ (x:G) u) = eV u
      rw [hact]
      exact hu x
  have hfixed : W.map eV.toLinearMap ⊓ fixedSpace (action.comp f) X =
      Submodule.span (ZMod 2) {eV v} := by
    have hh := congrArg (fun P : Submodule (ZMod 2) V => P.map eV.toLinearMap) h.fixedSpace_in_W
    rwa [Submodule.map_inf _ eV.injective,hmapFix,Submodule.map_span,Set.image_singleton] at hh
  apply exclude f hf hAlt X X Z le_rfl hZX (W.map eV.toLinearMap) (eV v) hv
  · intro x hx
    rw [← hact]
    exact congrArg eV (h.fixes_point hx)
  · rintro _ ⟨u,hu,rfl⟩ _ ⟨w,hw,rfl⟩
    exact (hform u w).symm.trans (h.isotropic u hu w hw)
  · rintro x hx _ ⟨u,hu,rfl⟩
    change action (f x) (eV u) - eV u ∈ Submodule.span (ZMod 2) {eV v}
    obtain ⟨l,_,hl⟩ := h.transvections ⟨x,hx⟩
    rw [← hact,hl ⟨u,hu⟩,map_add,map_smul,add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact hfixed
  · intro x hx w hw
    obtain ⟨u,rfl⟩ := eV.surjective w
    rw [← hact,← map_sub]
    exact Submodule.mem_map_of_mem (h.displacement ⟨x,hx⟩ u ((hform v u).trans hw))
  · rw [eV.finrank_map_eq]
    have hh := h.dimension
    rwa [binary_rank,hd] at hh
  · exact fun _ => hZ

noncomputable section
namespace SplitSix
open BinaryPermutation.TerminalOrthogonal
private def splitPermutationEquiv : Equiv.Perm (Fin 8) ≃*
    Theory.AlgebraicGroup.quadraticIsometrySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2)) :=
  MulEquiv.ofBijective Atlas.Order20160A8.DeletedEight.orthogonalHom
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨Atlas.Order20160A8.DeletedEight.orthogonalHom_injective,
        Nat.card_congr ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv.toEquiv⟩)

private def splitCoordinates :
    (ClassicalOrthogonal.formD 3 (ZMod 2)).IsometryEquiv Eight.form :=
  Atlas.Order20160A8.DeletedEight.splitIsometry.trans
    { __ := Eight.naturalEquiv, map_app' := Eight.form_naturalEquiv }

private theorem split_equivariant
    (a : Theory.AlgebraicGroup.quadraticIsometrySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2)))
    (w : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
    splitCoordinates (a.val w) = BinaryPermutation.naturalRepresentation (Fin 8)
      (splitPermutationEquiv.symm a) (splitCoordinates w) := by
  obtain ⟨σ,rfl⟩ := splitPermutationEquiv.surjective a
  rw [MulEquiv.symm_apply_apply]
  change Eight.naturalEquiv
    (Atlas.Order20160A8.DeletedEight.splitEquiv
      ((Atlas.Order20160A8.DeletedEight.orthogonalHom σ).val w)) = _
  change Eight.naturalEquiv (Atlas.Order20160A8.DeletedEight.splitEquiv
    (Atlas.Order20160A8.DeletedEight.splitEquiv.symm
      (Atlas.Order20160A8.DeletedEight.quotientPerm σ
        (Atlas.Order20160A8.DeletedEight.splitEquiv w)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Eight.naturalEquiv_equivariant σ _

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Construct the actual self-centralizing A₈ subgroup and its equivariant
quadratic coordinates from the split six-space row. -/
theorem caseFive_selfcentralizing_marking
    (h5 : ChapterG.Section11.CaseFive ρ B) :
    ∃ q : QuadraticForm (ZMod 2) V,
      ∃ c : q.IsometryEquiv Eight.form,
      ∃ K : Subgroup G, K.Normal ∧ centralizer (K : Set G) = ⊥ ∧
      ∃ e : K ≃* alternatingGroup (Fin 8),
        ∀ (k : K) (u : V),
          c (ρ k u) =
            BinaryPermutation.naturalRepresentation (Fin 8) (e k).val (c u) := by
  obtain ⟨_,q,_,f,hq,H,hH,e,he⟩ := h5
  let a := splitPermutationEquiv.symm
  let J := H.map a.toMonoidHom
  have hJ : J.index ≤ 2 := by
    rw [show J.index = H.index from Subgroup.index_map_equiv H a]
    exact hH
  have hAJ : alternatingGroup (Fin 8) ≤ J :=
    Equiv.Perm.alternatingGroup_le_of_index_le_two hJ
  let j : G →* Equiv.Perm (Fin 8) :=
    a.toMonoidHom.comp (H.subtype.comp e.toMonoidHom)
  have hj : Function.Injective j := a.injective.comp (H.subtype_injective.comp e.injective)
  have hr : j.range = J := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact mem_map_of_mem a.toMonoidHom (e t).property
    · rintro ⟨t,ht,rfl⟩
      obtain ⟨r,hr⟩ := e.surjective ⟨t,ht⟩
      exact ⟨r, congrArg (fun z : H => a z.val) hr⟩
  let K := (alternatingGroup (Fin 8)).comap j
  let kmap : K →* alternatingGroup (Fin 8) :=
    (j.comp K.subtype).codRestrict _ (fun k => k.property)
  have hk : Function.Bijective kmap := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hj (congrArg Subtype.val hxy))
    · intro x
      obtain ⟨t,ht⟩ := (hr.symm ▸ hAJ x.property : x.val ∈ j.range)
      exact ⟨⟨t,show j t ∈ alternatingGroup (Fin 8) from ht.symm ▸ x.property⟩,Subtype.ext ht⟩
  have hcent : centralizer (K : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    have hfix : j x ∈ centralizer (alternatingGroup (Fin 8) : Set (Equiv.Perm (Fin 8))) := by
      intro σ hσ
      obtain ⟨k,hσk⟩ := hk.surjective ⟨σ,hσ⟩
      have he := congrArg j (hx k k.property)
      simpa only [map_mul,show j (k : G) = σ from congrArg Subtype.val hσk] using he
    rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 8 (by decide)] at hfix
    exact mem_bot.mpr (hj ((mem_bot.mp hfix).trans j.map_one.symm))
  let c₀ : q.IsometryEquiv (ClassicalOrthogonal.formD 3 (ZMod 2)) :=
    { __ := f, map_app' := fun w => (hq w).symm }
  let c := c₀.trans splitCoordinates
  refine ⟨q,c,K,inferInstance,hcent,MulEquiv.ofBijective kmap hk,?_⟩
  intro k u
  change splitCoordinates (f (ρ k u)) = _
  rw [he]
  exact split_equivariant (e k).val (f u)


end SplitSix
end
end CFSG.Quasithin.ChapterG.Section11
