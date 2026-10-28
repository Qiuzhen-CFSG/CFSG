module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Setup

/-!
# Ambient normality of the residual-selected product factors

A selected S₃ factor has ambient-normal cubic residual X. Conjugate the
factor by an ambient element and project to the other product coordinate.
Every square lies in X, so this projection is a normal elementary two-group.
The other coordinate has trivial two-core; hence the projection vanishes.
Thus each conjugate is contained in the original selected factor.

The actual star consumers obtain the trivial two-core from the Sylow-central
seed, and the normal residual from MinimalSolvable. No support, transitivity,
irreducibility, or normality of the selected overgroup is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3),(5), printed p.105, and the first construction of 13.6.13, p.929.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson
variable {D : Type*} [Group D]
private def swapProduct {A B : Subgroup D} (h : InternalProduct A B) : InternalProduct B A where
  equiv := MulEquiv.prodComm.trans h.equiv
  apply_eq b a := by
    change h.equiv (a, b) = (b : D) * a
    have hc := congrArg h.equiv (show (a, (1 : B)) * (1, b) = (1, b) * (a, 1) by simp)
    rw [map_mul, map_mul, h.apply_eq, h.apply_eq] at hc
    simpa only [h.apply_eq, OneMemClass.coe_one, mul_one, one_mul] using hc

private theorem core_normal (N : Subgroup D) [N.Normal] (hc : pCore 2 D = ⊥) :
    pCore 2 N = ⊥ := by
  have hl : (pCore 2 N).map N.subtype ≤ pCore 2 D :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map N.subtype⟩
  rw [hc] at hl
  apply (pCore 2 N).eq_bot_iff_forall.mpr
  intro x hx
  apply Subtype.ext
  exact hl (mem_map_of_mem N.subtype hx)

private theorem square_residual {A : Type*} [Group A]
    (e : A ≃* Equiv.Perm (Fin 3)) (a : A) : a ^ 2 ∈ pResidual 2 A := by
  have he := map_pResidual 2 e
  rw [Equiv.Perm.twoResidual_eq_alternating] at he
  apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
  rw [he]
  have hh : ∀ x : Equiv.Perm (Fin 3), x ^ 2 ∈ alternatingGroup (Fin 3) := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  change e (a ^ 2) ∈ alternatingGroup (Fin 3)
  rw [map_pow]
  exact hh (e a)

private theorem selected_first_normal (I : Subgroup D) [I.Normal]
    {A B : Subgroup I} (h : InternalProduct A B)
    (hc : pCore 2 I = ⊥) (e : A ≃* Equiv.Perm (Fin 3))
    (hn : (((pResidual 2 A).map A.subtype).map I.subtype).Normal) :
    (A.map I.subtype).Normal := by
  let hs := swapProduct h
  let : A.Normal := hs.second_normal
  let : B.Normal := h.second_normal
  have hcB := core_normal B hc
  let R := (pResidual 2 A).map A.subtype
  let : (R.map I.subtype).Normal := hn
  have hRA : R ≤ A := map_subtype_le _
  have hproj : Function.Surjective hs.fst := by
    intro b
    refine ⟨hs.equiv (b, 1), ?_⟩
    exact congrArg Prod.fst (hs.equiv.symm_apply_apply (b, 1))
  constructor
  rintro x ⟨a, ha, rfl⟩ g
  let α : MulAut I := MulAut.conjNormal g
  let C := (A.map α.toMonoidHom).map hs.fst
  have hCn : C.Normal :=
    ((inferInstance : A.Normal).map _ α.surjective).map _ hproj
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨y, ⟨b, hb, rfl⟩, he⟩ := c.property
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (c : B) ^ (2 ^ 1) = 1
    rw [pow_one, ← he, ← map_pow, ← map_pow]
    have hsq : b ^ 2 ∈ R := mem_map_of_mem A.subtype (square_residual e (⟨b, hb⟩ : A))
    have hconj := hn.conj_mem (b ^ 2 : I) (mem_map_of_mem I.subtype hsq) g
    have hα : α (b ^ 2) ∈ R := by
      apply (mem_map_iff_mem I.subtype_injective).mp
      exact hconj
    change α (b ^ 2) ∈ hs.fst.ker
    rw [hs.ker_fst]
    exact hRA hα
  have hC : C = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcB]
    exact le_sSup ⟨hCn, hCp⟩
  have hm : hs.fst (α a) ∈ C := mem_map_of_mem hs.fst (mem_map_of_mem α.toMonoidHom ha)
  have hα : α a ∈ A := by
    rw [hC, mem_bot] at hm
    have hk : α a ∈ hs.fst.ker := hm
    rwa [hs.ker_fst] at hk
  exact mem_map_of_mem I.subtype hα
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]

/-- The global Thompson image lies in the actual offender actor and retains
X's full commutator. This uses Sylow conjugacy, not monotonicity of J. -/
theorem minimalSolvable_global_thompson (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X) :
    JGstar z v ≤ FFFactors.offenderActor (starRepresentation z v) ∧
      ⁅X, JGstar z v⁆ = X := by
  let A := starImage z v (elementaryAbelianMaxJ (Tv T v))
  have hAJ : A ≤ JGstar z v := by
    rw [JGstar_eq_conjugateSpan T z v ⟨S, hS⟩]
    exact le_conjugateSpanBy A ⊤
  constructor
  · rw [JGstar_eq_conjugateSpan T z v ⟨S, hS⟩]
    exact conjugateSpanBy_le (thompson_le_star_offender T z v hz S hS)
      (by rw [normalizer_eq_top])
  · let : X.Normal := hX.1.2
    apply le_antisymm (commutator_le_left _ _)
    exact hX.1.1.2.2.2.ge.trans (commutator_mono le_rfl hAJ)

/-- Residual selection descends through the literal inclusion of the offender actor. -/
theorem minimalSolvable_selected_residual (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    : let I := FFFactors.offenderActor (starRepresentation z v)
      ∀ (F : Subgroup I), X.subgroupOf I = (pResidual 2 F).map F.subtype →
        (pResidual 2 (F.map I.subtype)).map (F.map I.subtype).subtype = X := by
  intro I F hF
  rw [← map_embedded_pResidual, ← hF,
    map_subgroupOf_eq_of_le (XFamily_le_star_offender L T z v hz S hS hX.1)]

private theorem selected_normal (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    : let I := FFFactors.offenderActor (starRepresentation z v)
      ∀ {F K : Subgroup I}, InternalProduct F K → (F ≃* Equiv.Perm (Fin 3)) →
        X.subgroupOf I = (pResidual 2 F).map F.subtype → (F.map I.subtype).Normal := by
  intro I F K hp e hF
  have hR : ((pResidual 2 F).map F.subtype).map I.subtype = X := by
    rw [← hF, map_subgroupOf_eq_of_le
      (XFamily_le_star_offender L T z v hz S hS hX.1)]
  exact NormalThompson.selected_first_normal I hp
    (FFFactors.offender_twoCore (starRepresentation z v)
      (Gstar_twoCore_eq_bot T z v ⟨S, hS⟩ hfix)) e (hR.symm ▸ hX.1.2)

/-- Ambient normality of the first selected factor in native B.5.6(3). -/
theorem minimalSolvable_twoFactor_first_normal (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.first _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.first.subtype (pResidual 2 c.first)) :
    (c.first.map (FFFactors.offenderActor (starRepresentation z v)).subtype).Normal :=
  selected_normal L T z v hz S hS hfix hX c.product e hF

/-- Ambient normality of the second selected factor in native B.5.6(3). -/
theorem minimalSolvable_twoFactor_second_normal (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.second.subtype (pResidual 2 c.second)) :
    (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype).Normal :=
  selected_normal L T z v hz S hS hfix hX (NormalThompson.swapProduct c.product) e hF

/-- The residual selected by native B.5.6(5) makes its second factor ambient normal. -/
theorem minimalSolvable_hyperplane_second_normal (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.second.subtype (pResidual 2 c.second)) :
    (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype).Normal :=
  selected_normal L T z v hz S hS hfix hX (NormalThompson.swapProduct c.product) e hF

/-- The published hyperplane selection discharges both the model and residual premises. -/
theorem minimalSolvable_hyperplane_normal (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v))) :
    (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype).Normal := by
  obtain ⟨⟨e⟩, hF⟩ := minimalSolvable_hyperplane_choice L T z v hz S hS hX c
  exact minimalSolvable_hyperplane_second_normal L T z v hz S hS hfix hX c e hF

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
