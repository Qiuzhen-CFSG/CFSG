module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Duality
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.NaturalDual
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Dimension
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Geometry.Assembly
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The normal-L₁ natural-module and geometry branch

The ambient natural marking supplies both the homogeneous decomposition of
Ũ_J and the geometric restrictions in 12.8.5. Homogeneity retains the actual
ambient Sylow subgroup, which excludes graph twists, and the derived actor
GL_(n−1)(2)′, which is C₃ when n=3. The geometric branch proves natural-action
generation, lifts through O₂(L), and uses relative normality to obtain Gᵢ≤M,
uniqueness of the conjugate containing Vᵢ, and the intersection rank bound.

Natural seed simplicity also supplies the literal invariant-subgroup criterion
and V∩Z(U)=V₁ in the nonabelian branch. The resulting commutator duality is a
binary linear equivalence U/C_U(V) ≃ (V/V₁)∨ with evaluation and equivariance.
Homogeneity and genuine natural non-self-duality give n≤3 using the invariant
commutator form and its radical from 12.8.8(2).

These are conditional source implications. The 12.8.1 setup, the earlier
12.2.5–6 and 12.8.3 inputs, the elementary quotient in 12.8.4, and the form
in 12.8.8(2) remain with the Section08 preliminary assembly. No homogeneity,
generation, geometric conclusion or dimension bound remains as a premise.
The n=3 chief-series refinements of 12.8.8(5) also stay with that owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 12.8.5 and 12.8.8(3,5), printed pp.850–852 (PDF pp.867–869).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative MonoidAlgebra Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
  [IsElementaryAbelian 2 (F.tilde V)]
variable {L : Subgroup G} {hLV : L ≤ normalizer (V : Set G)}

/-- The full ambient natural marking supplies the exact conjugation action and
its two-core kernel used by the geometric branch. -/
noncomputable def AmbientNaturalMarking.geometryAction
    (A : AmbientNaturalMarking L hLV n) : NormalGeometry.NaturalAction L V where
  action := (BinaryLinear.SmallParabolicLevi.linearGroupCongr A.coordinates.symm).toMonoidHom.comp
    (A.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  surjective := (BinaryLinear.SmallParabolicLevi.linearGroupCongr A.coordinates.symm).surjective.comp
    (A.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  conjugation l v := by
    have he : A.coordinates.symm
        (A.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) (A.coordinates v)) =
        Additive.ofMul ⟨(l : G) * v.toMul * (l : G)⁻¹,
          (mem_normalizer_iff.mp (hLV l.property) v.toMul).mp v.toMul.property⟩ := by
      rw [← A.equivariant, A.coordinates.symm_apply_apply]
    exact congrArg (fun v : Additive V => (v.toMul : G)) he
  kernel := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (BinaryLinear.SmallParabolicLevi.linearGroupCongr A.coordinates.symm).injective,
      MonoidHom.ker_comp_of_injective _ _ A.quotientEquiv.injective, QuotientGroup.ker_mk']

omit [Finite G] in
/-- Natural-module simplicity gives the invariant-subgroup criterion for the
literal section V/V₁, including the C₃ actor when n=3. -/
theorem NaturalSeedMarking.invariant_subgroup
    (D : F.NaturalSeedMarking L hLV) (hn : 3 ≤ n)
    (A : Subgroup G) (hpoint : F.Vi 1 ≤ A) (hAV : A ≤ V)
    (hKA : F.Li L 1 ≤ normalizer (A : Set G)) : A = F.Vi 1 ∨ A = V := by
  let σ := F.localSeedRepresentation L hLV
  let S : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2
      ((F.tilde A).subgroupOf (F.tilde V)).toAddSubgroup
    apply_mem_toSubmodule k v hv := by
      obtain ⟨w, hw⟩ := F.tildeMap_surjective V
        ((le_conjugateSpanBy V F.H).trans F.U_le_H) v.toMul
      have hwA : (w : G) ∈ A := by
        apply (F.mem_tilde_iff_of_point_le A hpoint
          ⟨w, F.U_le_H (le_conjugateSpanBy V F.H w.property)⟩).mp
        change ((F.tildeMap V ((le_conjugateSpanBy V F.H).trans F.U_le_H)) w : F.G₁tilde) ∈ F.tilde A
        rw [hw]
        exact hv
      change (F.tildeAction (F.Li L 1) V _ _ k v.toMul : F.G₁tilde) ∈ F.tilde A
      rw [← hw, F.tildeAction_apply_map]
      apply (F.mem_tilde_iff_of_point_le A hpoint _).mpr
      exact (mem_normalizer_iff.mp (hKA k.property) w).mp hwA }
  let := D.seed_simple hn
  rcases eq_bot_or_eq_top S.asSubmodule with hS | hS
  · left
    apply le_antisymm _ hpoint
    intro a ha
    let v : Additive (F.tilde V) := Additive.ofMul
      (F.tildeMap V ((le_conjugateSpanBy V F.H).trans F.U_le_H) ⟨a, hAV ha⟩)
    have hv : σ.asModuleEquiv.symm v ∈ S.asSubmodule := by
      change F.tildeProjection ⟨a, _⟩ ∈ F.tilde A
      exact (F.mem_tilde_iff_of_point_le A hpoint _).mpr ha
    have hz : v = 0 := by
      have := (Submodule.mem_bot (R := (ZMod 2)[F.Li L 1])).mp (hS ▸ hv)
      exact congrArg σ.asModuleEquiv this
    have hq : F.tildeProjection ⟨a, F.U_le_H (le_conjugateSpanBy V F.H (hAV ha))⟩ = 1 :=
      congrArg (fun v : Additive (F.tilde V) => (v.toMul : F.G₁tilde)) hz
    change (⟨a, F.U_le_H (le_conjugateSpanBy V F.H (hAV ha))⟩ : F.H) ∈
      (F.Vi 1).subgroupOf F.H
    exact (QuotientGroup.eq_one_iff _).mp hq
  · right
    apply le_antisymm hAV
    intro a ha
    let v : Additive (F.tilde V) := Additive.ofMul
      (F.tildeMap V ((le_conjugateSpanBy V F.H).trans F.U_le_H) ⟨a, ha⟩)
    have hv : σ.asModuleEquiv.symm v ∈ S.asSubmodule := hS ▸ Submodule.mem_top
    exact (F.mem_tilde_iff_of_point_le A hpoint _).mp hv

/-- Construct the irreducibility input to 12.8.8(3) from the ambient natural action. -/
theorem invariant_subgroup_of_ambient_natural (A : AmbientNaturalMarking L hLV n)
    (hn : 3 ≤ n) (W : Subgroup G) (hpoint : F.Vi 1 ≤ W) (hWV : W ≤ V)
    (hKW : F.Li L 1 ≤ normalizer (W : Set G)) : W = F.Vi 1 ∨ W = V := by
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient hn L hLV A
  exact D.invariant_subgroup F hn W hpoint hWV hKW

/-- Source 12.8.8(3) with its natural-module irreducibility premise discharged. -/
theorem seed_inf_center_eq_point_of_ambient_natural
    (A : AmbientNaturalMarking L hLV n) (hn : 3 ≤ n)
    (hnonab : ¬ IsMulCommutative F.U) : V ⊓ F.ZU = F.Vi 1 :=
  F.seed_inf_center_eq_point L (by omega) hLV
    (F.invariant_subgroup_of_ambient_natural A hn) hnonab

/-- The actual binary linear duality used in 12.8.8(5), retaining commutator
evaluation and simultaneous L₁-conjugation. The elementary quotient gives the
commutator bound, and the natural marking gives the right radical V₁. -/
theorem exists_seed_commutator_linear_duality_of_ambient_natural
    (A : AmbientNaturalMarking L hLV n) (hn : 3 ≤ n)
    [IsElementaryAbelian 2 (F.tilde F.U)] (hnonab : ¬ IsMulCommutative F.U) :
    letI := F.seedCentralizer_normal (by omega : 1 ≤ n) F.seed_commutator_le_point
    letI := F.seedCentralizerQuotient_elementary (by omega : 1 ≤ n)
      F.seed_commutator_le_point (F.seed_inf_center_eq_point_of_ambient_natural A hn hnonab)
    ∃ e : Additive (F.U ⧸ (centralizer (V : Set G)).subgroupOf F.U) ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2) (Additive (V ⧸ (F.Vi 1).subgroupOf V)),
      (∀ (u : F.U) (v : V),
        e (Additive.ofMul (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U) u))
          (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf V) v)) =
            (F.seedCommutatorCharacters (by omega) F.seed_commutator_le_point u v).toAdd) ∧
      (∀ (j : F.Li L 1) (u : F.U) (v : V),
        e (Additive.ofMul (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U)
            (F.uAction ⟨j, (F.Li_le L 1 j.property).2⟩ u)))
          (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf V)
            ⟨(j : G) * v * (j : G)⁻¹,
              (mem_normalizer_iff.mp (hLV (F.Li_le L 1 j.property).1) v).mp v.property⟩)) =
        e (Additive.ofMul (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U) u))
          (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf V) v))) :=
  F.exists_seed_commutator_linear_duality L (by omega) hLV
    (F.invariant_subgroup_of_ambient_natural A hn) hnonab F.seed_commutator_le_point

omit [IsElementaryAbelian 2 (F.tilde V)] in
/-- Every clause of 12.8.5(2), using the same ambient marking as 12.8.5(1).
Generation and the ambient product factorization are proved outputs. The source
inputs retained here are O²(L)=L, M=N_G(L), 12.2.5(2), 12.2.6 and 12.8.3(2,3). -/
theorem normal_Li_one_geometry_of_ambient_natural
    (A : AmbientNaturalMarking L hLV n) (hn : 2 < n) {M : Subgroup G}
    (hL : pResidual 2 L = ⊤) (hM : M = normalizer (L : Set G))
    (hL1 : ((F.Li L 1).subgroupOf F.H).Normal)
    (hTI : ∀ g ∈ M, V ⊓ conjugate V g = ⊥ ∨ conjugate V g = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hplanes : ∀ W : Subgroup G, W ≤ V → Nat.card W = 4 →
      ∃ l ∈ L, conjugate W l = F.Vi 2)
    (htrans : ∀ i, 1 < i → i < n → ∀ g : G, F.Vi i ≤ conjugate V g →
      ∃ k ∈ F.Gi i, conjugate V g = conjugate V k) :
    (∀ i, 1 < i → i < n →
      conjugateSpanBy (F.Li L 1) (L ⊓ F.Gi i) = L ∧
      (F.Gi i : Set G) = (centralizer (F.Vi i : Set G) : Set G) *
        (L ⊓ F.Gi i : Subgroup G) ∧
      F.Gi i ≤ M ∧ F.Gi i ≤ seedNormalizer M V ∧
      ∀ g : G, F.Vi i ≤ conjugate V g → conjugate V g = V) ∧
    ∀ g : G, g ∉ seedNormalizer M V →
      primeRank 2 (V ⊓ conjugate V g : Subgroup G) ≤ 1 :=
  NormalGeometry.normal_geometry F A.geometryAction hn hL hM hL1 hTI hNV hplanes htrans

/-- The n≤3 conclusion of 12.8.8(5). The homogeneous decomposition is supplied
by 12.8.5(1), not assumed. Restriction of the invariant commutator form to the
seed gives the nonzero map to its dual, contradicting natural non-self-duality
in dimensions three and four. The invariant form and its literal radical are
the explicit earlier 12.8.8(2) inputs; no assumption Z(U)=V₁ is made. -/
theorem normal_Li_one_nonabelian_rank_le_three
    (A : AmbientNaturalMarking L hLV n) (hn : n ≤ 5)
    [((F.Li L 1).subgroupOf F.H).Normal] [IsElementaryAbelian 2 (F.tilde F.U)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (F.tilde F.U)))
    (hB : ∀ (j : F.Li L 1) u v,
      B (Additive.ofMul (F.localTildeAction F.H le_rfl
        ⟨j, (F.Li_le L 1 j.property).2⟩ u.toMul))
        (Additive.ofMul (F.localTildeAction F.H le_rfl
          ⟨j, (F.Li_le L 1 j.property).2⟩ v.toMul)) = B u v)
    (hrad : ∀ v : Additive (F.tilde F.U),
      (∀ u, B u v = 0) ↔ (v.toMul : F.G₁tilde) ∈ F.tilde F.ZU)
    (hnonab : ¬ IsMulCommutative F.U) : n ≤ 3 := by
  by_contra h
  exact F.nonabelian_exclusion_of_ambient_natural (by omega) hn L hLV A B hB hrad hnonab

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
