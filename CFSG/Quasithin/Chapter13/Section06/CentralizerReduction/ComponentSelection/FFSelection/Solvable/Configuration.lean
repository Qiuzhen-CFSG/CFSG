module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Preparation

/-!+# The factor-construction target in 13.6.13

This structure specifies the actual output to be constructed from B.5.6
for a minimal solvable member X. The group and module product maps agree
with the original factor inclusions. In particular the factors are actual
subgroups of G*_v and the supports are actual commutators inside U_v.

This is an output specification, not a source hypothesis or a construction
theorem. Neither existence, transitivity, irreducibility nor the projection
of L*_v is a field. The source-theorem assembly must construct these data
before using the subsequent finite-group argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
universe u
variable {G : Type u} [Group G]

/-- The actual subgroup denoted [U_v,H] in the source. -/
def movedSubgroup (z v : G) (H : Subgroup (Gstar z v)) : Subgroup G :=
  ⁅Uv z v, starPreimage z v H⁆

/-- Each support is the actual double commutator U_i = [U_H,H_i]. -/
def factorSupport (z v : G) (H A : Subgroup (Gstar z v)) : Subgroup G :=
  ⁅movedSubgroup z v H, starPreimage z v A⁆

/-- Required construction output, retaining O²(H) and the marked internal
products. This record deliberately carries no later inference from 13.6.13. -/
structure NormalS3Decomposition (z v : G) (X : Subgroup (Gstar z v)) where
  H : Subgroup (Gstar z v)
  normal : H.Normal
  count : ℕ
  count_pos : 0 < count
  count_le_two : count ≤ 2
  factor : Fin count → Subgroup (Gstar z v)
  factor_le : ∀ i, factor i ≤ H
  model : ∀ i, factor i ≃* Equiv.Perm (Fin 3)
  product : (∀ i, factor i) ≃* H
  product_single : ∀ i a, (product (Pi.mulSingle i a) : Gstar z v) = a
  residual_eq : (pResidual 2 H).map H.subtype = X
  thompson_eq : starImage z v (Stellmacher.elementaryAbelianMaxJ (starPreimage z v H)) = H
  space : (∀ i, factorSupport z v H (factor i)) ≃* movedSubgroup z v H
  space_single : ∀ i a, (space (Pi.mulSingle i a) : G) = a
  support_card : ∀ i, Nat.card (factorSupport z v H (factor i)) = 4

/-- The subgroup used by the finite-group branch lies in the original module. -/
theorem movedSubgroup_le_Uv (z v : G) (H : Subgroup (Gstar z v)) :
    movedSubgroup z v H ≤ Uv z v :=
  le_normalizer_iff_commutator_le_left.mp
    ((starPreimage_le_Gv z v H).trans (Gv_normalizes_Uv z v))

/-- The classification construction supplies a containing moved subgroup
for the literal U_X. This uses its residual equality, not an assumed
identification U_X = U_H. -/
theorem NormalS3Decomposition.UX_le (L : Subgroup G) (z v : G)
    {X : Subgroup (Gstar z v)} (d : NormalS3Decomposition z v X) :
    UX L z v X ≤ movedSubgroup z v d.H := by
  have hXH : X ≤ d.H :=
    d.residual_eq.symm.le.trans (map_subtype_le (pResidual 2 d.H))
  have hpre : starPreimage z v X ≤ starPreimage z v d.H :=
    map_mono (comap_mono hXH)
  exact (UX_le_moved L z v X).trans (commutator_mono le_rfl hpre)

/-- Consumer of the constructed product: after the independent orbit
argument proves irreducibility, the marked seed forces L_v to move U_H. -/
theorem NormalS3Decomposition.marked_moved_commutator [Finite G]
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : X ∈ XFamily L T (A5Module.markedZ s) (A5Module.markedV s))
    (d : NormalS3Decomposition (A5Module.markedZ s) (A5Module.markedV s) X)
    (hirr : IrreducibleOn
      (starPreimage (A5Module.markedZ s) (A5Module.markedV s) X ⊔ Tv T (A5Module.markedV s))
      (movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) d.H)) :
    UX L (A5Module.markedZ s) (A5Module.markedV s) X =
        movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) d.H ∧
      ⁅movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) d.H,
        Lv L (A5Module.markedV s)⁆ ≠ ⊥ :=
  marked_UX_eq_and_commutator_ne_bot s T S hS hfix hL hX _ (d.UX_le L _ _) hirr

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
end
