module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Model
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Transported binary flags for component refinement

Flags consist of actual nonzero proper binary subspaces in a chain. Their
stabilizers are transported through the canonical matrix action of PSLₙ(2).
Invariance is only under N_S(L), while the associated local overgroup is
formed with all of S. Conjugation by a component element transports each
subspace to its linear image. Generation by two intrinsic flag stabilizers
then gives generation of ⟨L,S⟩ by their ambient overgroups.

A nontrivial Dynkin action is expressed by conjugation carrying a transported
subspace stabilizer to one of different dimension. `ExcludedFlagShape`
selects the flags needed for the binary obstruction calculation; it does not
assert that their overgroups satisfy any block obstruction.

Source: Aschbacher–Smith 2.3.9(7), printed pp.525–526, and the invariant
parabolic convention in the proof of E.2.2, printed p.216. Graph-invariant
parabolics may be flag stabilizers rather than single-subspace stabilizers.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup

abbrev Space (n : ℕ) := Submodule (ZMod 2) (Vector n)

structure Flag (n : ℕ) where
  spaces : Finset (Space n)
  nonempty : spaces.Nonempty
  proper : ∀ W ∈ spaces, W ≠ ⊥ ∧ W ≠ ⊤
  chain : ∀ W ∈ spaces, ∀ W' ∈ spaces, W ≤ W' ∨ W' ≤ W

noncomputable def Flag.types {n : ℕ} (F : Flag n) : Finset ℕ :=
  F.spaces.image (fun W : Space n => Module.finrank (ZMod 2) W)

def ExcludedFlagShape {n : ℕ} (F : Flag n) : Prop :=
  (n = 4 ∧ (F.types = {1} ∨ F.types = {3})) ∨
  (n = 5 ∧ (F.types = {1} ∨ F.types = {4} ∨
    F.types = {1, 4} ∨ F.types = {2, 3}))

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} [NeZero n]

noncomputable def subspaceStabilizer (e : L ≃* PSL n) (W : Space n) : Subgroup L :=
  (BinaryLinear.parabolic W).comap (linearModel e).toMonoidHom

noncomputable def flagStabilizer (e : L ≃* PSL n) (F : Flag n) : Subgroup L :=
  ⨅ W : {W : Space n // W ∈ F.spaces}, subspaceStabilizer e W.val

noncomputable def ambientFlagStabilizer (e : L ≃* PSL n) (F : Flag n) : Subgroup G :=
  (flagStabilizer e F).map L.subtype

noncomputable def flagOvergroup (e : L ≃* PSL n) (F : Flag n) (S : Subgroup G) :
    Subgroup G := ambientFlagStabilizer e F ⊔ S

def FlagInvariant (e : L ≃* PSL n) (S : Subgroup G) (F : Flag n) : Prop :=
  S ⊓ normalizer (L : Set G) ≤ normalizer (ambientFlagStabilizer e F : Set G)

def NontrivialDynkinAction (e : L ≃* PSL n) (S : Subgroup G) : Prop :=
  ∃ s : G, s ∈ S ∧ ∃ hs : s ∈ normalizer (L : Set G),
    ∃ W W' : Space n, W ≠ ⊥ ∧ W ≠ ⊤ ∧ W' ≠ ⊥ ∧ W' ≠ ⊤ ∧
      Module.finrank (ZMod 2) W ≠ Module.finrank (ZMod 2) W' ∧
      (subspaceStabilizer e W).map
        (L.normalizerMonoidHom ⟨s, hs⟩).toMonoidHom = subspaceStabilizer e W'

theorem mem_subspaceStabilizer (e : L ≃* PSL n) (W : Space n) (g : L) :
    g ∈ subspaceStabilizer e W ↔ ∀ v, linearModel e g v ∈ W ↔ v ∈ W := Iff.rfl

theorem mem_flagStabilizer (e : L ≃* PSL n) (F : Flag n) (g : L) :
    g ∈ flagStabilizer e F ↔
      ∀ W ∈ F.spaces, ∀ v, linearModel e g v ∈ W ↔ v ∈ W := by
  simp only [flagStabilizer, mem_iInf, mem_subspaceStabilizer, Subtype.forall]

theorem ambientFlagStabilizer_le (e : L ≃* PSL n) (F : Flag n) :
    ambientFlagStabilizer e F ≤ L := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem flagOvergroup_le (e : L ≃* PSL n) (F : Flag n) (S : Subgroup G) :
    flagOvergroup e F S ≤ L ⊔ S :=
  sup_le_sup (ambientFlagStabilizer_le e F) le_rfl

theorem le_flagOvergroup (e : L ≃* PSL n) (F : Flag n) (S : Subgroup G) :
    S ≤ flagOvergroup e F S := le_sup_right

theorem flagOvergroups_generate (e : L ≃* PSL n) (F₁ F₂ : Flag n) (S : Subgroup G)
    (hgen : flagStabilizer e F₁ ⊔ flagStabilizer e F₂ = ⊤) :
    flagOvergroup e F₁ S ⊔ flagOvergroup e F₂ S = L ⊔ S := by
  have hg : ambientFlagStabilizer e F₁ ⊔ ambientFlagStabilizer e F₂ = L := by
    change (flagStabilizer e F₁).map L.subtype ⊔
      (flagStabilizer e F₂).map L.subtype = L
    rw [← Subgroup.map_sup, hgen]
    ext x
    simp
  change (ambientFlagStabilizer e F₁ ⊔ S) ⊔
    (ambientFlagStabilizer e F₂ ⊔ S) = L ⊔ S
  rw [sup_sup_sup_comm, sup_idem, hg]

omit [NeZero n] in
theorem conjugate_parabolic (a : BinaryLinear.GL (Vector n)) (W : Space n) :
    (BinaryLinear.parabolic W).map (MulAut.conj a).toMonoidHom =
      BinaryLinear.parabolic (W.map a.toLinearMap) := by
  calc
    _ = (BinaryLinear.parabolic W).comap (MulAut.conj a).symm.toMonoidHom :=
      Subgroup.map_equiv_eq_comap_symm (MulAut.conj a) _
    _ = _ := ?_
  ext g
  change (∀ v, a.symm (g (a v)) ∈ W ↔ v ∈ W) ↔
    ∀ v, g v ∈ W.map a.toLinearMap ↔ v ∈ W.map a.toLinearMap
  simp only [Submodule.mem_map_equiv]
  constructor
  · intro h v
    simpa using h (a.symm v)
  · intro h v
    simpa using h (a v)

theorem conjugate_subspaceStabilizer (e : L ≃* PSL n) (a : L) (W : Space n) :
    (subspaceStabilizer e W).map (MulAut.conj a).toMonoidHom =
      subspaceStabilizer e (W.map (linearModel e a).toLinearMap) := by
  calc
    _ = (subspaceStabilizer e W).comap (MulAut.conj a).symm.toMonoidHom :=
      Subgroup.map_equiv_eq_comap_symm (MulAut.conj a) _
    _ = _ := ?_
  ext g
  change (linearModel e (a⁻¹ * g * a) ∈ BinaryLinear.parabolic W) ↔
    linearModel e g ∈ BinaryLinear.parabolic (W.map (linearModel e a).toLinearMap)
  have hc := congrArg (fun P : Subgroup (BinaryLinear.GL (Vector n)) =>
    linearModel e g ∈ P) (conjugate_parabolic (linearModel e a) W)
  have hm : (BinaryLinear.parabolic W).map (MulAut.conj (linearModel e a)).toMonoidHom =
      (BinaryLinear.parabolic W).comap (MulAut.conj (linearModel e a)).symm.toMonoidHom :=
    Subgroup.map_equiv_eq_comap_symm (MulAut.conj (linearModel e a)) _
  rw [hm] at hc
  change ((linearModel e a)⁻¹ * linearModel e g * linearModel e a ∈
      BinaryLinear.parabolic W) = _ at hc
  simpa only [map_mul, map_inv] using Iff.of_eq hc

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
