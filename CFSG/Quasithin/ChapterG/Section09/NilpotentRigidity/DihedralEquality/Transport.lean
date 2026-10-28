module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Transporting a dihedral classification through an embedding

An injective group homomorphism takes each factor to its actual image.
The displacement spans are equal, and the product and direct-sum
coordinates preserve the canonical inclusions. The natural orthogonal
intertwiner is transported together with the group equivalence.

This is the final passage from a representation of a dihedral product to
its embedded image in Aschbacher--Smith G.9.2, printed pp.351--353.
The exposed constructor bodies specify the resulting factor images.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

universe u v w
variable {G : Type u} [Group G] {L : Type w} [Group L]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (f : L →* G)

theorem movedSpace_map (K : Subgroup L) :
    movedSpace ρ (K.map f) = movedSpace (ρ.comp f) K := by
  change Submodule.span (ZMod 2)
      (Set.range fun kv : K.map f × V => ρ kv.1 kv.2 - kv.2) =
    Submodule.span (ZMod 2)
      (Set.range fun kv : K × V => ρ (f kv.1) kv.2 - kv.2)
  congr 1
  ext v
  constructor
  · rintro ⟨⟨⟨g, hg⟩, v⟩, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hg
    exact ⟨(⟨k, hk⟩, v), rfl⟩
  · rintro ⟨⟨k, v⟩, rfl⟩
    exact ⟨(⟨f k, ⟨k, k.property, rfl⟩⟩, v), rfl⟩

noncomputable def InternalDecomposition.mapEmbedding
    (hf : Function.Injective f) {H : Subgroup L} {r : ℕ}
    (d : InternalDecomposition (ρ.comp f) H r) :
    InternalDecomposition ρ (H.map f) r := by
  let eg (K : Subgroup L) := K.equivMapOfInjective f hf
  let ev (K : Subgroup L) := LinearEquiv.ofEq _ _ (movedSpace_map ρ f K)
  refine
    { factor := fun i => (d.factor i).map f
      groupEquiv := (MulEquiv.piCongrRight fun i => (eg (d.factor i)).symm).trans
        (d.groupEquiv.trans (eg H))
      group_inclusion := ?_
      spaceEquiv := (LinearEquiv.piCongrRight fun i => ev (d.factor i)).trans d.spaceEquiv
      space_inclusion := ?_ }
  · intro i g
    have hsingle : (MulEquiv.piCongrRight fun j => (eg (d.factor j)).symm)
        (Pi.mulSingle i g) = Pi.mulSingle i ((eg (d.factor i)).symm g) := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [MulEquiv.piCongrRight, Pi.mulSingle_eq_of_ne hj]
    change f (d.groupEquiv ((MulEquiv.piCongrRight fun j =>
      (eg (d.factor j)).symm) (Pi.mulSingle i g))) = (g : G)
    rw [hsingle, d.group_inclusion]
    exact congrArg Subtype.val ((eg (d.factor i)).apply_symm_apply g)
  · intro i v
    have hsingle : (LinearEquiv.piCongrRight fun j => ev (d.factor j))
        (Pi.single i v) = Pi.single i ((ev (d.factor i)) v) := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [LinearEquiv.piCongrRight_apply, Pi.single_eq_of_ne hj]
    change d.spaceEquiv ((LinearEquiv.piCongrRight fun j =>
      ev (d.factor j)) (Pi.single i v)) = (v : V)
    rw [hsingle, d.space_inclusion]
    rfl

theorem isNaturalOmegaFour_map (hf : Function.Injective f) (K : Subgroup L)
    (h : IsNaturalOmegaFour (ρ.comp f) K (movedSpace (ρ.comp f) K)) :
    IsNaturalOmegaFour ρ (K.map f) (movedSpace ρ (K.map f)) := by
  obtain ⟨e, l, h⟩ := h
  let eg := K.equivMapOfInjective f hf
  let ev := LinearEquiv.ofEq _ _ (movedSpace_map ρ f K)
  refine ⟨eg.symm.trans e, ev.trans l, ?_⟩
  intro g v
  have hg : f (eg.symm g) = (g : G) :=
    congrArg Subtype.val (eg.apply_symm_apply g)
  have hh := h (eg.symm g) (ev v)
  change ρ (f (eg.symm g)) v = _ at hh
  rw [hg] at hh
  exact hh

theorem isOrdinaryFactor_map (hf : Function.Injective f) (K : Subgroup L)
    (h : IsOrdinaryFactor (ρ.comp f) K) : IsOrdinaryFactor ρ (K.map f) := by
  rcases h with ⟨⟨e⟩, hd⟩ | ⟨he, hd⟩
  · exact Or.inl ⟨⟨(K.equivMapOfInjective f hf).symm.trans e⟩,
      by rwa [movedSpace_map]⟩
  · exact Or.inr ⟨isNaturalOmegaFour_map ρ f hf K he,
      by rwa [movedSpace_map]⟩

noncomputable def ClassifiedDecomposition.mapEmbedding
    (hf : Function.Injective f) {H : Subgroup L} {exceptional : Prop}
    (d : ClassifiedDecomposition (ρ.comp f) H exceptional) :
    ClassifiedDecomposition ρ (H.map f) exceptional := by
  refine
    { count := d.count
      internal := d.internal.mapEmbedding ρ f hf
      exceptional_factor := ?_
      ordinary_factor := ?_ }
  · intro he
    obtain ⟨hpos, ⟨e⟩, hd⟩ := d.exceptional_factor he
    refine ⟨hpos, ⟨((d.internal.factor ⟨0, hpos⟩).equivMapOfInjective f hf).symm.trans e⟩, ?_⟩
    change Module.finrank (ZMod 2) (movedSpace ρ ((d.internal.factor ⟨0, hpos⟩).map f)) = 4
    rwa [movedSpace_map]
  · intro i hi
    exact isOrdinaryFactor_map ρ f hf _ (d.ordinary_factor i hi)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
