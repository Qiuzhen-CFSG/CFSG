module

public import Stellmacher.SectionOne.OneSevenFactorDefs
public import Stellmacher.DirectProductMap

/-!
# Original-module Baumann factor data

The ambient factor data records one common family of quotient SL2 factors
and four-element commutator modules. The richer action data retains their
raw factors inside a normal quotient subgroup, with the exact restricted
action on the original module. It also records solvability, faithfulness,
the trivial two-core, injective indexing, relative factor normality, and
the intrinsic and ambient module decompositions.

The raw product is the canonical subgroupOf of the actual closure image;
its subtype map is required to equal that full image. The projection maps
the same raw factors by the injective subtype homomorphism and preserves
their same ambient commutator modules. It does not infer joint independence
or product cardinality from the internal-product-family predicate.

These interfaces support Stellmacher (2.2), journal p.20, and the natural
factor action used in (4.6), p.26, on the unchanged original module.
Source: refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionTwo
universe u

/-- One common family of quotient factors and ambient commutator modules for V and L. -/
public structure BaumannFactorModuleData
    {G barG : Type u} [Group G] [Group barG] [Finite barG]
    (V L : Subgroup G) (q : G →* barG) : Prop where
  factors : ∃ (n : ℕ) (D : Fin n → Subgroup barG) (Vf : Fin n → Subgroup G),
    L.map q = ⨆ i, D i ∧
    IsInternalDirectProductFamily (L.map q) D ∧
    (∀ i, IsSL2Two (D i)) ∧
    (∀ i, Vf i = ambientCommutator ((D i).comap q) V ∧ Nat.card (Vf i) = 4) ∧
    IsInternalDirectProductFamily V
      (fun i : Option (Fin n) => match i with
        | none => V ⊓ Subgroup.centralizer (L : Set G)
        | some i => Vf i)

/-- The same normal-quotient factors retain their natural action on the original
module and their exact images in the ambient quotient and ambient group. -/
public structure BaumannFactorActionData
    {G barG : Type u} [Group G] [Group barG] [Finite G] [Finite barG]
    (V L : Subgroup G) (q : G →* barG) (barN : Subgroup barG)
    [MulDistribMulAction barG V] : Prop where
  solvable : Group.IsSolvable barN
  faithful : fixingSubgroup barN (Set.univ : Set V) = ⊥
  twoCore_eq_bot : pCore 2 barN = ⊥
  factors :
    let L0 := (L.map q).subgroupOf barN
    ∃ (n : ℕ) (D : Fin n → Subgroup barN),
      L0.map barN.subtype = L.map q ∧
      IsInternalDirectProductFamily L0 D ∧
      Function.Injective D ∧
      (∀ i, SectionOne.IsOneSevenFactor (V := V) (D i)) ∧
      (∀ i, ((D i).subgroupOf L0).Normal) ∧
      IsInternalDirectProductFamily (⊤ : Subgroup V)
        (fun i : Option (Fin n) => match i with
          | none => FixedPoints.subgroup L0 V
          | some i => commutatorAction (D i) V) ∧
      (∀ i, (commutatorAction (D i) V).map V.subtype =
          ambientCommutator (((D i).map barN.subtype).comap q) V ∧
        Nat.card ((commutatorAction (D i) V).map V.subtype) = 4) ∧
      IsInternalDirectProductFamily V
        (fun i : Option (Fin n) => match i with
          | none => V ⊓ Subgroup.centralizer (L : Set G)
          | some i => (commutatorAction (D i) V).map V.subtype)

/-- Forget the raw action data while retaining the very same factor/module family. -/
public theorem BaumannFactorActionData.toModuleData
    {G barG : Type u} [Group G] [Group barG] [Finite G] [Finite barG]
    {V L : Subgroup G} {q : G →* barG} {barN : Subgroup barG}
    [MulDistribMulAction barG V] (h : BaumannFactorActionData V L q barN) :
    BaumannFactorModuleData V L q := by
  rcases h.factors with ⟨n, D, hL, hprod, _, hD, _, _, hV, hVprod⟩
  refine ⟨n, (fun i => (D i).map barN.subtype),
    (fun i => (commutatorAction (D i) V).map V.subtype), ?_, ?_, ?_, hV, hVprod⟩
  · rw [← hL, hprod.1, Subgroup.map_iSup]
  · have hp := hprod.map_injective barN.subtype barN.subtype_injective
    rw [hL] at hp
    exact hp
  · intro i
    obtain ⟨e⟩ := (hD i).1
    exact ⟨(Subgroup.equivMapOfInjective (D i) barN.subtype barN.subtype_injective).symm.trans e⟩

end Stellmacher.SectionTwo
