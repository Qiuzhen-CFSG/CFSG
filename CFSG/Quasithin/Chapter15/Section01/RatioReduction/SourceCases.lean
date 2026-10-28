module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperOrbitOmega
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitNoncyclic
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitDecomposable
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitNine
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitExtraspecial

/-!
# The six original centralizing alternatives of15.1.2

The selected local action constructs its classified starred partition.
The proper-orbit argument gives the literal moved four-space, its natural
Ω action, and the centralizer product of index three. A full transitive
partition has two factors, or one. Two factors give the exchanged dihedral
case. A single noncyclic factor gives Ω4; a cyclic factor gives the marked
dihedral, elementary-nine, or extraspecial27 endpoint. The latter two are
placed in the full ambient image using the proved residual and original
Sylow geometry. All cases retain the original actions and embeddings.

The theorem is the centralizing row needed by original15.1.3; it does not
assert the later elimination of its cases. Source: Aschbacher--Smith15.1.2,
printed pp.1084--1086.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
namespace SourceCases
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

def Dihedral (ρ : Representation (ZMod 2) D V) : Prop :=
  ∃ (l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype)) (p m : ℕ),
    CyclicSource.PrimeDimensionOptions p m ∧ CyclicSource.DihedralMarking l p m

def Omega (ρ : Representation (ZMod 2) D V) : Prop :=
  Jhat ρ = ⊤ ∧ cubicRatio ρ = 3 / 2 ∧ Module.finrank (ZMod 2) V = 4 ∧
  Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
  ∃ (x : V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
    (e : D ≃* OrthogonalFourBinary.omega),
    ∀ g v, x (ρ g v) = (e g).val.val (x v)

def Extraspecial (ρ : Representation (ZMod 2) D V) (S : Subgroup D) : Prop :=
  ∃ l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype),
    letI := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
    letI := l.normal
    ChapterD.Section02.ExtraspecialEndpoint (V := Multiplicative V) l.kernel l.involution ∧
    l.kernel.map (Jhat ρ).subtype = pResidual 2 D ∧ IsExtraspecial 3 (pResidual 2 D) ∧
    Nat.card (pResidual 2 D) = 27 ∧ Monoid.exponent (pResidual 2 D) = 3 ∧
    Module.finrank (ZMod 2) V = 6 ∧
    ChapterD.Section03.FrattiniIrreducible S (pResidual 2 D) le_normalizer_of_normal

def Nine (ρ : Representation (ZMod 2) D V) (S : Subgroup D) : Prop :=
  ∃ l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype),
    letI := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
    letI := l.normal
    ChapterD.Section02.ElementaryNineEndpoint (V := Multiplicative V) l.kernel l.involution ∧
    Module.finrank (ZMod 2) V = 4 ∧ Nat.card D = 36 ∧
    l.kernel.map (Jhat ρ).subtype = pResidual 2 D ∧
    (∀ Q : Sylow 2 D, IsCyclic Q ∧ Nat.card Q = 4) ∧
    (IsCyclic S ∧ Nat.card S = 4) ∧
    ∃ (x : V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (f : D →* OrthogonalFourBinary.TerminalLines.IsometryGroup),
      Function.Injective f ∧ ∀ g v, x (ρ g v) = (f g).val (x v)

variable {G : Type u} [Group G] [Finite G]
def Decomposable (ρ : Representation (ZMod 2) D V)
    (T : Subgroup G) (M : Subgroup G) (f : M →* D)
    {U : Submodule (ZMod 2) V} (c : FactorData ρ (Jhat ρ) U)
    (d : Decomposition c.representation) (π : D →* Equiv.Perm d.Index) : Prop :=
  Nat.card d.Index = 2 ∧ ∃ p m, CyclicSource.PrimeDimensionOptions p m ∧
    (∀ i, ∃ l : CyclicSource.LocalGeneration (d.factor i).action,
      CyclicSource.DihedralMarking l p m) ∧
    ∃ i j : d.Index, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
      (c.ambientFactor d i).actor ⊔ (c.ambientFactor d j).actor = Jhat ρ ∧
      Disjoint (c.ambientFactor d i).actor (c.ambientFactor d j).actor ∧
      (∀ x ∈ (c.ambientFactor d i).actor,
        ∀ y ∈ (c.ambientFactor d j).actor, Commute x y) ∧
      IsCompl (c.ambientFactor d i).space (c.ambientFactor d j).space ∧
      ∃ t : M, (t : G) ∈ T ∧ π (f t) i = j ∧ π (f t) j = i

def Proper (T : Sylow 2 G) (M Mc V : Subgroup G) [IsElementaryAbelian 2 V]
    (ρ : Representation (ZMod 2) D (Additive V))
    (U : Submodule (ZMod 2) (Additive V)) : Prop :=
  let Wg := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
  let Fg := (Subgroup.toAddSubgroup.symm (fixedSpace ρ (Jhat ρ)).toAddSubgroup).map V.subtype
  U = subspaceCommutator ρ ⊤ (Jhat ρ) ∧
  Nonempty (Jhat ρ ≃* Equiv.Perm (Fin 3)) ∧ Module.finrank (ZMod 2) U = 4 ∧
  (⊤ : Subgroup D) ≤ subspaceStabilizer ρ U ∧ U ≠ ⊥ ∧ U ≠ ⊤ ∧
  fixedSpace ρ (Jhat ρ) ≠ ⊥ ∧ IsCompl U (fixedSpace ρ (Jhat ρ)) ∧
  Nonempty (subspaceActionImage ρ U ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
  ((M ⊓ centralizer (Wg : Set G) : Subgroup G) : Set G) *
    ((M ⊓ centralizer (Fg : Set G) : Subgroup G) : Set G) * (T : Set G) =
      (M ⊓ Mc : Subgroup G) ∧ (M ⊓ Mc).relIndex M = 3 ∧
  ∃ (x : U ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
    (e : subspaceActionImage ρ U ≃* OrthogonalFourBinary.omega),
    ∀ g u, x (subspaceImageRepresentation ρ U g u) = (e g).val.val (x u)
end SourceCases
variable {G : Type*} [Group G] [Finite G]

theorem source_lemma_15_1_2_centralizing
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let S := (T.subtype hM.1.2 : Subgroup M).map f
    ∃ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation) (π : D →* Equiv.Perm d.Index),
      d.FittingFull ∧
      (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ Jhat ρ ≤ π.ker ∧
      (∀ g i,
        Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
        (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor ∧
        (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space) ∧
      (SourceCases.Dihedral ρ ∨ SourceCases.Omega ρ ∨
        SourceCases.Decomposable ρ (T : Subgroup G) M f c d π ∨
        SourceCases.Extraspecial ρ S ∨ SourceCases.Nine ρ S ∨
        SourceCases.Proper T M Mc V ρ U) := by
  classical
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  obtain ⟨U,c,d,hd,π,hstars,hker,hp⟩ :=
    source_centralizing_classified_partition hG T hempty hM hmany hJ
  refine ⟨U,c,d,π,hd,hstars,hker,hp,?_⟩
  by_cases hfull : U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j
  · by_cases hmore : 1 < Nat.card d.Index
    · exact Or.inr (Or.inr (Or.inl (source_localAction_full_orbit_decomposable
        hG T hempty hM hmany hJ U c d hd hfull.1 π
        (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull.2 hmore)))
    · have hone : Nat.card d.Index = 1 := by
        have hpos := Nat.card_pos (α := d.Index)
        omega
      obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
      by_cases hn : ∃ A ∈ QhatStar (d.factor i).action, 1 < rank A
      · obtain ⟨A,hA,hr⟩ := hn
        exact Or.inr (Or.inl (source_localAction_singleton_noncyclic_full
          hG T hempty hM hmany hJ hu hne U c d hd i hi hfull.1 A hA hr))
      · have hc : ∀ A ∈ QhatStar (d.factor i).action, IsCyclic A := by
          intro A hA
          have hr : rank A = 1 := by
            have hh := hA.1.2.1.rank_pos
            have hn' : ¬1 < rank A := fun h => hn ⟨A,hA,h⟩
            omega
          obtain ⟨t,_,ht⟩ := CyclicSource.starred_generator (d.factor i).action hA hr
          rw [←ht]
          infer_instance
        obtain ⟨l,halt⟩ := source_localAction_singleton_cyclic_endpoints
          hG T hempty hM hmany hJ U c d hd i hi hfull.1 hc
        let := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
        let : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
        let : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
        let := l.normal
        rcases halt with ⟨p,m,hpm,hm⟩ | h9 | hex
        · exact Or.inl ⟨l,p,m,hpm,hm⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l,h9,
            source_localAction_full_orbit_nine hG T hempty hM hmany hJ hu hne
              U c d hd i hi hfull.1 hc l h9⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨l,hex,
            source_localAction_extraspecial_full hG T hM hu hne l hex⟩)))
  · have hsix := source_localAction_proper_orbit_case_six hG T hempty hM hmany hJ hu hne
      U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    obtain ⟨he,hiso,hdim,hstable,hU0,hUt,hF0,hcompl,himage,hprod,hindex⟩ := hsix
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨he,hiso,hdim,hstable,hU0,hUt,hF0,hcompl,himage,hprod,hindex,
        source_localAction_proper_orbit_omega hG T hempty hM hmany hJ hu hne
          U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull⟩))))
end CFSG.Quasithin.Chapter15.Section01
