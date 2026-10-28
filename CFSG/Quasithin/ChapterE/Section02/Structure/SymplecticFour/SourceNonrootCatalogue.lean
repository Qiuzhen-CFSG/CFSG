module

public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceNonrootSocle
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.SpecificGroups.SymplecticFour.SmallOddLinear

/-!
# The inherited source catalogue of the root-free opposition socle

The original core identities make the Fitting subgroup trivial, so its simple
generalized Fitting subgroup is the perfect ordinary layer. The inherited
SQTK hypothesis therefore gives the complete genuine Theorem C catalogue.
Its odd-field rank-one row collapses to the actual A5 or A6 models by the
four-dimensional symplectic action, for all field parameters.

This supplies the catalogue input to the all-c2 paragraph of Aschbacher--Smith
E.2.7, printed p.220. It does not identify the entire pair with its socle or
claim the subsequent coefficient-field and Borel markings.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate InvolutionTypes
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The actual simple socle inherits Theorem C, with every odd PSL2 row
reduced to A5 or A6. The two cores and simplicity are the already proved
source outputs, rather than additional classification premises. -/
theorem nonroot_pair_socle_catalogue {n : ℕ} (hF : Nat.card F=2^n)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (L : Subgroup G) (e : Sp F ≃* L)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hr : 2<Nat.card V)
    (hc : V≤(CentralRootGeometry.parameter (F := F)).range)
    (h2 : pCore 2 (oppositePair V)=⊥)
    (hnr : ∀ g ∈ oppositePair V, ¬IsRootElement g) :
    let I := generalizedFitting (oppositePair V)
    ChapterA.Section02.IsTheoremCModel I ∧
    ¬Group.IsSolvable I ∧
    (∀ q : ℕ, Odd q → ClassicalGroup.IsPSL I 2 q →
      Nonempty (I ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (I ≃* alternatingGroup (Fin 6))) := by
  let P := oppositePair V
  let I := generalizedFitting P
  have ho : pPrimeCore 2 P=⊥ :=
    oppositePair_oddCore_eq_bot_of_nonroot_central hF V hr hc hnr
  have hfit : fittingSubgroup P=⊥ :=
    le_bot_iff.mp (ho ▸ fitting_le_pPrimeCore_of_pCore_eq_bot 2 h2)
  let : IsSimpleGroup I :=
    oppositePair_generalizedFitting_simple_of_nonroot_central hF V hr hc h2 hnr
  have hperfect : Group.IsPerfect I := by
    change Group.IsPerfect (↥(fittingSubgroup (↥P) ⊔ componentLayer (↥P)))
    rw [hfit,bot_sup_eq]
    exact componentLayer_isPerfect
  let := hperfect
  have hsq := (((hG.subgroup L).knownSimple_of_equiv e.symm).subgroup P).subgroup I
  have hns : ¬Group.IsSolvable I := Group.IsPerfect.not_isSolvable I
  refine ⟨ChapterA.Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative I) hsq.stronglyQuasithin hsq.isKGroup,hns,?_⟩
  intro q hq hm
  obtain ⟨K,_,_,hK,⟨a⟩⟩ := hm
  have hnK : ¬Group.IsSolvable PSL(2,K) := by
    intro hs
    let := hs
    exact hns (Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective)
  rcases odd_psl2_equiv_alternating_five_or_six (hK.symm ▸ hq) hnK
      (P.subtype.comp (I.subtype.comp a.symm.toMonoidHom))
      (P.subtype_injective.comp (I.subtype_injective.comp a.symm.injective)) with h5 | h6
  · exact Or.inl (h5.map (a.trans ·))
  · exact Or.inr (h6.map (a.trans ·))

/-- The catalogue theorem on the original marked source pullback, with all
core, simplicity, and central-plane premises discharged by source geometry. -/
theorem source_geometry_nonroot_socle_catalogue {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V)
    (hnr : ∀ g ∈ oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),
      ¬IsRootElement g) :
    let W := V.comap (L.subtype.comp e.toMonoidHom)
    let I := generalizedFitting (oppositePair W)
    ChapterA.Section02.IsTheoremCModel I ∧
    ¬Group.IsSolvable I ∧
    (∀ q : ℕ, Odd q → ClassicalGroup.IsPSL I 2 q →
      Nonempty (I ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (I ≃* alternatingGroup (Fin 6))) := by
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  obtain ⟨_,hmap,hc,_,h2⟩ := source_geometry hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr
  have hcard : Nat.card W=Nat.card V := by
    rw [←hmap,card_map_of_injective hf]
  let j : W →* V := (f.comp W.subtype).codRestrict V (fun x => x.property)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective j (by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun z : V => (z : G)) h)))
  exact nonroot_pair_socle_catalogue hF hG L e W (hcard.symm ▸ hr)
    (CentralRootGeometry.parameter_range (F := F) ▸ hc) h2 hnr

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
