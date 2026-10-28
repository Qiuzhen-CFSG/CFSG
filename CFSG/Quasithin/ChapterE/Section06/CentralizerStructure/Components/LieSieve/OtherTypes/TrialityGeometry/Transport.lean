module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import Theory.SpecificGroups.Triality.RootParabolics
public import Theory.GroupTheory.RelativeNormalizerTransport

/-!
# Triality parabolics in the actual E.6.8 quotient

Pull the genuine D4 graph-field parabolics back through a model isomorphism
and embed them in the component. Their images in (L Q_L)/O₂(L Q_L) generate
the component image whenever the finite model parabolics generate. The full
preimage of each image is exactly its ambient parabolic joined with the
embedded two-core. Thus adjoining Q absorbs that kernel when O₂(L Q_L) ≤ Q.
Normalizer invariance also descends through these actual maps.

Sylow conjugacy aligns a model isomorphism with the actual Q intersection.
These are transport results: finite parabolic generation, Sylow maximality,
stabilizer invariance, characteristic two and relative block exclusion remain
explicit premises. In particular, split-group generation does not prove the
finite fixed-point generation premise. No auxiliary triality model is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and the root parabolics of GLS3 §2.6.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
open _root_.Triality.Standard

variable {G : Type*} [Group G] {Q L : Subgroup G} {P : Parameters}

/-- The root-defined whole parabolic, pulled back to L and then included in G. -/
def componentParabolic (e : L ≃* Carrier P) (a : Parabolics.Node) : Subgroup G :=
  ((Parabolics.parabolic P a).comap e.toMonoidHom).map L.subtype

/-- Its actual image in (L Q_L)/O₂(L Q_L). -/
def quotientParabolic (Q : Subgroup G) (e : L ≃* Carrier P)
    (a : Parabolics.Node) : Subgroup (ComponentQuotient Q L) :=
  ((componentParabolic e a).subgroupOf (componentExtension Q L)).map (quotientMap Q L)

/-- The local overgroup whose characteristic two and blocks must be calculated. -/
def parabolicJoin (Q : Subgroup G) (e : L ≃* Carrier P)
    (a : Parabolics.Node) : Subgroup G := componentParabolic e a ⊔ Q

/-- Transport retains containment in the specified component. -/
theorem componentParabolic_le (e : L ≃* Carrier P) (a : Parabolics.Node) :
    componentParabolic e a ≤ L := map_subtype_le _

/-- Each quotient parabolic lies in the component image. -/
theorem quotientParabolic_le_component (e : L ≃* Carrier P) (a : Parabolics.Node) :
    quotientParabolic Q e a ≤ componentImage Q L :=
  map_mono (comap_mono (componentParabolic_le e a))

/-- Generation of the finite model descends through the component isomorphism. -/
theorem componentParabolic_sup (e : L ≃* Carrier P)
    (hgen : Parabolics.parabolic P .arms ⊔ Parabolics.parabolic P .central = ⊤) :
    componentParabolic e .arms ⊔ componentParabolic e .central = L := by
  simp only [componentParabolic, Subgroup.comap_equiv_eq_map_symm']
  rw [← Subgroup.map_sup, ← Subgroup.map_sup, hgen, map_top_of_surjective _ e.symm.surjective,
    ← MonoidHom.range_eq_map, L.range_subtype]

/-- The two images generate precisely the component image in the actual quotient. -/
theorem quotientParabolic_sup (e : L ≃* Carrier P)
    (hgen : Parabolics.parabolic P .arms ⊔ Parabolics.parabolic P .central = ⊤) :
    quotientParabolic Q e .arms ⊔ quotientParabolic Q e .central =
      componentImage Q L := by
  have hle (a : Parabolics.Node) : componentParabolic e a ≤ componentExtension Q L :=
    (componentParabolic_le e a).trans le_sup_left
  rw [quotientParabolic, quotientParabolic, ← Subgroup.map_sup,
    ← subgroupOf_sup (hle .arms) (hle .central), componentParabolic_sup e hgen]
  rfl

/-- Ambient normalization descends to normalization by the actual Q_L image. -/
theorem quotientParabolic_invariant (e : L ≃* Carrier P) (a : Parabolics.Node)
    (hN : Q ≤ normalizer (componentParabolic e a : Set G)) :
    sylowImage Q L ≤ normalizer (quotientParabolic Q e a : Set (ComponentQuotient Q L)) := by
  apply le_trans (map_mono (comap_mono (inf_le_left.trans hN)))
  exact (map_mono ((componentParabolic e a).le_normalizer_comap
    (componentExtension Q L).subtype)).trans
      (((componentParabolic e a).subgroupOf (componentExtension Q L)).le_normalizer_map
        (quotientMap Q L))

/-- The entire lost kernel is retained in the pullback identity. -/
theorem quotientParabolic_preimage (e : L ≃* Carrier P) (a : Parabolics.Node) :
    quotientPreimage Q L (quotientParabolic Q e a) =
      componentParabolic e a ⊔ (componentExtension Q L).pCoreIn 2 := by
  have hle : componentParabolic e a ≤ componentExtension Q L :=
    (componentParabolic_le e a).trans le_sup_left
  rw [quotientPreimage, quotientParabolic, comap_map_eq, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hle]
  rw [quotientMap, QuotientGroup.ker_mk']
  rfl

/-- Adjoining Q absorbs the two-core kernel, with no centerlessness premise. -/
theorem quotientParabolic_preimage_join (e : L ≃* Carrier P) (a : Parabolics.Node)
    (hcore : (componentExtension Q L).pCoreIn 2 ≤ Q) :
    quotientPreimage Q L (quotientParabolic Q e a) ⊔ Q = parabolicJoin Q e a := by
  rw [quotientParabolic_preimage, sup_assoc, sup_eq_right.mpr hcore]
  rfl

/-- Invariance under Sylow-stabilizing model automorphisms gives Q_L invariance. -/
theorem componentParabolic_invariant_of_stabilizer (e : L ≃* Carrier P)
    (hmark : (Q.subgroupOf L).map e.toMonoidHom = Parabolics.unipotent P)
    (a : Parabolics.Node)
    (hstable : ∀ β : MulAut (Carrier P),
      (Parabolics.unipotent P).map β.toMonoidHom = Parabolics.unipotent P →
      (Parabolics.parabolic P a).map β.toMonoidHom = Parabolics.parabolic P a) :
    componentNormalizer Q L ≤ normalizer (componentParabolic e a : Set G) := by
  simpa only [componentNormalizer, componentParabolic, comap_equiv_eq_map_symm'] using
    normalizes_pullback_of_stabilizer_invariant e (Parabolics.unipotent P)
      (Parabolics.parabolic P a) hmark hstable

/-- Enumerate the arms and central parabolics for the finite-family interface. -/
def nodeOfFin (i : Fin 2) : Parabolics.Node := if i = 0 then .arms else .central

/-- The two-element quotient family has the required generation property. -/
theorem quotientParabolic_generate (e : L ≃* Carrier P)
    (hgen : Parabolics.parabolic P .arms ⊔ Parabolics.parabolic P .central = ⊤) :
    componentImage Q L ≤ ⨆ i : Fin 2, quotientParabolic Q e (nodeOfFin i) := by
  rw [← quotientParabolic_sup e hgen]
  apply sup_le
  · exact le_iSup_of_le (0 : Fin 2) (by simp [nodeOfFin])
  · exact le_iSup_of_le (1 : Fin 2) (by simp [nodeOfFin])

/-- Transport explicitly supplied local calculations to the quotient-family interface.
This construction does not discharge those model calculations. -/
def familyOfParabolics (e : L ≃* Carrier P)
    (hcore : (componentExtension Q L).pCoreIn 2 ≤ Q)
    (hgen : Parabolics.parabolic P .arms ⊔ Parabolics.parabolic P .central = ⊤)
    (hN : ∀ a, Q ≤ normalizer (componentParabolic e a : Set G))
    (hchar : ∀ a, HasCharacteristicTwo (parabolicJoin Q e a))
    (hfree : ∀ a, NoChiZeroBlocks (parabolicJoin Q e a)) :
    BlockFreeQuotientFamily Q L where
  count := 2
  subgroup i := quotientParabolic Q e (nodeOfFin i)
  le_component i := quotientParabolic_le_component e _
  invariant i := quotientParabolic_invariant e _ (hN _)
  characteristic_two i := by
    rw [quotientParabolic_preimage_join e _ hcore]
    exact hchar _
  no_blocks i := by
    rw [quotientParabolic_preimage_join e _ hcore]
    exact hfree _
  generate := quotientParabolic_generate e hgen

variable [Finite G] {K : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}

/-- Conjugate the model isomorphism to align the actual component Sylow.
Only the model unipotent Sylow assertion is an additional premise. -/
theorem exists_marked_model_equiv (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (e : L ≃* Carrier P)
    (hSylow : ∃ S : Sylow 2 (Carrier P), (S : Subgroup _) = Parabolics.unipotent P) :
    ∃ e' : L ≃* Carrier P,
      (Q.subgroupOf L).map e'.toMonoidHom = Parabolics.unipotent P := by
  obtain ⟨R, hR⟩ := component_sylow_intersection h hU hL
  have hQR : Q.subgroupOf L = (R : Subgroup L) := by
    apply map_injective L.subtype_injective
    rw [subgroupOf_map_subtype, hR, hQ, inf_comm]
  obtain ⟨S, hS⟩ := hSylow
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Carrier P) R' S
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hQR, ← hS]
  change (R : Subgroup L).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← map_map]
  exact congrArg Sylow.toSubgroup hg

/-- E.6 supplies control of the two-core; the remaining premises are the
finite model generation, invariance, characteristic-two and block calculations. -/
theorem family_of_local_parabolics (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) (e : L ≃* Carrier P)
    (hgen : Parabolics.parabolic P .arms ⊔ Parabolics.parabolic P .central = ⊤)
    (hinv : ∀ a, Q ≤ normalizer (componentParabolic e a : Set G))
    (hchar : ∀ a, HasCharacteristicTwo (parabolicJoin Q e a))
    (hfree : ∀ a, NoChiZeroBlocks (parabolicJoin Q e a)) :
    Nonempty (BlockFreeQuotientFamily Q L) :=
  ⟨familyOfParabolics e (extension_core_le_Q h hU hL hQ hN) hgen hinv hchar hfree⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
