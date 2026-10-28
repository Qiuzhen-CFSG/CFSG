module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.Natural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.Orthogonal

/-!
# Source fields and the actual marked sections

The independent natural and orthogonal markings construct the common plane,
its faithful SL₂ action and the fixed-space identity. These supply 11.3.8's
compatible field structure on the original P while preserving Y-conjugation.

For the subsequent complement construction, a linear conjugation displacement
pulls the original point back to a subspace of P. Its identification with
P intersect R₁ and its order remain explicit group-theoretic premises here.
From precisely those premises, the source consumer proves scalar stability,
Cartan invariance, both one-dimensional complements, and the dimensions and
incidence of the literal V₂ and P/V₂. Thus the printed P/V typo is not used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 11.3.8 and
the following complement paragraph, printed pp.774–775.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections

section Source
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (P I : Subgroup G)
    [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (E : BinaryField) (d : OrthogonalMarking E P (f.Li 1 ⊔ I : Subgroup G))

/-- Extract the common-plane datum from the full independent markings.
In particular this datum is constructed, not an extra source hypothesis. -/
def extractedPlaneActions
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I) :
    let := originalModule D (.sl3 m) hfixed
    let := d.moduleStructure
    SeparatePlaneActions (E := E.Carrier) (F := S.field.Carrier) P V (f.Li 1) := by
  let := originalModule D (.sl3 m) hfixed
  let := d.moduleStructure
  exact SeparatePlaneActions.ofFixedPlane d.action d.action_conj
    (hVI.trans le_sup_right) le_sup_left (fixed_plane D S m f P hP hcore)
    (planeCoordinates D S m f P hPV) (planeCoordinates_linear D hfixed S m f P hPV)
    (planeActors D S m f) (planeActors_surjective D S m f)
    (planeCoordinates_conj D S m f P hPV)

include d in
/-- Source 11.3.8 from the independent full action markings and the preceding
core geometry. The plane, SL₂ surjection, linear inclusion and fixed-space
identity are derived, rather than supplied as a separate compatibility datum. -/
theorem exists_compatible_fields
    (hcard : Nat.card E.Carrier = 2 ^ S.field.degree)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I) :
    let := originalModule D (.sl3 m) hfixed
    ∃ mP : Module S.field.Carrier (Additive P),
      let := mP
      (∀ (a : S.field.Carrier) (b : f.Vi 1),
        ((a • Additive.ofMul (⟨b,(show (b : G) ∈ P ⊓ V from hPV.symm ▸ b.property).1⟩ : P)).toMul : G) =
        ((a • Additive.ofMul (⟨b,(show (b : G) ∈ P ⊓ V from hPV.symm ▸ b.property).2⟩ : V)).toMul : G)) ∧
      ∃ ρ : Representation S.field.Carrier (f.Li 1 ⊔ I : Subgroup G) (Additive P),
        ∀ (y : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P),
          ((ρ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G) := by
  let := originalModule D (.sl3 m) hfixed
  let := d.moduleStructure
  obtain ⟨mP,hcompat,ρ,hρ⟩ := exists_compatible_source_fields_of_fixed_plane D S f P
    (f.Li 1 ⊔ I : Subgroup G) hcard hPV d.action d.action_conj (hVI.trans le_sup_right) le_sup_left
    (fixed_plane D S m f P hP hcore) (planeCoordinates D S m f P hPV)
    (planeCoordinates_linear D hfixed S m f P hPV) (planeActors D S m f)
    (planeActors_surjective D S m f) (planeCoordinates_conj D S m f P hPV)
  refine ⟨mP,hcompat,ρ,?_⟩
  intro y p
  rw [hρ]
  exact d.action_conj y p

end Source


section Normalization
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m))

/-- In the odd-degree source placement, the Cartan normalizes each literal radical. -/
theorem cartan_normalizes_radical {X : Subgroup G} (hX : IsCartan T L X)
    (hTL : (T : Subgroup G) ≤ L) (i : Fin 2) :
    X ≤ normalizer (f.Ri i : Set G) := by
  have hXT : X ≤ normalizer ((T : Subgroup G) : Set G) := by
    have ht : sourceTL T L = T := inf_eq_left.mpr (hTL.trans le_sup_left)
    simpa only [cartanNormalizer,ht] using hX.1.trans inf_le_right
  have hXf : X ≤ normalizer (f.Vi i.castSucc : Set G) := by
    rw [flag_eq D S m f]
    exact SL3.cartan_normalizes D S m hX i.castSucc
  have hXL : X ≤ normalizer (L : Set G) := (hX.1.trans inf_le_left).trans L.le_normalizer
  have hXLi : X ≤ normalizer (f.Li i : Set G) :=
    (((le_inf hXL (hXf.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _)))
  exact ((le_inf hXLi hXT).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
end Normalization


section Hyperplane
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (P I : Subgroup G)
    [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)

/-- The original point, with its inherited field structure. -/
def originalPoint :
    let := originalModule D (.sl3 m) hfixed
    Submodule S.field.Carrier (Additive V) := by
  let := originalModule D (.sl3 m) hfixed
  exact (f.space 0).comap
    ((originalCoordinates D (.sl3 m) hfixed).linearEquiv S.field.Carrier).toLinearMap

theorem mem_originalPoint (v : Additive V) :
    v ∈ originalPoint D S m f hfixed ↔ (v.toMul : G) ∈ f.Vi 0 :=
  ((Coordinates.sl3 m).mem_preimage (f.space 0) v.toMul).symm

variable [Module S.field.Carrier (Additive P)]

/-- Agreement on the common subgroup transfers the original point into P. -/
def commonPoint
    (hcommon : letI := originalModule D (.sl3 m) hfixed
      ∀ (a : S.field.Carrier) (b : Additive (P ⊓ V : Subgroup G)),
        ((a • (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
        ((a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G)) :
    Submodule S.field.Carrier (Additive P) := by
  let := originalModule D (.sl3 m) hfixed
  exact {
    __ := ((f.Vi 0).subgroupOf P).toAddSubgroup
    smul_mem' := by
      intro a p hp
      have hv : (p.toMul : G) ∈ V := D.centralQuotientPreimage_le _ hp
      let b : Additive (P ⊓ V : Subgroup G) :=
        Additive.ofMul ⟨p.toMul,p.toMul.property,hv⟩
      have hb : (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b ∈
          originalPoint D S m f hfixed := (mem_originalPoint D S m f hfixed _).mpr hp
      have hs := (mem_originalPoint D S m f hfixed _).mp
        ((originalPoint D S m f hfixed).smul_mem a hb)
      change ((a • p).toMul : G) ∈ f.Vi 0
      rw [show ((a • p).toMul : G) = _ from hcommon a b]
      exact hs }

/-- The hyperplane is the inverse image of the original point under a linear
conjugation displacement. Its ambient identification is a separate group calculation. -/
def radicalHyperplane
    (hcommon : letI := originalModule D (.sl3 m) hfixed
      ∀ (a : S.field.Carrier) (b : Additive (P ⊓ V : Subgroup G)),
        ((a • (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
        ((a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G))
    (ρ : Representation S.field.Carrier (f.Li 1 ⊔ I : Subgroup G) (Additive P))
    (v : V) (hv : (v : G) ∈ f.Li 1 ⊔ I) :
    Submodule S.field.Carrier (Additive P) :=
  (commonPoint D S m f P hfixed hcommon).comap (ρ ⟨v,hv⟩ - LinearMap.id)

variable
    (hcommon : letI := originalModule D (.sl3 m) hfixed
      ∀ (a : S.field.Carrier) (b : Additive (P ⊓ V : Subgroup G)),
        ((a • (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
        ((a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G))
    (ρ : Representation S.field.Carrier (f.Li 1 ⊔ I : Subgroup G) (Additive P))
    (hρ : ∀ (y : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P),
      ((ρ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G))
    (v : V) (hv : (v : G) ∈ f.Li 1 ⊔ I)

include hρ in
theorem mem_radicalHyperplane (p : Additive P) :
    p ∈ radicalHyperplane D S m f P I hfixed hcommon ρ v hv ↔
      ⁅(v : G), (p.toMul : G)⁆ ∈ f.Vi 0 := by
  change (((ρ ⟨v,hv⟩ - (LinearMap.id : Module.End S.field.Carrier (Additive P))) p).toMul : G) ∈ f.Vi 0 ↔ _
  rw [LinearMap.sub_apply,LinearMap.id_apply,sub_eq_add_neg]
  change ((ρ ⟨v,hv⟩ p).toMul : G) * (p.toMul : G)⁻¹ ∈ f.Vi 0 ↔ _
  rw [hρ]
  rfl

include hρ in
/-- A literal group identity identifies the constructed field subspace with P∩R₁. -/
theorem ambient_radicalHyperplane
    (hinc : ∀ p : P, (p : G) ∈ f.Ri 0 ↔ ⁅(v : G), (p : G)⁆ ∈ f.Vi 0) :
    ambientSubgroup (radicalHyperplane D S m f P I hfixed hcommon ρ v hv) = P ⊓ f.Ri 0 := by
  apply le_antisymm
  · rintro g ⟨p,hp,rfl⟩
    exact ⟨p.property,(hinc p).mpr
      ((mem_radicalHyperplane D S m f P I hfixed hcommon ρ hρ v hv _).mp hp)⟩
  · rintro g ⟨hp,hr⟩
    exact ⟨⟨g,hp⟩,(mem_radicalHyperplane D S m f P I hfixed hcommon ρ hρ v hv _).mpr
      ((hinc ⟨g,hp⟩).mp hr),rfl⟩

end Hyperplane

section Dimensions
variable {G F : Type*} [Group G] [Field F] [Finite G] {P : Subgroup G}
    [IsMulCommutative P] [Module F (Additive P)]

omit [Finite G] in
/-- The underlying field subspace and its literal ambient subgroup have equal orders. -/
private theorem card_ambientSubgroup (U : Submodule F (Additive P)) :
    Nat.card (ambientSubgroup U) = Nat.card U := by
  let e : U ≃ ambientSubgroup U := Equiv.ofBijective
    (fun u => ⟨u.val.toMul, (mem_ambientSubgroup U u.val.toMul).mpr u.property⟩) (by
      constructor
      · intro u w h
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg (fun z : ambientSubgroup U => (z : G)) h
      · rintro ⟨g,⟨p,hp,rfl⟩⟩
        exact ⟨⟨Additive.ofMul p,hp⟩,rfl⟩)
  exact Nat.card_congr e.symm

/-- Dimension can be read from the order of the actual ambient subgroup. -/
private theorem finrank_of_ambient_card [Finite F] (U : Submodule F (Additive P)) (n : ℕ)
    (hF : 1 < Nat.card F) (hc : Nat.card (ambientSubgroup U) = Nat.card F ^ n) :
    Module.finrank F U = n := by
  rw [card_ambientSubgroup,Module.natCard_eq_pow_finrank (K := F) (V := U)] at hc
  exact Nat.pow_right_injective hF hc
end Dimensions

section Invariance
variable {G F : Type*} [Group G] [Field F] {P X : Subgroup G}
    [IsMulCommutative P] [Module F (Additive P)]

/-- A literal normalizer acts on the corresponding field subspace. -/
theorem invariant_of_normalizes (U : Submodule F (Additive P))
    (ρ : Representation F X (Additive P))
    (hρ : ∀ (x : X) (p : Additive P),
      ((ρ x p).toMul : G) = MulAut.conj (x : G) (p.toMul : G))
    (hX : X ≤ normalizer (ambientSubgroup U : Set G)) :
    ∀ x : X, ∀ p ∈ U, ρ x p ∈ U := by
  intro x p hp
  apply (mem_ambientSubgroup U (ρ x p).toMul).mp
  rw [hρ]
  exact (mem_normalizer_iff.mp (hX x.property) _).mp
    ((mem_ambientSubgroup U p.toMul).mpr hp)
end Invariance


section Quotient
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (P I : Subgroup G)
    [IsMulCommutative P] [IsMulCommutative V]
    [Module S.field.Carrier (Additive P)]

/-- The actual fixed plane and its quotient both have field dimension two.
The displayed denominator is literally V₂ inside P, correcting the printed P/V. -/
theorem common_plane_sections
    (ρ : Representation S.field.Carrier (f.Li 1 ⊔ I : Subgroup G) (Additive P))
    (hρ : ∀ (y : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P),
      ((ρ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G))
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I)
    (hdim : Module.finrank S.field.Carrier (Additive P) = 4) :
    let U := SeparatePlaneActions.fixedPlane (V := V) ρ
    ambientSubgroup U = f.Vi 1 ∧
      U.toAddSubgroup.toSubgroup = (f.Vi 1).subgroupOf P ∧
      Module.finrank S.field.Carrier U = 2 ∧
      Module.finrank S.field.Carrier ((Additive P) ⧸ U) = 2 := by
  let U := SeparatePlaneActions.fixedPlane (V := V) ρ
  have hmem (p : Additive P) : p ∈ U ↔ (p.toMul : G) ∈ V :=
    SeparatePlaneActions.mem_fixedPlane ρ hρ (hVI.trans le_sup_right)
      (fixed_plane D S m f P hP hcore) p
  have hU : ambientSubgroup U = f.Vi 1 := by
    rw [← hPV]
    apply le_antisymm
    · rintro g ⟨p,hp,rfl⟩
      exact ⟨p.property,(hmem (Additive.ofMul p)).mp hp⟩
    · rintro g ⟨hp,hv⟩
      exact ⟨⟨g,hp⟩,(hmem (Additive.ofMul ⟨g,hp⟩)).mpr hv,rfl⟩
  have hdimU : Module.finrank S.field.Carrier U = 2 := by
    apply finrank_of_ambient_card U 2
    · rw [S.field.card_eq]
      exact Nat.one_lt_pow (Nat.ne_of_gt S.field.degree_pos) (by decide)
    · rw [hU,← hPV]
      exact (Nat.card_congr (planeCoordinates D S m f P hPV).toEquiv).trans
        (by simp only [Nat.card_fun,Nat.card_fin])
  refine ⟨hU,?_,hdimU,?_⟩
  · ext p
    change p.toAdd ∈ U ↔ (p.toAdd.toMul : G) ∈ f.Vi 1
    rw [hmem,← hPV]
    exact ⟨fun h => ⟨p.toAdd.toMul.property,h⟩, fun h => h.2⟩
  · change Module.finrank S.field.Carrier ((Additive P) ⧸ U) = 2
    have h := U.finrank_quotient_add_finrank
    rw [hdimU,hdim] at h
    dsimp only [U] at h ⊢
    omega
end Quotient


section Assembly
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (P I : Subgroup G)
    [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (E : BinaryField) (d : OrthogonalMarking E P (f.Li 1 ⊔ I : Subgroup G))

include d in
/-- Construct both source field complements from the independent markings.
The only remaining section inputs are the literal radical incidence and order;
no field-stability, compatible-scalar or invariant-subspace datum is assumed. -/
theorem exists_compatible_complements_of_radical_geometry
    (hcard : Nat.card E.Carrier = 2 ^ S.field.degree)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I)
    {X : Subgroup G} (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I)
    (hTL : (T : Subgroup G) ≤ L)
    (v : V)
    (hinc : ∀ p : P, (p : G) ∈ f.Ri 0 ↔ ⁅(v : G), (p : G)⁆ ∈ f.Vi 0)
    (hsize : Nat.card (P ⊓ f.Ri 0 : Subgroup G) = (2 ^ S.field.degree) ^ 3) :
    let := originalModule D (.sl3 m) hfixed
    ∃ mP : Module S.field.Carrier (Additive P),
      let := mP
      ∃ ρ : Representation S.field.Carrier (f.Li 1 ⊔ I : Subgroup G) (Additive P),
      ∃ U : Submodule S.field.Carrier (Additive P),
      ∃ B : Submodule S.field.Carrier (Additive P),
      ∃ W₁ : Submodule S.field.Carrier (Additive V),
      ∃ W₂ : Submodule S.field.Carrier (Additive P),
        (∀ (y : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P),
          ((ρ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G)) ∧
        (∀ (a : S.field.Carrier) (b : Additive (P ⊓ V : Subgroup G)),
          ((a • (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
          ((a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G)) ∧
        ambientSubgroup U = f.Vi 1 ∧
        U.toAddSubgroup.toSubgroup = (f.Vi 1).subgroupOf P ∧
        Module.finrank S.field.Carrier U = 2 ∧
        Module.finrank S.field.Carrier ((Additive P) ⧸ U) = 2 ∧
        U ≤ B ∧
        ambientSubgroup B = P ⊓ f.Ri 0 ∧ Module.finrank S.field.Carrier B = 3 ∧
        P ⊓ f.Ri 0 < P ∧ X ≤ normalizer (ambientSubgroup B : Set G) ∧
        IsCompl (originalPlane D (.sl3 m) hfixed f) W₁ ∧ IsCompl B W₂ ∧
        Module.finrank S.field.Carrier W₁ = 1 ∧ Module.finrank S.field.Carrier W₂ = 1 ∧
        Disjoint (f.Vi 1) (ambientSubgroup W₁) ∧ f.Vi 1 ⊔ ambientSubgroup W₁ = V ∧
        Disjoint (P ⊓ f.Ri 0) (ambientSubgroup W₂) ∧
        (P ⊓ f.Ri 0) ⊔ ambientSubgroup W₂ = P ∧
        X ≤ normalizer (ambientSubgroup W₁ : Set G) ∧
        X ≤ normalizer (ambientSubgroup W₂ : Set G) ∧
        X ≤ normalizer ((⁅ambientSubgroup W₁, ambientSubgroup W₂⁆ : Subgroup G) : Set G) := by
  let := originalModule D (.sl3 m) hfixed
  obtain ⟨mP,hcompat,ρ,hρ⟩ := exists_compatible_fields D S m f P I hfixed E d
    hcard hP hcore hPV hVI
  let := mP
  have hcommon (a : S.field.Carrier) (b : Additive (P ⊓ V : Subgroup G)) :
      ((a • (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
        ((a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G) :=
    hcompat a ⟨b.toMul,hPV ▸ b.toMul.property⟩
  have hv : (v : G) ∈ f.Li 1 ⊔ I := (hVI.trans le_sup_right) v.property
  let B := radicalHyperplane D S m f P I hfixed hcommon ρ v hv
  have hB : ambientSubgroup B = P ⊓ f.Ri 0 :=
    ambient_radicalHyperplane D S m f P I hfixed hcommon ρ hρ v hv hinc
  have hdimB : Module.finrank S.field.Carrier B = 3 := by
    apply finrank_of_ambient_card B 3
    · rw [S.field.card_eq]
      exact Nat.one_lt_pow (Nat.ne_of_gt S.field.degree_pos) (by decide)
    · rw [hB,S.field.card_eq]
      exact hsize
  let ρX := ρ.comp (inclusion hXY)
  have hρX (x : X) (p : Additive P) :
      ((ρX x p).toMul : G) = MulAut.conj (x : G) (p.toMul : G) :=
    hρ (inclusion hXY x) p
  have hXB : X ≤ normalizer (ambientSubgroup B : Set G) := by
    rw [hB]
    exact (le_inf (hXY.trans d.normalizes) (cartan_normalizes_radical D S m f hX hTL 0)).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨W₁,W₂,h₁,h₂,hd₁,hs₁,hd₂,hs₂,hn₁,hn₂,hn₃⟩ :=
    exists_source_complements D S f P X hX
      (cartanRepresentation D (.sl3 m) hfixed hX) ρX
      (cartanRepresentation_conj D (.sl3 m) hfixed hX) hρX
      (originalPlane D (.sl3 m) hfixed f) B (ambient_originalPlane D (.sl3 m) hfixed f)
      hB (originalPlane_invariant D hfixed S m f hX) (invariant_of_normalizes B ρX hρX hXB)
  let U := SeparatePlaneActions.fixedPlane (V := V) ρ
  obtain ⟨hU,hdenom,hdimU,hdimQ⟩ := common_plane_sections D S m f P I ρ hρ
    hP hcore hPV hVI (d.finrank_of_same_field S.field (hcard.trans S.field.card_eq.symm))
  have hUB : U ≤ B := by
    intro p hp
    apply (mem_ambientSubgroup B _).mp
    rw [hB]
    have hu := (mem_ambientSubgroup U _).mpr hp
    rw [hU] at hu
    exact ⟨p.toMul.property, f.seed_le_Ri S 0 (D.centralQuotientPreimage_le _ hu)⟩
  have hproper : P ⊓ f.Ri 0 < P := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hq : 1 < 2 ^ S.field.degree :=
      Nat.one_lt_pow (Nat.ne_of_gt S.field.degree_pos) (by decide)
    have hs := hsize
    rw [he,d.card,hcard] at hs
    have hn := Nat.pow_right_injective hq hs
    omega
  have hdim₂ : Module.finrank S.field.Carrier W₂ = 1 := by
    have h := Submodule.finrank_add_eq_of_isCompl h₂
    rw [hdimB,d.finrank_of_same_field S.field (hcard.trans S.field.card_eq.symm)] at h
    omega
  exact ⟨mP,ρ,U,B,W₁,W₂,hρ,hcommon,hU,hdenom,hdimU,hdimQ,hUB,hB,hdimB,hproper,hXB,h₁,h₂,
    original_complement_finrank D hfixed S m f W₁ h₁,hdim₂,hd₁,hs₁,hd₂,hs₂,hn₁,hn₂,hn₃⟩
end Assembly


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections
