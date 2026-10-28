module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.CoreField
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ScalarSubfield

/-!
# Coefficient fields and dimensions on the same source core

Inside the constructed commuting field of H R_i on the original Frattini
section, take the fixed field of binary Frobenius. Faithful Cartan action
supplies the unit-order divisibility needed to prove its cardinality.
Restricting the actual action to these scalars gives a linear irreducible
representation on the same section; its dimension follows from its order.
When the Cartan kernel has exactly the nonzero scalar order, its scalar
map is bijective, so every nonzero scalar is actual source conjugation.

The earlier remainder containment, irreducibility and numerical source
orders are explicit inputs. This constructs scalar structure, not the
natural/tensor model identification or compatible root labels. Their
source assembly remains with the unitary source owner; the structural
irreducible-action producers are in QuadrangleStructure.

Source: Fong--Seitz II (8B), printed p.201, and (8C), p.203.
CoefficientApplication retains the original Q.q and Frattini quotient maps.
-/

public noncomputable section
open Subgroup
open scoped MonoidAlgebra IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
variable (hV : simpleRemainder Q split i ≤ HexagonStructure.localKernel Q i)
variable [Representation.IsIrreducible (coreActorRepresentation Q split i hV)]

abbrev CoreCoefficientField (n : ℕ) := ScalarSubfield.field (CoreEnd Q split i hV) n

instance coreCoefficientModule (n : ℕ) :
    Module (CoreCoefficientField Q split i hV n) (coreActorRepresentation Q split i hV).asModule :=
  Module.compHom _ (CoreCoefficientField Q split i hV n).subtype

instance coreCoefficientModuleFinite (n : ℕ) :
    Module.Finite (CoreCoefficientField Q split i hV n) (coreActorRepresentation Q split i hV).asModule := by
  let : Finite (coreActorRepresentation Q split i hV).asModule :=
    Finite.of_injective _ (coreActorRepresentation Q split i hV).asModuleEquiv.injective
  exact Module.Finite.of_finite

@[expose] def coreCoefficientRepresentation (n : ℕ) :
    Representation (CoreCoefficientField Q split i hV n) (coreActor Q split i)
      (coreActorRepresentation Q split i hV).asModule where
  toFun g :=
    { toFun := Representation.endFieldRep (coreActorRepresentation Q split i hV) g
      map_add' := map_add _
      map_smul' a v :=
        (Representation.endFieldRep (coreActorRepresentation Q split i hV) g).map_smul
          (a : CoreEnd Q split i hV) v }
  map_one' := by ext v; exact LinearMap.congr_fun (map_one
    (Representation.endFieldRep (coreActorRepresentation Q split i hV))) v
  map_mul' g h := by ext v; exact LinearMap.congr_fun (map_mul
    (Representation.endFieldRep (coreActorRepresentation Q split i hV)) g h) v

@[simp] theorem coreCoefficientRepresentation_apply (n : ℕ)
    (g : coreActor Q split i) (v : (coreActorRepresentation Q split i hV).asModule) :
    (coreActorRepresentation Q split i hV).asModuleEquiv
      (coreCoefficientRepresentation Q split i hV n g v) =
        coreActorRepresentation Q split i hV g
          ((coreActorRepresentation Q split i hV).asModuleEquiv v) := rfl

theorem coreCoefficientField_card (n : ℕ) (hn : 0 < n)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i}))
    (hd : 2 ^ n - 1 ∣ Nat.card (coreCartan Q i)) :
    Nat.card (CoreCoefficientField Q split i hV n) = 2 ^ n :=
  ScalarSubfield.card_eq _ n hn (hd.trans (coreCartan_card_dvd_field_sub_one Q split i hV hc))

theorem coreCoefficient_finrank (n d : ℕ) (hn : 0 < n)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i}))
    (hd : 2 ^ n - 1 ∣ Nat.card (coreCartan Q i))
    (hcard : Nat.card (CoreSpace Q split i) = (2 ^ n) ^ d) :
    Module.finrank (CoreCoefficientField Q split i hV n)
      (coreActorRepresentation Q split i hV).asModule = d := by
  have he := Module.natCard_eq_pow_finrank
    (K := CoreCoefficientField Q split i hV n)
    (V := (coreActorRepresentation Q split i hV).asModule)
  rw [Nat.card_congr (coreActorRepresentation Q split i hV).asModuleEquiv.toEquiv,
    hcard, coreCoefficientField_card Q split i hV n hn hc hd] at he
  have hq : 1 < (2 : ℕ) ^ n := one_lt_pow₀ (by decide) hn.ne'
  exact Nat.pow_right_injective hq he.symm

@[expose] def coreCoefficientUnits (n : ℕ)
    (hcard : Nat.card (coreCartan Q i) = 2 ^ n - 1) :
    coreCartan Q i →* (CoreCoefficientField Q split i hV n)ˣ :=
  (ScalarSubfield.actorMap _ n hcard (coreScalar Q split i hV)).toHomUnits

theorem coreCoefficientUnits_bijective (n : ℕ) (hn : 0 < n)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i}))
    (hcard : Nat.card (coreCartan Q i) = 2 ^ n - 1) :
    Function.Bijective (coreCoefficientUnits Q split i hV n hcard) :=
  ScalarSubfield.actorMap_bijective _ n hn hcard (coreScalar Q split i hV)
    (coreScalar_injective Q split i hV hc)

@[simp] theorem coreCoefficientUnits_smul (n : ℕ)
    (hcard : Nat.card (coreCartan Q i) = 2 ^ n - 1)
    (h : coreCartan Q i) (v : (coreActorRepresentation Q split i hV).asModule) :
    (coreActorRepresentation Q split i hV).asModuleEquiv
      ((coreCoefficientUnits Q split i hV n hcard h : CoreCoefficientField Q split i hV n) • v) =
      coreFrattiniRepresentation Q split i h
        ((coreActorRepresentation Q split i hV).asModuleEquiv v) := rfl

theorem coreCoefficient_nonzero_scalar (n : ℕ) (hn : 0 < n)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i}))
    (hcard : Nat.card (coreCartan Q i) = 2 ^ n - 1)
    (a : CoreCoefficientField Q split i hV n) (ha : a ≠ 0) :
    ∃ h : coreCartan Q i, ∀ v : (coreActorRepresentation Q split i hV).asModule,
      (coreActorRepresentation Q split i hV).asModuleEquiv (a • v) =
        coreFrattiniRepresentation Q split i h
          ((coreActorRepresentation Q split i hV).asModuleEquiv v) := by
  obtain ⟨h,hh⟩ := (coreCoefficientUnits_bijective Q split i hV n hn hc hcard).surjective
    (Units.mk0 a ha)
  refine ⟨h,fun v => ?_⟩
  have he := coreCoefficientUnits_smul Q split i hV n hcard h v
  rw [hh] at he
  exact he

theorem coreCoefficientRepresentation_irreducible (n : ℕ) :
    (coreCoefficientRepresentation Q split i hV n).IsIrreducible := by
  let ρ := coreActorRepresentation Q split i hV
  let : ρ.IsIrreducible := inferInstanceAs
    (Representation.IsIrreducible (coreActorRepresentation Q split i hV))
  let : Nontrivial (CoreSpace Q split i) :=
    Subrepresentation.irreducible_module_nontrivial (coreActorRepresentation Q split i hV)
  let : Nontrivial ρ.asModule := ρ.asModuleEquiv.toEquiv.nontrivial
  refine { toNontrivial := inferInstance, eq_bot_or_eq_top := ?_ }
  intro r
  let r' : Subrepresentation ρ :=
    { toSubmodule := AddSubgroup.toZModSubmodule 2
        (r.toSubmodule.toAddSubgroup.map ρ.asModuleEquiv.toAddEquiv.toAddMonoidHom)
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨w,hw,rfl⟩ := hv
        exact ⟨coreCoefficientRepresentation Q split i hV n g w,
          r.apply_mem_toSubmodule g hw,
          coreCoefficientRepresentation_apply Q split i hV n g w⟩ }
  rcases eq_bot_or_eq_top r' with hr | hr
  · left
    apply le_antisymm _ bot_le
    intro v hv
    have he : ρ.asModuleEquiv v ∈ r' := ⟨v,hv,rfl⟩
    rw [hr] at he
    change ρ.asModuleEquiv v = 0 at he
    exact ρ.asModuleEquiv.map_eq_zero_iff.mp he
  · right
    apply top_unique
    intro v _
    have he : ρ.asModuleEquiv v ∈ r' := hr ▸ Submodule.mem_top
    obtain ⟨w,hw,he⟩ := he
    have hwe : w = v := ρ.asModuleEquiv.injective he
    exact hwe ▸ hw

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
