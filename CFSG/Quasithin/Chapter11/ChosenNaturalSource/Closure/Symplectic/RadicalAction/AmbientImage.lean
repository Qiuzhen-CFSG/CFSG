module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.Branches
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExtensionCores
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.Representation.SymplecticNaturalNormalizer.RootHyperplaneImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus

/-!
# The original ambient comparisons in the symplectic radical branch

This file isolates the three comparisons used by the opening paragraph of
Aschbacher--Smith 11.5.7.  The first is the two-core transport through the
actual normalizer action.  The second keeps the natural-normalizer argument
on the literal action image: its only source input is that an actor fixing the
marked hyperplane is inner in the marked symplectic component, together with
the compatible hyperplane coordinates.  The third is the quotient-map
calculation for the preceding Cartan geometry.

No conclusion about `U`, about `O₂(L)`, or about the radical action is used.
The normal-extension, diagram-preservation, and centralizer requirements for
the native core theorem are explicit in `CoreExtensionData`; in particular,
we do not silently impose centricity on a full natural normalizer.

Source: Aschbacher--Smith 11.5.7, printed pp.782--783.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.AmbientImage

open Subgroup
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)

/-! ### The `R₁` image -/

/- The extension theorem is stated for a faithful normal copy of the marked
symplectic group.  The equality `hR` is the source's literal identification
of the action of `R₁` with the core of the adjoining normalizer actor.  It is
the exact point at which the source normal-extension producer enters; the
theorem below then performs the core comparison and the transport to the
original `actionImage`. -/
structure CoreExtensionData (F : Type*) [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] where
  N : Subgroup (MulAut V)
  normal : N.Normal
  e : Sp F ≃* N
  hcent : centralizer (N : Set (MulAut V)) = ⊥
  hdiagram : ∀ a : MulAut V,
    PreservesDiagram (extensionAction N e a)
  S : Subgroup (MulAut V)
  hnorm : S ≤ normalizer
    ((pointLocal (F := F)).map (N.subtype.comp e.toMonoidHom) : Set (MulAut V))
  hlocal : (pointLocal (F := F)).map (N.subtype.comp e.toMonoidHom) =
    actionImage (V := V) E.L₁
  hR : actionImage (V := V) E.R₁ =
    (pCore 2
      (((pointLocal (F := F)).map (N.subtype.comp e.toMonoidHom) ⊔ S) :
        Subgroup (MulAut V))).map
      (((pointLocal (F := F)).map (N.subtype.comp e.toMonoidHom) ⊔ S) :
        Subgroup (MulAut V)).subtype

include m
theorem actionImage_R₁_le_local_core
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (c : CoreExtensionData (E := E) F) :
    actionImage (V := V) E.R₁ ≤
      actionImage (V := V) (E.L₁.pCoreIn 2) := by
  let _ : c.N.Normal := c.normal
  have hcore := pointLocal_join_core_eq c.N c.e hcard hn c.hcent c.hdiagram c.S c.hnorm
  rw [c.hR, hcore, c.hlocal]
  exact (FullAction.core_image m E.L₁ E.L₁_le).ge

/-! ### The full hyperplane fixer -/

/- The source's natural-normalizer calculation is deliberately separated from
the transport below.  `hinner` is the result of applying the fixed-field-line
argument to the actual actor (and is where the precise centralizer hypothesis
for the component must be supplied).  `hhyper` is the compatible symplectic
flag coordinate: it identifies fixation of the literal `V₃` with fixation of
the transported natural hyperplane. -/
theorem ambient_fixer_bound_of_inner
    (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ =
      pointLocal.map (MulAut.conj g).toMonoidHom)
    (hinner : ∀ a : MulAut V,
      a ∈ actionImage (V := V) (E.M ⊓ normalizer (V : Set G)) →
      ∃ b : Sp E.input.field.Carrier, FullAction.modelHom m b = a)
    (hhyper : ∀ b : Sp E.input.field.Carrier,
      FullAction.modelHom m b ∈ fixingSubgroup (MulAut V)
          (E.V₃.subgroupOf V : Set V) ↔
        b ∈ fixingSubgroup (Sp E.input.field.Carrier)
          (((form E.input.field.Carrier).orthogonal
            (point E.input.field.Carrier)).map
            (toLinear g).toLinearMap : Set (Vector E.input.field.Carrier))) :
    actionImage (V := V) (E.M ⊓ normalizer (V : Set G)) ⊓
        fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) ≤
      (center (actionImage (V := V) E.L₁)).map
        (actionImage (V := V) E.L₁).subtype := by
  intro a ha
  obtain ⟨b, rfl⟩ := hinner a ha.1
  have hbfix : b ∈ fixingSubgroup (Sp E.input.field.Carrier)
      (((form E.input.field.Carrier).orthogonal
        (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap : Set (Vector E.input.field.Carrier)) :=
    (hhyper b).mp ha.2
  have hbcenter : b ∈
      (center (PointModel.image m E.L₁)).map
        (PointModel.image m E.L₁).subtype := by
    rw [← PointModel.hyperplane_fixer m g hlocal]
    exact hbfix
  have hmap := FullAction.center_image m
  have hbmap : FullAction.modelHom m b ∈
      ((center (actionImage (V := V) E.L₁)).map
        (actionImage (V := V) E.L₁).subtype) := by
    rw [← hmap]
    exact mem_map_of_mem (FullAction.modelHom m) hbcenter
  exact hbmap

/-! ### The Cartan image -/

theorem image_sup (A B : Subgroup G) (hA : A ≤ L) (hB : B ≤ L) :
    PointModel.image m (A ⊔ B) =
      PointModel.image m A ⊔ PointModel.image m B := by
  change ((A ⊔ B).subgroupOf L).map (PointModel.quotientMap m) =
    (A.subgroupOf L).map (PointModel.quotientMap m) ⊔
      (B.subgroupOf L).map (PointModel.quotientMap m)
  rw [subgroupOf_sup hA hB, Subgroup.map_sup]

/- The preceding source producer supplies the model image of the Cartan and
the compatible flag alignment supplies the model join identity.  The proof is
then only the literal quotient map and two subgroup-map identities. -/
theorem cartan_image_of_compatible_geometry
    (g : Sp E.input.field.Carrier)
    (hX : E.X ≤ L)
    (Q : Subgroup (Sp E.input.field.Carrier))
    (hcartan : PointModel.image m E.X =
      Q.map (MulAut.conj g).toMonoidHom)
    (hjoin : pointLocal (F := E.input.field.Carrier) ⊔ Q =
      pointParabolic (F := E.input.field.Carrier))
    (hlocal : PointModel.image m E.L₁ =
      pointLocal.map (MulAut.conj g).toMonoidHom) :
    PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom := by
  rw [image_sup m E.L₁ E.X E.L₁_le hX, hlocal, hcartan,
    ← Subgroup.map_sup, hjoin]

/-! ### Actual downstream application -/

include m
theorem local_fixer_bound_of_inner
    (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ =
      pointLocal.map (MulAut.conj g).toMonoidHom)
    (hinner : ∀ a : MulAut V,
      a ∈ actionImage (V := V) (E.M ⊓ normalizer (V : Set G)) →
      ∃ b : Sp E.input.field.Carrier, FullAction.modelHom m b = a)
    (hhyper : ∀ b : Sp E.input.field.Carrier,
      FullAction.modelHom m b ∈ fixingSubgroup (MulAut V)
          (E.V₃.subgroupOf V : Set V) ↔
        b ∈ fixingSubgroup (Sp E.input.field.Carrier)
          (((form E.input.field.Carrier).orthogonal
            (point E.input.field.Carrier)).map
            (toLinear g).toLinearMap : Set (Vector E.input.field.Carrier))) :
    actionImage (V := V) E.R₁ ⊓
        fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) ≤
      (center (actionImage (V := V) E.L₁)).map
        (actionImage (V := V) E.L₁).subtype := by
  exact RadicalAction.local_fixer_bound_of_ambient E
    (ambient_fixer_bound_of_inner m g hlocal hinner hhyper)

/- The three comparisons can now be fed directly to the source branch
   assembly.  The preceding Cartan and compatible-flag producers are kept as
   their literal hypotheses (`hcartanX` and `hjoin`); the local image is
   recovered from the marked flag by `local_identification`, and the radical
   image and fixer premises are discharged by the preceding theorems. -/
theorem initial_branch_of_preceding_and_ambient_comparisons
    (g : Sp E.input.field.Carrier)
    (Q : Subgroup (Sp E.input.field.Carrier))
    (hpoint : m.flag.space 0 =
      (point E.input.field.Carrier).map
        (toLinear g).toLinearMap)
    (hcartanX : PointModel.image m E.X =
      Q.map (MulAut.conj g).toMonoidHom)
    (hjoin : pointLocal (F := E.input.field.Carrier) ⊔ Q =
      pointParabolic (F := E.input.field.Carrier))
    (c : CoreExtensionData (E := E) E.input.field.Carrier)
    (hinner : ∀ a : MulAut V,
      a ∈ actionImage (V := V) (E.M ⊓ normalizer (V : Set G)) →
      ∃ b : Sp E.input.field.Carrier, FullAction.modelHom m b = a)
    (hhyper : ∀ b : Sp E.input.field.Carrier,
      FullAction.modelHom m b ∈ fixingSubgroup (MulAut V)
          (E.V₃.subgroupOf V : Set V) ↔
        b ∈ fixingSubgroup (Sp E.input.field.Carrier)
          (((form E.input.field.Carrier).orthogonal
            (point E.input.field.Carrier)).map
            (toLinear g).toLinearMap : Set (Vector E.input.field.Carrier)))
    (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) →
        A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M,
      V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hroot : ⁅E.V₃,FullAction.rootPreimage (E := E)⁆ = ⊥)
    (hmove : ⁅V,E.L₁.pCoreIn 2⁆ = E.V₃)
    (hrootmove : ⁅V,FullAction.rootPreimage (E := E)⁆ = E.V₁)
    (hne : ¬ IsMulCommutative E.W) :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 ∧ IsMulCommutative E.U ∧
    actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map
        (actionImage (V := V) E.L₁).subtype ∧
    ⁅V,auxiliaryW E⁆ = E.V₁ ∧ ⁅E.V₃,auxiliaryW E⁆ = ⊥ ∧
    (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁ ∧
    auxiliaryW E ≤ E.W ∧ auxiliaryW E ≤ E.G₁.pCoreIn 2 ∧
    E.G₁ ≤ normalizer (auxiliaryW E : Set G) := by
  have hlocal := PointModel.local_identification m g hpoint
  have hcartan := cartan_image_of_compatible_geometry m g hXL Q hcartanX hjoin hlocal
  have hR := actionImage_R₁_le_local_core m E.input.field.card_eq
    E.input.nonbinary c
  have hfix := ambient_fixer_bound_of_inner m g hlocal hinner hhyper
  exact initial_branch_of_preceding_and_action_comparisons E m g hcartan hXL hXG hR
    hpoint hn3 hirr hti hgen hVX hfour hfive hroot hmove hrootmove
    hfix hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.AmbientImage
