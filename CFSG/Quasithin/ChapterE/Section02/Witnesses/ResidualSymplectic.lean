module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualCentralImage
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.InnerCore
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.InnerAction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Nonsolvable E.2.17 excludes the nonbinary symplectic row

Residual centralization forces a nontrivial center in the literal maximal
quotient. For a nonbinary symplectic normal component, the marked Borel
intersection has no center: a central element induces an automorphism fixing
the Borel pointwise, and the intrinsic Sp4 torus-fixer theorem makes that
automorphism trivial. Core-freeness then makes the original quotient centerless.
The final theorem retains the actual selected Sylow, maximal core, component,
and residual map.

Source: Aschbacher--Smith E.2.17, printed p.230, using the E.2.2 Sp4
Borel placement and the E.6.8 pointwise Borel calculation.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms
open ChapterB
variable {H : Type*} [Group H] [Finite H]

theorem coreFree_symplectic_max_center_eq_bot
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup H) [L.Normal] [IsSimpleGroup L] (e : L ≃* Sp F)
    (hgen : L ⊔ (T : Subgroup H) = ⊤) :
    center (minimalParabolicMax T hP) = ⊥ := by
  obtain ⟨g,hmark,_,hB⟩ := Structure.SymplecticFour.source_diagram_and_borel hF hn T hP L e hgen
  let e' := (e.trans (MulAut.conj g)).symm
  let f := L.subtype.comp e'.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e'.injective
  have hC := Structure.SymplecticFour.source_centralizer hF hn T hP hJ L e' hgen
  apply le_bot_iff.mp
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  apply extensionAction_injective L e' hC
  rw [show (↑(1 : minimalParabolicMax T hP) : H) = 1 by rfl, map_one]
  apply Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.aut_fixing_borel_eq_one hF hn
    SemilinearClassification.inner_field_of_preservesDiagram
  intro x hx
  apply hf
  change f (extensionAction L e' v.val x) = f x
  rw [show f (extensionAction L e' v.val x) = v.val * f x * v.val⁻¹ from
    extensionAction_apply L e' v.val x]
  have hxM : f x ∈ minimalParabolicMax T hP := hB.ge hx
  have hc : v.val * f x = f x * v.val :=
    (congrArg Subtype.val (mem_center_iff.mp hv ⟨f x,hxM⟩)).symm
  rw [hc,mul_inv_cancel_right]

theorem source_not_nonbinary_symplectic_of_residual_centralizes
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (minimalParabolicCore T hP))) 2 (2^n))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬V ≤ minimalParabolicCore T hP)
    (hres : (pResidual 2 (minimalParabolicMax T hP)).map
      (minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : False := by
  let J := minimalParabolicCore T hP
  let M := minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map q
  obtain ⟨hLs,_,hLn,hLT⟩ := Structure.source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L := hLs
  let : L.Normal := hLn
  have hmin : IsMinimalParabolicOver S ⊤ := (Structure.source_star_minimal_core_free T hP).1
  have hcore : minimalParabolicCore S hmin = ⊥ := (Structure.source_star_minimal_core_free T hP).2
  have hmax : minimalParabolicMax S hmin = M.map q :=
    (minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hcard
  have hc := coreFree_symplectic_max_center_eq_bot hcard hn S hmin hcore L
    (e.trans EvenProjective.equiv.symm) hLT
  rw [hmax] at hc
  exact source_star_maximal_center_ne_bot T hP V hVT hvn hout hres hc
end CFSG.Quasithin.ChapterE.Witnesses
