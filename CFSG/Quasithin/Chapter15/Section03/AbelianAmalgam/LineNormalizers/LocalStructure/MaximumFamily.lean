module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.SylowTransport
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.StrictFixedBound
public import Stellmacher.MaxElementaryOffender
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The maximum elementary family of the selected line normalizer

Every maximum elementary abelian subgroup of `T_E` centralizes `V`.
We transport its actual maximum family to the relative ambient group `M`,
where the compatible natural action makes `V` normal. The elementary
replacement inequality there gives `16 ≤ |C_V(A)| |image(A)|`. Coordinates
inject the centralizer into the fixed vectors of the image, whereas the
selected singular-line Sylow geometry gives a strict upper bound of sixteen
for each nontrivial image. Thus the image is trivial.

The selected Sylow subgroup of `M_E` is retained explicitly. Neither a
comparison with the maximum rank of `T` nor an ambient centralizer containment
is needed. This supplies the family premise of
`BaumannAssembly.line_control_of_maximum_family`; the subsequent control and
Sylow promotion remain with that assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.67,
first paragraph of the proof, printed p.1153. The natural orthogonal action
is 15.3.2(1), pp.1121–1122, and the Sylow selection is on p.1152.
-/

public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open OrthogonalFourBinary.SylowGeometry Stellmacher
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

private theorem maximum_image_bound (d : NaturalAction V M)
    [IsElementaryAbelian 2 V] (S A : Subgroup G) (hSM : S ≤ M) (hVS : V ≤ S)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    16 ≤ Nat.card (FixedVectors (actionImage d A)) * Nat.card (actionImage d A) := by
  have hVM : V ≤ M := hVS.trans hSM
  have hAM : A ≤ M := hA.1.trans hSM
  let W := V.subgroupOf M
  let A' := A.subgroupOf M
  let S' := S.subgroupOf M
  let : W.Normal := (normal_subgroupOf_iff_le_normalizer hVM).mpr d.normalizes
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVM
  have hA' : A' ∈ elementaryAbelianMaxSubgroups S' := by
    apply (maxFamily_map_injective_iff M.subtype M.subtype_injective S' A').mp
    change (A.subgroupOf M).map M.subtype ∈
      elementaryAbelianMaxSubgroups ((S.subgroupOf M).map M.subtype)
    rwa [map_subgroupOf_eq_of_le hAM, map_subgroupOf_eq_of_le hSM]
  have hker : d.action.ker = centralizer (W : Set M) := by
    rw [action_ker d]
    ext m
    change (m : G) ∈ centralizer (V : Set G) ↔ m ∈ centralizer (W : Set M)
    constructor
    · intro h
      apply mem_centralizer_iff.mpr
      intro v hv
      exact Subtype.ext (mem_centralizer_iff.mp h v hv)
    · intro h
      apply mem_centralizer_iff.mpr
      intro v hv
      exact congrArg Subtype.val (mem_centralizer_iff.mp h (⟨v,hVM hv⟩ : M) hv)
  have hb := maxElementary_card_le_fixed_mul_image S' W A'
    (subgroupOf_mono M hVS) hA' d.action hker
  have hW : Nat.card W = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv,
      Nat.card_congr d.coordinates.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hfixed : Nat.card (W ⊓ centralizer (A' : Set M) : Subgroup M) ≤
      Nat.card (FixedVectors (actionImage d A)) := by
    let f : (W ⊓ centralizer (A' : Set M) : Subgroup M) →
        FixedVectors (actionImage d A) := fun v =>
      ⟨(d.coordinates ⟨(v.val : G),v.property.1⟩).toAdd, by
        intro g hg
        obtain ⟨a,ha,rfl⟩ := hg
        change vectorAction (d.action a) (d.coordinates ⟨(v.val : G),v.property.1⟩) =
          d.coordinates ⟨(v.val : G),v.property.1⟩
        apply d.coordinates.symm.injective
        apply Subtype.ext
        rw [d.coordinates.symm_apply_apply]
        have hh := d.intertwines a ⟨(v.val : G),v.property.1⟩
        change (d.coordinates.symm (vectorAction (d.action a)
          (d.coordinates ⟨(v.val : G),v.property.1⟩)) : G) =
          (a : G) * (v.val : G) * (a : G)⁻¹ at hh
        apply hh.trans
        apply mul_inv_eq_iff_eq_mul.mpr
        exact congrArg Subtype.val (mem_centralizer_iff.mp v.property.2 a ha)⟩
    apply Nat.card_le_card_of_injective f
    intro v w h
    have hc : d.coordinates ⟨(v.val : G),v.property.1⟩ =
        d.coordinates ⟨(w.val : G),w.property.1⟩ :=
      congrArg (fun u : FixedVectors (actionImage d A) => u.val) h
    exact Subtype.ext (Subtype.ext
      (congrArg (fun u : V => (u : G)) (d.coordinates.injective hc)))
  rw [hW] at hb
  exact hb.trans (Nat.mul_le_mul_right _ hfixed)

/-- Every maximum elementary abelian subgroup of the selected `T_E` centralizes `V`.
The maximum family is taken in `T_E` itself, and `P` retains the source Sylow choice
inside `M_E`. -/
theorem lineT_maximum_family_centralizes (d : NaturalAction V M)
    [IsElementaryAbelian 2 V] (T : Sylow 2 G) (E : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hVT : V ≤ (T : Subgroup G))
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E) :
    ∀ A ∈ elementaryAbelianMaxSubgroups (lineT (T : Subgroup G) E),
      A ≤ centralizer (V : Set G) := by
  have hVV : V ≤ centralizer (V : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hVD : V ≤ lineT T E :=
    le_inf hVT (hVV.trans ((centralizer_le hEV).trans (Subgroup.centralizer_le_normalizer _)))
  obtain ⟨S,hS⟩ := actionImage_sylow d T hTM
  obtain ⟨Q,hQ⟩ := Orthogonal.coordinateLine_sylow d T E hEV P hP
  rw [← hS] at hQ
  intro A hA
  have hAM : A ≤ M := hA.1.trans (inf_le_left.trans hTM)
  have himage : actionImage d A = ⊥ := by
    by_contra hn
    have hl : actionImage d A ≤ (S : Subgroup Actor) ⊓ lineStabilizer (coordinateLine d E) := by
      rw [hS, ← actionImage_lineNormalizer d (T : Subgroup G) E hEV]
      exact map_mono (subgroupOf_mono M hA.1)
    have hlt := line_sylow_strict_fixed_bound S (coordinateLine d E)
      ((coordinateLine_card d E hEV).trans hcard) (coordinateLine_singular d E hEV hs)
      Q hQ (actionImage d A) hl hn
    have hge := maximum_image_bound d (lineT T E) A (inf_le_left.trans hTM) hVD hA
    exact (Nat.not_lt_of_ge hge) hlt
  have hker : A.subgroupOf M ≤ d.action.ker := (Subgroup.map_eq_bot_iff (A.subgroupOf M)).mp himage
  rw [action_ker d] at hker
  intro a ha
  exact hker (show (⟨a,hAM ha⟩ : M) ∈ A.subgroupOf M from ha)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
