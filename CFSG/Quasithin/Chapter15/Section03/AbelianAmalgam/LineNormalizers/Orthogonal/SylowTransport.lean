module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.FullAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalNormalizer
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.FixedLine

/-!
# Transport of the singular-line Sylow subgroup

The compatible quadratic action restricts to a surjection from the ambient
relative line normalizer onto the actual coordinate line stabilizer. It sends
the chosen Sylow subgroup to the selected finite Sylow intersection. Fixing
the coordinate line pointwise is equivalent to ambient centralization. The
finite fixed-vector and displacement calculations then give `C_V(T) ≤ E`
and the ambient identity `[V,C_T(E)] = E`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the selection
before 15.3.66 and its use in 15.3.67, printed pp.1152--1153.
-/

@[expose] public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
variable {G : Type*} [Group G] {M V : Subgroup G}

/-- Pointwise fixation in the given coordinates is ambient centralization. -/
theorem coordinateLine_pointwise_iff (d : NaturalAction V M) (E : Subgroup G)
    (hEV : E ≤ V) (m : M) :
    (∀ w ∈ coordinateLine d E, vectorAction (d.action m) w = w) ↔
      (m : G) ∈ centralizer (E : Set G) := by
  constructor
  · intro h
    apply mem_centralizer_iff.mpr
    intro e he
    have hw : d.coordinates ⟨e, hEV he⟩ ∈ coordinateLine d E :=
      (mem_coordinateLine d E _).mpr (by simpa using he)
    have hh := d.intertwines m ⟨e,hEV he⟩
    change (d.coordinates.symm (vectorAction (d.action m)
      (d.coordinates ⟨e,hEV he⟩)) : G) = (m : G) * e * (m : G)⁻¹ at hh
    rw [h _ hw, d.coordinates.symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro h w hw
    apply d.coordinates.symm.injective
    apply Subtype.ext
    have hh := d.intertwines m (d.coordinates.symm w)
    rw [d.coordinates.apply_symm_apply] at hh
    exact hh.trans (mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp h _ ((mem_coordinateLine d E w).mp hw)).symm)

/-- The ambient Sylow selection descends to the actual coordinate line stabilizer. -/
theorem coordinateLine_sylow [Finite G] (d : NaturalAction V M)
    (T : Sylow 2 G) (E : Subgroup G) (hEV : E ≤ V)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype =
      lineT (T : Subgroup G) E) :
    ∃ Q : Sylow 2 (lineStabilizer (coordinateLine d E)),
      (Q : Subgroup (lineStabilizer (coordinateLine d E))).map
        (lineStabilizer (coordinateLine d E)).subtype =
      actionImage d (T : Subgroup G) ⊓ lineStabilizer (coordinateLine d E) := by
  let f : lineM M E →* lineStabilizer (coordinateLine d E) :=
    (d.action.comp (inclusion (show lineM M E ≤ M from inf_le_left))).codRestrict
      (lineStabilizer (coordinateLine d E)) (fun m =>
        (coordinateLine_stabilizer_iff d E hEV (inclusion inf_le_left m)).mpr m.property.2)
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨m,hm⟩ := d.onto g.val
    have hmE : (m : G) ∈ lineNormalizer E :=
      (coordinateLine_stabilizer_iff d E hEV m).mp (hm.symm ▸ g.property)
    exact ⟨⟨m, m.property, hmE⟩, Subtype.ext hm⟩
  refine ⟨P.mapSurjective hf, ?_⟩
  rw [← actionImage_lineNormalizer d (T : Subgroup G) E hEV]
  change ((P : Subgroup (lineM M E)).map f).map _ = actionImage d (lineT (T : Subgroup G) E)
  ext g
  constructor
  · rintro ⟨s, ⟨p,hp,rfl⟩,rfl⟩
    have hpT : (p : G) ∈ lineT (T : Subgroup G) E := by
      rw [← hP]
      exact mem_map_of_mem _ hp
    exact mem_map.mpr ⟨inclusion inf_le_left p, hpT, rfl⟩
  · rintro ⟨m,hm,rfl⟩
    have hmT : (m : G) ∈ lineT (T : Subgroup G) E := hm
    rw [← hP] at hmT
    obtain ⟨p,hp,hpm⟩ := hmT
    refine mem_map.mpr ⟨f p, mem_map_of_mem f hp, ?_⟩
    change d.action (inclusion inf_le_left p) = d.action m
    exact congrArg d.action (Subtype.ext hpm)

variable [Finite G]

/-- The selected singular line contains the fixed subgroup `C_V(T)`. -/
theorem fixedSubgroup_le_singularLine (d : NaturalAction V M)
    (T : Sylow 2 G) (E : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype =
      lineT (T : Subgroup G) E) :
    V ⊓ centralizer (T : Set G) ≤ E := by
  obtain ⟨S,hS⟩ := actionImage_sylow d T hTM
  obtain ⟨Q,hQ⟩ := coordinateLine_sylow d T E hEV P hP
  rw [← hS] at hQ
  rintro z ⟨hzV,hzc⟩
  have hz := OrthogonalFourBinary.SylowGeometry.line_sylow_fixed_mem S
    (coordinateLine d E) ((coordinateLine_card d E hEV).trans hcard)
    (coordinateLine_singular d E hEV hs) Q hQ (d.coordinates ⟨z,hzV⟩) (by
      intro g hg
      rw [hS] at hg
      obtain ⟨m,hm,rfl⟩ := hg
      apply d.coordinates.symm.injective
      apply Subtype.ext
      have hh := d.intertwines m ⟨z,hzV⟩
      change (d.coordinates.symm (vectorAction (d.action m) (d.coordinates ⟨z,hzV⟩)) : G) =
        (m : G) * z * (m : G)⁻¹ at hh
      rw [d.coordinates.symm_apply_apply]
      exact hh.trans (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hzc m hm)))
  simpa only [d.coordinates.symm_apply_apply] using (mem_coordinateLine d E _).mp hz

/-- The identity `[V,C_T(E)] = E` used in the proof of source 15.3.67. -/
theorem singularLine_commutator_centralizer (d : NaturalAction V M)
    (T : Sylow 2 G) (E : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype =
      lineT (T : Subgroup G) E) :
    ⁅V, (T : Subgroup G) ⊓ centralizer (E : Set G)⁆ = E := by
  rw [commutator_comm]
  apply le_antisymm
  · apply commutator_le.mpr
    rintro m ⟨hmT,hmC⟩ v hv
    let m' : M := ⟨m,hTM hmT⟩
    have hd := OrthogonalFourBinary.SylowGeometry.line_pointwise_displacement_mem
      (coordinateLine d E) ((coordinateLine_card d E hEV).trans hcard)
      (coordinateLine_singular d E hEV hs) (d.action m')
      ((coordinateLine_pointwise_iff d E hEV m').mpr hmC) (d.coordinates ⟨v,hv⟩)
    have hh := (mem_coordinateLine d E _).mp hd
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      d.coordinates.symm_apply_apply] at hh
    have hc := d.intertwines m' ⟨v,hv⟩
    change (d.coordinates.symm (vectorAction (d.action m') (d.coordinates ⟨v,hv⟩)) : G) =
      m * v * m⁻¹ at hc
    rw [hc] at hh
    exact hh
  · obtain ⟨S,hS⟩ := actionImage_sylow d T hTM
    obtain ⟨Q,hQ⟩ := coordinateLine_sylow d T E hEV P hP
    rw [← hS] at hQ
    obtain ⟨g,hg,hfix,hmove⟩ :=
      OrthogonalFourBinary.SylowGeometry.line_sylow_displacement_surjective S
        (coordinateLine d E) ((coordinateLine_card d E hEV).trans hcard)
        (coordinateLine_singular d E hEV hs) Q hQ
    rw [hS] at hg
    obtain ⟨m,hm,rfl⟩ := hg
    have hmC := (coordinateLine_pointwise_iff d E hEV m).mp hfix
    intro e he
    have hec : d.coordinates ⟨e,hEV he⟩ ∈ coordinateLine d E :=
      (mem_coordinateLine d E _).mpr (by simpa using he)
    obtain ⟨w,hw⟩ := hmove _ hec
    let a := d.coordinates.symm w
    have hconj := d.intertwines m a
    rw [d.coordinates.apply_symm_apply] at hconj
    have heq := congrArg (fun u => (d.coordinates.symm u : G)) hw
    rw [map_mul, map_inv, d.coordinates.symm_apply_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at heq
    change (d.coordinates.symm (vectorAction (d.action m) w) : G) * (a : G)⁻¹ = e at heq
    change (d.coordinates.symm (vectorAction (d.action m) w) : G) =
      (m : G) * (a : G) * (m : G)⁻¹ at hconj
    rw [hconj] at heq
    have hecomm : e = ⁅(m : G),(a : G)⁆ := heq.symm
    rw [hecomm]
    exact commutator_mem_commutator ⟨hm,hmC⟩ a.property



end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
