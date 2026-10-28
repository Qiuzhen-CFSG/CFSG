module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.Contracts
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# Source-compatible marking for the original quotient

The original quotient map `qL` is marked using the actual point fixed by the
central involution `d.z`.  Its stabilizer is the image of the original `H`,
while the image of the original Sylow subgroup is a Sylow subgroup inside that
stabilizer.  Sylow conjugacy first sends this image to the standard Borel.  The
proved flag duality then exchanges the point and line parabolics, preserving
the Borel, and its outer-action representation equivalence supplies the
required natural/dual identification.

This keeps the original `qL` fixed throughout.  In particular, it does not
assume a containment of `S` in `L`, a cyclic vector, or any recognition
conclusion.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076 (PDF p.1093),
and H.6.5, printed p.388 (PDF p.399), manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
open Chapter12.Section08 CriticalFusion.Source
open Matrix.PSL3Two
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem source_point_stabilizer :
    ∃ p : Fano.Point, (F.H.subgroupOf L).map d.qL = MulAction.stabilizer SL p := by
  have hzV : d.z ∈ V := F.le_seed 1 (by rw [d.point]; exact mem_zpowers d.z)
  let z : V := ⟨d.z, hzV⟩
  let v : BinaryLinearThree.Vector := (d.naturalCoordinates z).toAdd
  have hv : v ≠ 0 := by
    intro h
    have he : d.naturalCoordinates z = d.naturalCoordinates 1 := by
      rw [map_one]
      exact h
    exact d.z_ne_one (congrArg Subtype.val (d.naturalCoordinates_bijective.1 he))
  let p : Fano.Point := ⟨v, hv⟩
  have hmem (l : L) : d.qL l ∈ MulAction.stabilizer SL p ↔ l ∈ F.H.subgroupOf L := by
    change d.qL l • p = p ↔ (l : G) ∈ F.H
    rw [d.centralizer_eq, mem_centralizer_singleton_iff]
    have he := d.naturalCoordinates_equivariant l z
    constructor
    · intro h
      have hcoord :
          (d.naturalCoordinates ⟨(l : G) * d.z * (l : G)⁻¹,
            (mem_normalizer_iff.mp (d.natural.chosen.normalizes l.property) z).mp z.property⟩).toAdd =
            (d.naturalCoordinates z).toAdd :=
        he.trans (congrArg Subtype.val h)
      have hz' :
          (⟨(l : G) * d.z * (l : G)⁻¹,
            (mem_normalizer_iff.mp (d.natural.chosen.normalizes l.property) z).mp z.property⟩ : V) = z :=
        d.naturalCoordinates_bijective.1 (Multiplicative.toAdd.injective hcoord)
      have hc : (l : G) * d.z * (l : G)⁻¹ = d.z := congrArg Subtype.val hz'
      exact mul_inv_eq_iff_eq_mul.mp hc
    · intro h
      apply Subtype.ext
      change BinaryLinearThree.W (d.qL l) v = v
      rw [← he]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr h
  refine ⟨p, ?_⟩
  ext g
  obtain ⟨l, rfl⟩ := d.qL_surjective g
  constructor
  · rintro ⟨k, hk, he⟩
    rw [← he]
    exact (hmem k).mpr hk
  · intro h
    exact ⟨l, (hmem l).mp h, rfl⟩

private theorem borel_fixed_point (p : Fano.Point)
    (h : ∀ g ∈ borelSL, g • p = p) : p = Matrix.PSL3Two.flagPoint := by
  have hc : ∀ p : Fano.Point,
      Bruhat.upper 1 • p = p → Bruhat.upper 4 • p = p → p = Matrix.PSL3Two.flagPoint := by
    decide +kernel
  exact hc p (h _ (Bruhat.upper_mem 1)) (h _ (Bruhat.upper_mem 4))

private theorem inner_sylow_marking (P : Sylow 2 SL) :
    ∃ g : SL, (P : Subgroup SL).map (MulAut.conj g).toMonoidHom = borelSL := by
  let B : Sylow 2 SL := Sylow.ofCard borelSL (by
    rw [card_borelSL, card_SL]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL P B
  refine ⟨g, ?_⟩
  have he := congrArg (fun Q : Sylow 2 SL => (Q : Subgroup SL)) hg
  rw [Sylow.coe_subgroup_smul] at he
  exact he

private theorem flag_duality_outer : flagDuality ∉ MulAut.innerSubgroup SL := by
  have he : BinaryLinear.OuterCyclic.graphSL 3 = BinaryLinearThree.AutomorphismAction.graph := by
    ext g : 1
    apply Subtype.ext
    exact (Matrix.adjugate_transpose g.val).symm
  have hf : flagDuality = MulAut.conj (Bruhat.perm 5) *
      BinaryLinearThree.AutomorphismAction.graph := by
    rw [← he]
    rfl
  rw [hf]
  intro h
  exact BinaryLinearThree.AutomorphismAction.graph_not_inner
    ((MulAut.innerSubgroup SL).mul_mem_cancel_left (show MulAut.conj (Bruhat.perm 5) ∈
      MulAut.innerSubgroup SL from ⟨_, rfl⟩) |>.mp h)

/-- The original quotient admits the point/line and natural/dual compatible marking. -/
theorem nonempty_marking (hTL : (T : Subgroup G) ≤ normalizer L) : Nonempty (Marking d) := by
  obtain ⟨p, hp⟩ := source_point_stabilizer d
  obtain ⟨P, hP⟩ := d.source_sylow_image hTL
  have hmap : ((T : Subgroup G).subgroupOf L).map d.qL = (P : Subgroup SL) := by
    rw [← hP]
    ext g
    constructor
    · rintro ⟨l, hl, he⟩
      exact ⟨⟨l, hl, l.property⟩, he⟩
    · rintro ⟨l, he⟩
      exact ⟨⟨l, l.property.2⟩, l.property.1, he⟩
  have hPH : (P : Subgroup SL) ≤ MulAction.stabilizer SL p := by
    rw [← hp, ← hmap]
    exact map_mono (fun l hl => F.invariant 1 hl)
  obtain ⟨g, hg⟩ := inner_sylow_marking P
  have hp' : g • p = Matrix.PSL3Two.flagPoint := by
    apply borel_fixed_point
    intro a ha
    have ha' : a ∈ (MulAction.stabilizer SL p).map (MulAut.conj g).toMonoidHom :=
      map_mono hPH (hg.symm ▸ ha)
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj] at ha'
    exact ha'
  have hpar : ((F.H.subgroupOf L).map d.qL).map (MulAut.conj g).toMonoidHom =
      pointParabolicSL := by
    rw [hp, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hp', Fano.stabilizer_flagPoint_SL]
  let e : MulAut BinaryLinearThree.Group := (MulAut.conj g).trans flagDuality
  have he : e.symm ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
    intro h
    have hi : e ∈ MulAut.innerSubgroup SL := (MulAut.innerSubgroup SL).inv_mem h
    change flagDuality * MulAut.conj g ∈ MulAut.innerSubgroup SL at hi
    have hg' : MulAut.conj g ∈ MulAut.innerSubgroup SL := ⟨g, rfl⟩
    have hcancel : flagDuality * MulAut.conj g ∈ MulAut.innerSubgroup SL ↔
        flagDuality ∈ MulAut.innerSubgroup SL :=
      (MulAut.innerSubgroup SL).mul_mem_cancel_right hg'
    exact flag_duality_outer (hcancel.mp hi)
  have he_to : e.toMonoidHom =
      flagDuality.toMonoidHom.comp (MulAut.conj g).toMonoidHom := by rfl
  have hsylow : ((T : Subgroup G).subgroupOf L).map (e.toMonoidHom.comp d.qL) =
      borelSL := by
    rw [he_to, ← map_map, ← map_map, hmap, hg, flagDuality_map_borel]
  have hline : (F.H.subgroupOf L).map (e.toMonoidHom.comp d.qL) =
      lineParabolicSL := by
    rw [he_to, ← map_map, ← map_map, hpar, flagDuality_map_point]
  let b : Marking d :=
    { twist := e.symm
      sylow := by simpa only [MulEquiv.symm_symm] using hsylow
      parabolic := by simpa only [MulEquiv.symm_symm] using hline
      naturalDual := BinaryLinearThree.AutomorphismAction.naturalOuterEquiv e.symm he }
  exact ⟨b⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
