module
public import Theory.Representation.BinaryPermutation.EightGeometry
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightSylow
import Mathlib.Tactic

/-!
# The singular point interval in the eight-letter permutation module

A three-cycle extracts a pair from any even word perpendicular to the
marked four-word and outside its line modulo constants. The block swap
and the two block cycles then span the whole perpendicular. The finite
certificates check only the 256 binary words and six spanning vectors.
Permutation transport handles every nonzero singular point. A separate
Sylow calculation uses four internal three-cycles to force the fixed
representative to be constant on each block, proving its singularity.

The resulting interval theorem retains the actual six-dimensional quotient,
its half-weight form and the full alternating point-stabilizer action.
The application to the original L₁T and V₅/V₁ is in Chapter12.Section06.
Source: Aschbacher--Smith, 12.6.24(1), printed pp.830--831.
The form is reused from the attributed ATLAS port through EightGeometry.
-/

public section
namespace BinaryPermutation.EightPointInterval
open BinaryPermutation TerminalOrthogonal.Eight
open scoped BigOperators
private def c : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 2
private def s : Equiv.Perm (Fin 8) := Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7
private def z : Full (Fin 8) := ![1,1,1,1,0,0,0,0]
private def e : Full (Fin 8) := ![1,1,0,0,0,0,0,0]
private def basisWord (i : Fin 6) : Full (Fin 8) :=
  if i.val < 3 then Pi.single ⟨i.val, by omega⟩ 1 + Pi.single 3 1
  else Pi.single ⟨i.val+1,by omega⟩ 1 + Pi.single 7 1
private noncomputable def polar (w : Full (Fin 8)) : ZMod 2 :=
  Atlas.Order20160A8.HalfWeight.binaryHalfWeight (z+w) -
  Atlas.Order20160A8.HalfWeight.binaryHalfWeight z -
  Atlas.Order20160A8.HalfWeight.binaryHalfWeight w
private theorem extract : ∀ w : Full (Fin 8), (∑ i,w i)=0 → polar w=0 →
    w ≠ 0 → w ≠ allOne (Fin 8) → w ≠ z → w ≠ allOne (Fin 8)+z →
    ∃ b : Bool, ∃ j : Fin 3,
      representation (Fin 8) (c^j.val)
        (representation (Fin 8) c (representation (Fin 8) (if b then s else 1) w) +
          representation (Fin 8) (if b then s else 1) w) = e := by
  decide +kernel
private theorem basis_orbit : ∀ i : Fin 6, ∃ b : Bool, ∃ j : Fin 3,
    basisWord i = representation (Fin 8) (if b then s else 1)
      (z + representation (Fin 8) (c^j.val) e) := by decide +kernel
private theorem expansion : ∀ w : Full (Fin 8), (∑ i,w i)=0 → polar w=0 →
    w = ∑ i : Fin 6, w (if i.val<3 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩) • basisWord i := by
  decide +kernel

private theorem raw_interval (U : Submodule (ZMod 2) (Full (Fin 8)))
    (hz : z ∈ U)
    (hc : ∀ w ∈ U, representation (Fin 8) c w ∈ U)
    (hs : ∀ w ∈ U, representation (Fin 8) s w ∈ U)
    (w : Full (Fin 8)) (hw : w ∈ U) (heven : (∑ i,w i)=0) (hpolar : polar w=0)
    (h0 : w ≠ 0) (h1 : w ≠ allOne (Fin 8)) (hz' : w ≠ z)
    (h1z : w ≠ allOne (Fin 8)+z) :
    ∀ v : Full (Fin 8), (∑ i,v i)=0 → polar v=0 → v ∈ U := by
  have hpow (n : ℕ) (v : Full (Fin 8)) (hv : v ∈ U) :
      representation (Fin 8) (c^n) v ∈ U := by
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      rw [pow_succ',map_mul,Module.End.mul_apply]
      exact hc _ ih
  have hb (b : Bool) (v : Full (Fin 8)) (hv : v ∈ U) :
      representation (Fin 8) (if b then s else 1) v ∈ U := by
    cases b
    · simpa using hv
    · exact hs _ hv
  obtain ⟨b,j,hj⟩ := extract w heven hpolar h0 h1 hz' h1z
  have hem : e ∈ U := hj ▸ hpow j.val _ (U.add_mem (hc _ (hb b w hw)) (hb b w hw))
  have hbas (i : Fin 6) : basisWord i ∈ U := by
    obtain ⟨b,j,hj⟩ := basis_orbit i
    rw [hj]
    exact hb b _ (U.add_mem hz (hpow j.val e hem))
  intro v hv hp
  rw [expansion v hv hp]
  exact U.sum_mem (fun i _ => U.smul_mem _ (hbas i))

private def zCore : core (Fin 8) := ⟨z,by change (∑ i,z i)=0; decide⟩
private noncomputable def point : natural (Fin 8) := coreToNatural (Fin 8) zCore
private theorem z_projection : coreToNatural (Fin 8) zCore =
    point := rfl
private theorem polar_projection (w : core (Fin 8)) :
    form.polarBilin point (coreToNatural (Fin 8) w) =
      polar w.val := by
  change form (coreToNatural (Fin 8) zCore + coreToNatural (Fin 8) w) -
    form (coreToNatural (Fin 8) zCore) - form (coreToNatural (Fin 8) w) = _
  rw [←map_add]
  simp only [EightGeometry.form_coreToNatural]
  rfl

private theorem generators : ∀ g ∈ ({c,s} : Set (Equiv.Perm (Fin 8))),
    g ∈ alternatingGroup (Fin 8) ∧ naturalRepresentation (Fin 8) g
      point = point := by
  have hsign : c.sign=1 ∧ s.sign=1 := by decide
  have hwords : (coreRepresentation (Fin 8) c zCore).val-zCore.val=0 ∧
      (coreRepresentation (Fin 8) s zCore).val-zCore.val=allOne (Fin 8) := by decide
  intro g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  all_goals
    refine ⟨Equiv.Perm.mem_alternatingGroup.mpr ?_,?_⟩
  · exact hsign.1
  · rw [←z_projection,←coreToNatural_equivariant,←sub_eq_zero,←map_sub]
    exact (EightGeometry.coreToNatural_eq_zero _).mpr (Or.inl hwords.1)
  · exact hsign.2
  · rw [←z_projection,←coreToNatural_equivariant,←sub_eq_zero,←map_sub]
    exact (EightGeometry.coreToNatural_eq_zero _).mpr (Or.inr hwords.2)

/-- The actual even point stabilizer is irreducible on the perpendicular
modulo its distinguished singular line. -/
private theorem invariant_interval (W : Submodule (ZMod 2) (natural (Fin 8)))
    (hz : point ∈ W)
    (hupper : ∀ w ∈ W, form.polarBilin point w=0)
    (hinv : ∀ g : alternatingGroup (Fin 8), naturalRepresentation (Fin 8) g.val
        point = point →
      ∀ w ∈ W, naturalRepresentation (Fin 8) g.val w ∈ W) :
    (∀ w ∈ W, w=0 ∨ w=point) ∨
      ∀ w, form.polarBilin point w=0 → w ∈ W := by
  classical
  by_cases hsmall : ∀ w ∈ W, w=0 ∨ w=point
  · exact Or.inl hsmall
  push Not at hsmall
  obtain ⟨w,hw,h0,hz'⟩ := hsmall
  obtain ⟨v,rfl⟩ := coreToNatural_surjective w
  let U := (W.comap (coreToNatural (Fin 8))).map (core (Fin 8)).subtype
  have hmem (u : core (Fin 8)) : u.val ∈ U ↔ coreToNatural (Fin 8) u ∈ W := by
    constructor
    · rintro ⟨a,ha,he⟩
      exact (show a=u from Subtype.ext he) ▸ ha
    · intro hu
      exact ⟨u,hu,rfl⟩
  have hstable (g : Equiv.Perm (Fin 8)) (hg : g ∈ ({c,s} : Set _)) :
      ∀ u ∈ U, representation (Fin 8) g u ∈ U := by
    rintro _ ⟨u,hu,rfl⟩
    apply (hmem (coreRepresentation (Fin 8) g u)).mpr
    rw [coreToNatural_equivariant]
    exact hinv ⟨g,(generators g hg).1⟩ (generators g hg).2 _ hu
  have hn0 : v.val ≠ 0 := by
    intro he
    exact h0 ((EightGeometry.coreToNatural_eq_zero v).mpr (Or.inl he))
  have hn1 : v.val ≠ allOne (Fin 8) := by
    intro he
    exact h0 ((EightGeometry.coreToNatural_eq_zero v).mpr (Or.inr he))
  have hnz : v.val ≠ z := by
    intro he
    exact hz' (congrArg (coreToNatural (Fin 8)) (Subtype.ext he : v=zCore))
  have hn1z : v.val ≠ allOne (Fin 8)+z := by
    intro he
    apply hz'
    rw [←z_projection,←sub_eq_zero,←map_sub]
    apply (EightGeometry.coreToNatural_eq_zero _).mpr
    right
    change v.val-z=allOne (Fin 8)
    rw [he,add_sub_cancel_right]
  have hall := raw_interval U ((hmem zCore).mpr hz)
    (hstable c (by simp)) (hstable s (by simp)) v.val ((hmem v).mpr hw)
    v.property ((polar_projection v).symm.trans (hupper _ hw)) hn0 hn1 hnz hn1z
  right
  intro w hw
  obtain ⟨u,rfl⟩ := coreToNatural_surjective w
  exact (hmem u).mp (hall u.val u.property ((polar_projection u).symm.trans hw))
private theorem undo (r : Equiv.Perm (Fin 8)) (v : natural (Fin 8)) :
    naturalRepresentation (Fin 8) r (naturalRepresentation (Fin 8) r⁻¹ v)=v := by
  rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
private theorem act_conj (r g : Equiv.Perm (Fin 8)) (v : natural (Fin 8)) :
    naturalRepresentation (Fin 8) (r*g*r⁻¹) (naturalRepresentation (Fin 8) r v) =
      naturalRepresentation (Fin 8) r (naturalRepresentation (Fin 8) g v) := by
  simp only [map_mul,Module.End.mul_apply]
  rw [show naturalRepresentation (Fin 8) r⁻¹ (naturalRepresentation (Fin 8) r v)=v by
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]]
private theorem polar_invariant (r : Equiv.Perm (Fin 8)) (v w : natural (Fin 8)) :
    form.polarBilin (naturalRepresentation (Fin 8) r v) (naturalRepresentation (Fin 8) r w)=
      form.polarBilin v w := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←map_add,form_invariant]

/-- Point coordinates are constructed from the actual weight-four representative. -/
private theorem exists_point_coordinates (v : natural (Fin 8)) (hv : v ≠ 0)
    (hq : form v=0) : ∃ r : Equiv.Perm (Fin 8),
      v=naturalRepresentation (Fin 8) r point := by
  obtain ⟨w,rfl,hw⟩ := (EightGeometry.singular_iff_weight_four v hv).mp hq
  have hc : Fintype.card {i : Fin 8 // z i ≠ 0} =
      Fintype.card {i : Fin 8 // w.val i ≠ 0} := by
    have hz : (Finset.univ.filter fun i => z i ≠ 0).card=4 := by decide
    simpa only [Fintype.card_subtype,hammingNorm] using hz.trans hw.symm
  let e := Fintype.equivOfCardEq hc
  have he : coreRepresentation (Fin 8) e.extendSubtype zCore=w := by
    apply Subtype.ext
    ext i
    change z (e.extendSubtype.symm i)=w.val i
    apply (by decide : ∀ a b : ZMod 2, (a=0 ↔ b=0) → a=b)
    constructor
    · intro h
      by_contra hn
      exact (e.extendSubtype_not_mem (e.extendSubtype.symm i) (by simpa using h)) (by simpa using hn)
    · intro h
      by_contra hn
      exact (e.extendSubtype_mem (e.extendSubtype.symm i) hn) (by simpa using h)
  refine ⟨e.extendSubtype,?_⟩
  rw [←z_projection,←coreToNatural_equivariant,he]

/-- The same irreducible interval at every nonzero singular point, retaining
the full alternating action and the half-weight perpendicular. -/
theorem singular_invariant_interval (v : natural (Fin 8)) (hv : v ≠ 0)
    (hq : form v=0) (W : Submodule (ZMod 2) (natural (Fin 8)))
    (hz : v ∈ W) (hupper : ∀ w ∈ W, form.polarBilin v w=0)
    (hinv : ∀ g : alternatingGroup (Fin 8), naturalRepresentation (Fin 8) g.val v=v →
      ∀ w ∈ W, naturalRepresentation (Fin 8) g.val w ∈ W) :
    (∀ w ∈ W, w=0 ∨ w=v) ∨ ∀ w, form.polarBilin v w=0 → w ∈ W := by
  obtain ⟨r,rfl⟩ := exists_point_coordinates v hv hq
  let U := W.comap (naturalRepresentation (Fin 8) r)
  have hU : point ∈ U := hz
  have hu : ∀ w ∈ U, form.polarBilin point w=0 := by
    intro w hw
    rw [←polar_invariant r]
    exact hupper _ hw
  have hi : ∀ g : alternatingGroup (Fin 8), naturalRepresentation (Fin 8) g.val
      point=point →
      ∀ w ∈ U, naturalRepresentation (Fin 8) g.val w ∈ U := by
    intro g hg w hw
    have heven : r*g.val*r⁻¹ ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      simp only [map_mul,map_inv,Equiv.Perm.mem_alternatingGroup.mp g.property,mul_one,mul_inv_cancel]
    have hf : naturalRepresentation (Fin 8) (r*g.val*r⁻¹)
        (naturalRepresentation (Fin 8) r point)=
        naturalRepresentation (Fin 8) r point := by
      rw [act_conj,hg]
    have hh := hinv ⟨r*g.val*r⁻¹,heven⟩ hf _ hw
    rwa [act_conj] at hh
  rcases invariant_interval U hU hu hi with hsmall | hfull
  · left
    intro w hw
    have hm : naturalRepresentation (Fin 8) r⁻¹ w ∈ U := by
      change naturalRepresentation (Fin 8) r (naturalRepresentation (Fin 8) r⁻¹ w) ∈ W
      rwa [undo]
    rcases hsmall _ hm with he | he
    · left
      have hh := congrArg (naturalRepresentation (Fin 8) r) he
      simpa only [undo,map_zero] using hh
    · right
      have hh := congrArg (naturalRepresentation (Fin 8) r) he
      simpa only [undo] using hh
  · right
    intro w hw
    have hp : form.polarBilin point
        (naturalRepresentation (Fin 8) r⁻¹ w)=0 := by
      rw [←polar_invariant r,undo]
      exact hw
    have hh := hfull _ hp
    change naturalRepresentation (Fin 8) r (naturalRepresentation (Fin 8) r⁻¹ w) ∈ W at hh
    rwa [undo] at hh

end BinaryPermutation.EightPointInterval


public section
namespace BinaryPermutation.EightPointInterval
open BinaryPermutation TerminalOrthogonal.Eight
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
private def sylowGenerators : Fin 4 → Equiv.Perm (Fin 8) :=
  ![Equiv.swap 0 1 * Equiv.swap 1 2,Equiv.swap 0 1 * Equiv.swap 1 3,
    Equiv.swap 4 5 * Equiv.swap 5 6,Equiv.swap 4 5 * Equiv.swap 5 7]
private theorem sylowGenerators_mem : ∀ i, sylowGenerators i ∈ fourStabilizer := by
  intro i
  rw [mem_fourStabilizer]
  have h : ∀ i : Fin 4, ∀ j k : Fin 8,
      (sylowGenerators i j).val/4=(sylowGenerators i k).val/4 ↔ j.val/4=k.val/4 := by decide
  exact h i
private theorem sylowGenerators_fix : ∀ j, ∃ i : Fin 8, sylowGenerators j i=i := by decide
private theorem fixed_singular : ∀ w : Full (Fin 8),
    (∀ j, representation (Fin 8) (sylowGenerators j) w=w) →
      Atlas.Order20160A8.HalfWeight.binaryHalfWeight w=0 := by decide +kernel

/-- Every vector fixed by an alternating Sylow two-subgroup is singular
for the half-weight form, on the actual six-dimensional quotient. -/
theorem sylow_fixed_singular (Q : Sylow 2 (alternatingGroup (Fin 8)))
    (v : natural (Fin 8))
    (hfix : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      naturalRepresentation (Fin 8) g.val v=v) : form v=0 := by
  by_cases hv : v=0
  · simp [hv]
  obtain ⟨r,hr⟩ := alternating_exists_conjugate_stabilizer Q v hv hfix
  let u := naturalRepresentation (Fin 8) r.val v
  have hu (j : Fin 4) : naturalRepresentation (Fin 8) (sylowGenerators j) u=u := by
    have hg := (hr (r.val⁻¹ * sylowGenerators j * r.val)).mpr (by
      simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using sylowGenerators_mem j)
    have hh := congrArg (naturalRepresentation (Fin 8) r.val) hg
    have he : naturalRepresentation (Fin 8) (sylowGenerators j)
        (naturalRepresentation (Fin 8) r.val v) =
      naturalRepresentation (Fin 8) r.val
        (naturalRepresentation (Fin 8) (r.val⁻¹ * sylowGenerators j * r.val) v) := by
      simp only [←Module.End.mul_apply,←map_mul,mul_assoc,mul_inv_cancel_left]
    exact he.trans hh
  obtain ⟨w,hw⟩ := coreToNatural_surjective u
  have hf (j : Fin 4) : representation (Fin 8) (sylowGenerators j) w.val=w.val := by
    obtain ⟨i,hi⟩ := sylowGenerators_fix j
    apply (deleted_fixed_iff_of_fixed_point (sylowGenerators j) w.val i hi).mp
    have hh := hu j
    rw [←hw] at hh
    exact congrArg Subtype.val hh
  have hs : form u=0 := by
    rw [←hw,EightGeometry.form_coreToNatural]
    exact fixed_singular w.val hf
  exact (form_invariant r.val v).symm.trans hs
end BinaryPermutation.EightPointInterval

