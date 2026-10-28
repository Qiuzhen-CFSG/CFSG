module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.Action
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The literal M23 restriction on an incident octad

The point-stabilizer subgroup acts on the seven points left after deleting the
fixed point from an octad.  We keep that action as a literal permutation
action.  Its image is obtained from the full alternating eight-coordinate
image by extending a seven-permutation by the fixed coordinate, and its
kernel is the restriction of the octad two-core.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.CocodeOctad

/-- The seven coordinates left after removing the distinguished point. -/
def octadSeven (O : Octad) : Finset (Fin 24) := O.val.erase 0

lemma octadSeven_card (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (octadSeven O).card = 7 := by
  rw [octadSeven, Finset.card_erase_of_mem hO, m24Blocks_card _ O.property]

/-- The native M23 subgroup whose point embedding stabilizes the octad. -/
def m23OctadStabilizer (O : Octad) : Subgroup M23 :=
  (octadStabilizer O).comap MathieuCode.pointEmbedding

/-- The literal inclusion in the M24 octad stabilizer. -/
def m23ToOctad (O : Octad) : m23OctadStabilizer O →* octadStabilizer O :=
  (pointEmbedding.comp (m23OctadStabilizer O).subtype).codRestrict _ (fun g => g.property)

lemma m23ToOctad_injective (O : Octad) : Function.Injective (m23ToOctad O) := by
  intro g h he
  apply Subtype.ext
  exact pointEmbedding_injective (congrArg Subtype.val he)

/-- Restriction action on a finite M24 coordinate set. -/
def setAction24 (B : Finset (Fin 24)) :
    MulAction.stabilizer M24 B →* Equiv.Perm B where
  toFun g := g.val.val.subtypePerm (MulAction.mem_stabilizer_finset.mp g.property)
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

def sevenStabilizer (O : Octad) : Subgroup M24 :=
  MulAction.stabilizer M24 (octadSeven O)

def toSevenStabilizer (O : Octad) (_hO : (0 : Fin 24) ∈ O.val) :
    m23OctadStabilizer O →* sevenStabilizer O where
  toFun g := ⟨MathieuCode.pointEmbedding g, by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro x hx
    change x ∈ O.val.erase 0 at hx
    change pointEmbedding (g : M23) • x ∈ O.val.erase 0
    rw [Finset.mem_erase] at hx ⊢
    refine ⟨?_, (MulAction.mem_stabilizer_finset.mp g.property x).mpr hx.2⟩
    intro hz
    have hf : ((MathieuCode.pointEmbedding (g : M23) : M24) : Equiv.Perm (Fin 24)) 0 = 0 :=
      MathieuCode.pointEmbedding_fixed (g : M23)
    apply hx.1
    apply ((MathieuCode.pointEmbedding (g : M23) : M24) : Equiv.Perm (Fin 24)).injective
    have hz' : ((MathieuCode.pointEmbedding (g : M23) : M24) : Equiv.Perm (Fin 24)) x =
        ((MathieuCode.pointEmbedding (g : M23) : M24) : Equiv.Perm (Fin 24)) 0 := by
      change ((MathieuCode.pointEmbedding (g : M23) : M24) : Equiv.Perm (Fin 24)) x = 0 at hz
      simpa [hf] using hz
    exact hz'⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    exact Subtype.ext (by simp [MathieuCode.pointEmbedding])

def sevenCoordinateAction (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    m23OctadStabilizer O →* Equiv.Perm (octadSeven O) :=
  (setAction24 (octadSeven O)).comp (toSevenStabilizer O hO)

@[simp] lemma sevenCoordinateAction_apply (O : Octad)
    (hO : (0 : Fin 24) ∈ O.val) (g : m23OctadStabilizer O)
    (x : octadSeven O) :
    (sevenCoordinateAction O hO g x).val =
      ((MathieuCode.pointEmbedding (g : M23) : M24) : Equiv.Perm (Fin 24)) x.val := by
  change ((coordinateAction O ⟨MathieuCode.pointEmbedding g, g.property⟩)
      ⟨x.val, (Finset.mem_erase.mp x.property).2⟩).val = _
  rw [coordinateAction_apply]

/-- The relative pullback of the intrinsic octad two-core. -/
def m23OctadKernelRestricted (O : Octad) (_hO : (0 : Fin 24) ∈ O.val) :
    Subgroup (m23OctadStabilizer O) :=
  (pCore 2 (octadStabilizer O)).comap (m23ToOctad O)

lemma sevenCoordinateAction_ker (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (sevenCoordinateAction O hO).ker = m23OctadKernelRestricted O hO := by
  ext g
  change sevenCoordinateAction O hO g = 1 ↔ m23ToOctad O g ∈ pCore 2 _
  rw [core_eq_coordinateKernel, mem_coordinateAction_ker]
  constructor
  · intro hg i hi
    by_cases hi0 : i = 0
    · subst i
      exact pointEmbedding_fixed g.val
    · exact congrArg Subtype.val (Equiv.congr_fun hg
        ⟨i, Finset.mem_erase.mpr ⟨hi0, hi⟩⟩)
  · intro hg
    apply Equiv.ext
    intro x
    exact Subtype.ext (hg x.val (Finset.mem_erase.mp x.property).2)

noncomputable def octadSevenComplementEquiv (O : Octad)
    (_hO : (0 : Fin 24) ∈ O.val) : octadSeven O ≃ {x : O.val // x.val ≠ 0} where
  toFun x := ⟨⟨x.val, (Finset.mem_erase.mp x.property).2⟩,
    (Finset.mem_erase.mp x.property).1⟩
  invFun x := ⟨x.val.val, Finset.mem_erase.mpr ⟨x.property, x.val.property⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

noncomputable def sevenExtend (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (p : Equiv.Perm (octadSeven O)) : Equiv.Perm O.val :=
  p.extendDomain (octadSevenComplementEquiv O hO)

lemma sevenExtend_apply (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (p : Equiv.Perm (octadSeven O)) (x : octadSeven O) :
    (sevenExtend O hO p ((octadSevenComplementEquiv O hO) x)).val =
      (p x).val := by
  rw [sevenExtend, Equiv.Perm.extendDomain_apply_image]
  rfl

lemma sevenExtend_fixed (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (p : Equiv.Perm (octadSeven O)) :
    sevenExtend O hO p ⟨0, hO⟩ = ⟨0, hO⟩ := by
  rw [sevenExtend, Equiv.Perm.extendDomain_apply_not_subtype]
  simp

lemma sevenCoordinateAction_range (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (sevenCoordinateAction O hO).range = alternatingGroup (octadSeven O) := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    have hgO : MathieuCode.pointEmbedding (g : M23) ∈ octadStabilizer O := g.property
    let q : Equiv.Perm O.val :=
      coordinateAction O ⟨MathieuCode.pointEmbedding (g : M23), hgO⟩
    have hq : Equiv.Perm.sign q = 1 := by
      apply Equiv.Perm.mem_alternatingGroup.mp
      rw [← coordinateAction_range]
      exact ⟨⟨MathieuCode.pointEmbedding (g : M23), g.property⟩, rfl⟩
    apply Equiv.Perm.mem_alternatingGroup.mpr
    have hqext : q = sevenExtend O hO (sevenCoordinateAction O hO g) := by
      apply Equiv.ext
      intro x
      by_cases hx : x.val = 0
      · have hx' : x = ⟨0, hO⟩ := Subtype.ext hx
        rw [hx', sevenExtend_fixed]
        apply Subtype.ext
        change ((MathieuCode.pointEmbedding (g : M23) : M24) : Equiv.Perm (Fin 24)) 0 = 0
        exact MathieuCode.pointEmbedding_fixed (g : M23)
      · let y : octadSeven O := ⟨x.val, Finset.mem_erase.mpr ⟨hx, x.property⟩⟩
        have hxy : x = (octadSevenComplementEquiv O hO) y := by
          apply Subtype.ext
          rfl
        apply Subtype.ext
        rw [hxy]
        rw [sevenExtend_apply]
        change ((MathieuCode.pointEmbedding (g : M23) : M24) : Equiv.Perm (Fin 24))
          y.val = (sevenCoordinateAction O hO g y).val
        exact (sevenCoordinateAction_apply O hO g y).symm
    have hsign : Equiv.Perm.sign (sevenExtend O hO (sevenCoordinateAction O hO g)) = 1 := by
      rw [← hqext]
      exact hq
    rw [sevenExtend, Equiv.Perm.sign_extendDomain] at hsign
    exact hsign
  · intro hp
    have hq : Equiv.Perm.sign (sevenExtend O hO p) = 1 := by
      rw [sevenExtend, Equiv.Perm.sign_extendDomain]
      exact Equiv.Perm.mem_alternatingGroup.mp hp
    have hqmem : sevenExtend O hO p ∈ alternatingGroup O.val :=
      Equiv.Perm.mem_alternatingGroup.mpr hq
    rw [← coordinateAction_range] at hqmem
    obtain ⟨g, hg⟩ := hqmem
    have hfix : coordinateAction O g ⟨0, hO⟩ = ⟨0, hO⟩ := by
      rw [hg, sevenExtend_fixed]
    have hfix0 : ((g : M24) : Equiv.Perm (Fin 24)) 0 = 0 := by
      simpa [coordinateAction_apply] using congrArg Subtype.val hfix
    have hgpoint : (g : M24) ∈ MulAction.stabilizer M24 (0 : Fin 24) := by
      rw [MulAction.mem_stabilizer_iff]
      exact hfix0
    rw [← MathieuCode.pointEmbedding_range] at hgpoint
    obtain ⟨m, hm⟩ := hgpoint
    refine ⟨⟨m, ?_⟩, ?_⟩
    · exact (show MathieuCode.pointEmbedding (m : M23) ∈ octadStabilizer O from by
        rw [hm]
        exact g.property)
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [sevenCoordinateAction_apply]
    change ((MathieuCode.pointEmbedding (m : M23) : M24) : Equiv.Perm (Fin 24)) x.val = _
    let xO : O.val := ⟨x.val, (Finset.mem_erase.mp x.property).2⟩
    have hm' : (⟨MathieuCode.pointEmbedding (m : M23), (show
        MathieuCode.pointEmbedding (m : M23) ∈ octadStabilizer O from by
          rw [hm]
          exact g.property)⟩ : octadStabilizer O) = g := by
      apply Subtype.ext
      exact hm
    have hcoord := congrArg (fun z : Equiv.Perm O.val => z xO) hg
    rw [← hm'] at hcoord
    have hx : x.val ≠ 0 := (Finset.mem_erase.mp x.property).1
    let y : octadSeven O := ⟨x.val, Finset.mem_erase.mpr ⟨hx,
      (Finset.mem_erase.mp x.property).2⟩⟩
    have hxy : xO = octadSevenComplementEquiv O hO y := by
      apply Subtype.ext
      rfl
    rw [hxy] at hcoord
    have hcoord' := congrArg Subtype.val hcoord
    rw [sevenExtend_apply] at hcoord'
    simpa [y, octadSevenComplementEquiv, coordinateAction_apply] using hcoord'

noncomputable def sevenAlternatingAction (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    m23OctadStabilizer O →* alternatingGroup (octadSeven O) :=
  (sevenCoordinateAction O hO).codRestrict (alternatingGroup (octadSeven O))
    (fun g => by
      rw [← sevenCoordinateAction_range O hO]
      exact ⟨g, rfl⟩)

lemma sevenAlternatingAction_surjective (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Function.Surjective (sevenAlternatingAction O hO) := by
  intro p
  have hp : (p : Equiv.Perm (octadSeven O)) ∈
      (sevenCoordinateAction O hO).range := by
    rw [sevenCoordinateAction_range O hO]
    exact p.property
  obtain ⟨g, hg⟩ := hp
  exact ⟨g, Subtype.ext hg⟩

lemma sevenAlternatingAction_ker (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (sevenAlternatingAction O hO).ker = (sevenCoordinateAction O hO).ker := by
  ext g
  constructor
  · intro hg
    have hfg : sevenAlternatingAction O hO g = 1 := MonoidHom.mem_ker.mp hg
    apply MonoidHom.mem_ker.mpr
    exact congrArg Subtype.val hfg
  · intro hg
    have hfg : sevenCoordinateAction O hO g = 1 := MonoidHom.mem_ker.mp hg
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact hfg

lemma m23OctadKernelRestricted_isPGroup (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    IsPGroup 2 (m23OctadKernelRestricted O hO) :=
  IsPGroup.comap_of_injective pCore_isPGroup (m23ToOctad O) (m23ToOctad_injective O)

lemma sevenCoordinateAction_core (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    pCore 2 (m23OctadStabilizer O) = (sevenCoordinateAction O hO).ker := by
  have hker : (sevenCoordinateAction O hO).ker ≤ pCore 2 (m23OctadStabilizer O) := by
    rw [sevenCoordinateAction_ker O hO]
    have hn : (m23OctadKernelRestricted O hO).Normal := by
      rw [← sevenCoordinateAction_ker O hO]
      infer_instance
    exact le_sSup ⟨hn, m23OctadKernelRestricted_isPGroup O hO⟩
  apply le_antisymm
  · let f := sevenAlternatingAction O hO
    have hn : ((pCore 2 (m23OctadStabilizer O)).map f).Normal :=
      Subgroup.Normal.map inferInstance f (sevenAlternatingAction_surjective O hO)
    have hp : IsPGroup 2 ((pCore 2 (m23OctadStabilizer O)).map f) :=
      pCore_isPGroup.map f
    have hcard : Nat.card (octadSeven O) = 7 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, octadSeven_card O hO]
    have hcard' : Fintype.card (octadSeven O) = 7 := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    let _ : IsSimpleGroup (alternatingGroup (octadSeven O)) :=
      alternatingGroup.isSimpleGroup (by rw [hcard]; norm_num)
    let _ : Nontrivial (octadSeven O) :=
      not_subsingleton_iff_nontrivial.mp (by
        intro hs
        have hle : Fintype.card (octadSeven O) ≤ 1 :=
          Fintype.card_le_one_iff.mpr (fun a b => Subsingleton.elim a b)
        rw [hcard'] at hle
        omega)
    have hb : (pCore 2 (m23OctadStabilizer O)).map f = ⊥ := by
      rcases hn.eq_bot_or_eq_top with h | h
      · exact h
      · have htwo : IsPGroup 2 (alternatingGroup (octadSeven O)) :=
          (h ▸ hp).of_surjective (⊤ : Subgroup (alternatingGroup (octadSeven O))).subtype
            (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
        obtain ⟨n, hn⟩ := htwo.exists_card_dvd_pow
        have hc : Nat.card (alternatingGroup (octadSeven O)) = 2520 := by
          rw [nat_card_alternatingGroup, hcard]
          norm_num [Nat.factorial]
        have hd : 3 ∣ 2 ^ n := (show 3 ∣ 2520 by decide).trans (hc ▸ hn)
        exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
    rw [← sevenAlternatingAction_ker O hO]
    intro x hx
    have h : f x ∈ (⊥ : Subgroup (alternatingGroup (octadSeven O))) :=
      hb ▸ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact MonoidHom.mem_ker.mpr (by simpa using h)
  · exact hker

/-- A faithful quotient action onto the literal alternating-seven image. -/
def quotientSevenEquiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (m23OctadStabilizer O ⧸ (sevenCoordinateAction O hO).ker) ≃*
      alternatingGroup (octadSeven O) :=
  (QuotientGroup.quotientKerEquivRange (sevenCoordinateAction O hO)).trans
    (MulEquiv.subgroupCongr (sevenCoordinateAction_range O hO))

end MathieuCode.CocodeOctad
