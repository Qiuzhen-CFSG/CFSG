module
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.CenterBounds
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFixed

/-!
# Natural planes and the fixed-space family of the symplectic pair

The two radicals have relative index |F| in the standard Sylow subgroup.
They are the pointwise stabilizers of the plane in the natural and graph
summands, respectively. These facts force any fixed-space-family member
with parameter greater than log₂ |F| into both radicals and hence into the
Sylow center. The chapter adapter applies the central root contradiction.

The transvection-root family below consists of actual conjugates of the
long matrix root, with their inclusion in the standard Sylow recorded.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389.
-/

@[expose] public section
open scoped Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
set_option linter.unusedSectionVars false

/-- Actual long-root subgroups contained in the standard Sylow subgroup. -/
def IsSylowTransvectionRoot (R : Subgroup (Sp F)) : Prop :=
  R ≤ unipotent ∧ ∃ g : Sp F, (RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom = R

lemma root_zero_isSylowTransvectionRoot :
    IsSylowTransvectionRoot (RootSubgroup.group (F := F) 0) := by
  constructor
  · intro g hg
    obtain ⟨s,rfl⟩ := (RootSubgroup.mem_group_iff 0 g).mp hg
    exact positive_root_mem_unipotent 0 s (Or.inl rfl)
  · refine ⟨1, ?_⟩
    ext g
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa using hx
    · intro hg
      exact ⟨g,hg,by simp⟩

lemma IsSylowTransvectionRoot.card {R : Subgroup (Sp F)}
    (hR : IsSylowTransvectionRoot R) : Nat.card R = Nat.card F := by
  obtain ⟨g,rfl⟩ := hR.2
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,RootSubgroup.card]

lemma IsSylowTransvectionRoot.rank_le {n : ℕ} (hF : Nat.card F = 2^n)
    {R A : Subgroup (Sp F)} (hR : IsSylowTransvectionRoot R) (hAR : A ≤ R) :
    rank A ≤ n := by
  have h := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hAR)
  rwa [hR.card,hF,Nat.log_pow (by decide : 1 < 2)] at h

lemma IsSylowTransvectionRoot.relIndex_planeRadical {R : Subgroup (Sp F)}
    (hR : IsSylowTransvectionRoot R) (hRP : R ≤ planeRadical) :
    R.relIndex planeRadical = Nat.card F^2 := by
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (Sp F)) R
    planeRadical bot_le hRP
  simp only [Subgroup.relIndex_bot_left,hR.card,card_planeRadical] at h
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F))
  rw [h,show Nat.card F * Nat.card F^2 = Nat.card F^3 by ring]

lemma IsSylowTransvectionRoot.log_relIndex_planeRadical {n : ℕ}
    (hF : Nat.card F = 2^n) {R : Subgroup (Sp F)}
    (hR : IsSylowTransvectionRoot R) (hRP : R ≤ planeRadical) :
    Nat.log 2 (R.relIndex planeRadical) = 2*n := by
  rw [hR.relIndex_planeRadical hRP,hF,← pow_mul,Nat.log_pow (by decide : 1 < 2)]
  omega

lemma natural_injective : Function.Injective (binaryNatural (F := F)) := by
  intro g h he
  apply Subtype.ext
  ext i j
  have hv := congrArg (fun f : Module.End (ZMod 2) (Vector F) =>
    f (Pi.single j 1) i) he
  change (g.val *ᵥ Pi.single j 1) i = (h.val *ᵥ Pi.single j 1) i at hv
  simpa [Matrix.mulVec_single] using hv

lemma planeRadical_le_unipotent : planeRadical (F := F) ≤ unipotent := by
  rw [planeRadical_eq_wing]
  exact Subgroup.map_subtype_le _

lemma pointRadical_le_unipotent : pointRadical (F := F) ≤ unipotent := by
  rw [pointRadical_eq_wing]
  exact Subgroup.map_subtype_le _

lemma planeRadical_relIndex_unipotent :
    (planeRadical (F := F)).relIndex unipotent = Nat.card F := by
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (Sp F)) planeRadical
    unipotent bot_le planeRadical_le_unipotent
  simp only [Subgroup.relIndex_bot_left,card_planeRadical,card_unipotent] at h
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := F)) 3)
  rw [h,show (Nat.card F)^3 * Nat.card F = (Nat.card F)^4 by ring]

lemma pointRadical_relIndex_unipotent :
    (pointRadical (F := F)).relIndex unipotent = Nat.card F := by
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (Sp F)) pointRadical
    unipotent bot_le pointRadical_le_unipotent
  simp only [Subgroup.relIndex_bot_left,card_pointRadical,card_unipotent] at h
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := F)) 3)
  rw [h,show (Nat.card F)^3 * Nat.card F = (Nat.card F)^4 by ring]

lemma log_relIndex_radical_le {n : ℕ} (hF : Nat.card F = 2^n)
    {A : Subgroup (Sp F)} (hA : A ≤ unipotent) (i : Bool) :
    Nat.log 2 ((if i then planeRadical else pointRadical).relIndex A) ≤ n := by
  have hi : (if i then planeRadical else pointRadical : Subgroup (Sp F)).relIndex
      unipotent = Nat.card F := by
    cases i
    · exact pointRadical_relIndex_unipotent
    · exact planeRadical_relIndex_unipotent
  have hb := Nat.log_mono_right (b := 2)
    (Subgroup.relIndex_le_of_le_right hA (by rw [hi]; exact Nat.card_pos.ne'))
  rwa [hi,hF,Nat.log_pow (by decide : 1 < 2)] at hb

lemma le_planeRadical_iff_plane_fixed {A : Subgroup (Sp F)} (hA : A ≤ unipotent) :
    A ≤ planeRadical ↔ (plane F).restrictScalars (ZMod 2) ≤ fixedSpace binaryNatural A := by
  constructor
  · intro h v hv g
    have hh : v ∈ fixedSpace (binaryNatural (F := F)) planeRadical := by
      rwa [planeRadical_natural_fixedSpace]
    exact hh ⟨g.val,h g.property⟩
  · intro h g hg
    obtain ⟨⟨b,u,w,v⟩,he⟩ := element_surjective ⟨g,hA hg⟩
    have hg' : (element b u w v).val = g := congrArg Subtype.val he
    have hh := congrFun (h (e_mem_plane (F := F) 1) ⟨g,hg⟩) (.inl 0)
    change (g.val *ᵥ e 1) (.inl 0) = e (F := F) 1 (.inl 0) at hh
    rw [← hg',element_matrix] at hh
    have hb : b = 0 := by
      simpa [Theory.SpecificGroups.SymplecticFour.e,Matrix.mulVec_single] using hh
    rw [← hg',planeRadical_eq_wing]
    exact ⟨element b u w v,(element_mem_wing _ _ _ _ _).mpr hb,rfl⟩

lemma mem_conjugateNatural_fixedSpace_iff (A : Subgroup (Sp F)) (v : Vector F) :
    v ∈ fixedSpace binaryNatural (A.map (graphAut (F := F)).toMonoidHom) ↔
      (0,v) ∈ fixedSpace graphPair A := by
  constructor
  · intro h g
    change (symplecticNatural 2 (g : Sp F) 0,
      symplecticNatural 2 (graphAut (g : Sp F)) v) = (0,v)
    exact Prod.ext (map_zero _) (h ⟨_,Subgroup.mem_map_of_mem _ g.property⟩)
  · intro h g
    obtain ⟨x,hx,hg⟩ := g.property
    change binaryNatural (g : Sp F) v = v
    rw [← hg]
    exact congrArg Prod.snd (h ⟨x,hx⟩)

lemma le_pointRadical_iff_conjugate_plane_fixed {A : Subgroup (Sp F)}
    (hA : A ≤ unipotent) : A ≤ pointRadical ↔
      (plane F).restrictScalars (ZMod 2) ≤
        fixedSpace binaryNatural (A.map (graphAut (F := F)).toMonoidHom) := by
  constructor
  · intro h v hv
    apply (mem_conjugateNatural_fixedSpace_iff A v).mpr
    have hh : (0,v) ∈ fixedSpace (graphPair (F := F)) pointRadical := by
      rw [pointRadical_fixedSpace]
      exact ⟨Submodule.zero_mem _,hv⟩
    intro g
    exact hh ⟨g.val,h g.property⟩
  · intro h g hg
    obtain ⟨⟨b,u,w,v⟩,he⟩ := element_surjective ⟨g,hA hg⟩
    have hg' : (element b u w v).val = g := congrArg Subtype.val he
    have hh := congrFun
      (h (e_mem_plane (F := F) 1) ⟨_,Subgroup.mem_map_of_mem _ hg⟩) (.inl 0)
    change ((graphAut g).val *ᵥ e 1) (.inl 0) = e (F := F) 1 (.inl 0) at hh
    rw [← hg',graphAut_apply] at hh
    change (graphMatrix (element b u w v).val.val *ᵥ e 1) (.inl 0) = _ at hh
    rw [element_matrix] at hh
    have hv : v = 0 := by
      simpa [Theory.SpecificGroups.SymplecticFour.e,Matrix.mulVec_single,
        graphMatrix,minor,first,second,fromBlocks] using hh
    rw [← hg',pointRadical_eq_wing]
    exact ⟨element b u w v,(element_mem_wing _ _ _ _ _).mpr hv,rfl⟩

end SymplecticConjugatePair
