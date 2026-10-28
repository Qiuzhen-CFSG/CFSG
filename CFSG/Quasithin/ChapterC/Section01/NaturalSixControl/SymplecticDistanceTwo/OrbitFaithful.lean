module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitQuotient
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitCore
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer
public import Theory.Alternating.Aut

/-!
# Faithfulness of the actual critical-orbit action

The large-core branch makes the A6 component act nontrivially on the literal
orbit quotient A/Z-alpha. Every nontrivial normal subgroup of the marked
permutation image contains A6, since A6 is simple and has trivial centralizer.
Thus the quotient representation is faithful. When the projection is onto,
transport to S6 preserves both the exact conjugation formula and coordinates.
No identification with the original natural four-space is imposed.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
  {c b : Vertex R}
  (hb : s.geometry.b R = 2)
  (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
  (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
  [IsElementaryAbelian 2 (OrbitQuotient R c b)]

include hb hc hab hcb

theorem orbit_component_nontrivial (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    ∃ l : L, orbitRepresentation R c b ⟨l,mem_top _⟩ ≠ 1 := by
  by_contra! hn
  apply s.criticalOrbit_commutator_not_le_Z h t hfull hb hlarge hc hab hcb
  have he : ⁅L,criticalOrbitNative R c b⁆ ≤ orbitLayer R := by
    apply commutator_le.mpr
    intro l hl a ha
    exact ((orbitSection R c b (s.orbitLayer_le_orbit hb hc hab hcb)).action_mem_ker_iff
      ⟨l,mem_top _⟩).mp (hn ⟨l,hl⟩) a ha
  rw [commutator_comm] at he
  rw [Ltilde_alpha,s.residual,criticalOrbit,←map_commutator]
  exact (map_le_iff_le_comap.mpr he)

theorem orbitImageRepresentation_injective (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    Function.Injective (s.orbitImageRepresentation hb hc hab hcb) := by
  let H := s.projection.range
  let C := (alternatingGroup (Fin 6)).subgroupOf H
  let e : C ≃* alternatingGroup (Fin 6) := subgroupOfEquivOfLe s.image_contains_alternating
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hLC : L.map s.projection.rangeRestrict = C := by
    apply map_injective H.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le s.image_contains_alternating]
    exact s.component_image
  have hC : centralizer (C : Set H) = ⊥ := by
    apply bot_unique
    intro x hx
    have hm : (x : Equiv.Perm (Fin 6)) ∈ centralizer
        (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) := by
      intro y hy
      exact congrArg Subtype.val (hx ⟨y,s.image_contains_alternating hy⟩ hy)
    rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide)] at hm
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp hm))
  apply (s.orbitImageRepresentation hb hc hab hcb).ker_eq_bot_iff.mp
  by_contra hn
  have hle := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot C
    (Group.IsPerfect.not_isMulCommutative C) hC
    (s.orbitImageRepresentation hb hc hab hcb).ker hn
  obtain ⟨l,hl⟩ := s.orbit_component_nontrivial hb hc hab hcb h t hfull hlarge
  apply hl
  rw [←s.orbitImageRepresentation_projection hb hc hab hcb]
  apply hle
  rw [←hLC]
  exact mem_map_of_mem _ l.property

omit hb hc hab hcb [IsElementaryAbelian 2 (OrbitQuotient R c b)] in
def orbitImageEquiv (hsurj : Function.Surjective s.projection) :
    s.projection.range ≃* S :=
  MulEquiv.ofBijective s.projection.range.subtype ⟨Subtype.coe_injective,by
    intro g
    obtain ⟨m,hm⟩ := hsurj g
    exact ⟨⟨g,⟨m,hm⟩⟩,rfl⟩⟩

def orbitFullRepresentation (hsurj : Function.Surjective s.projection) :
    Representation (ZMod 2) S (Additive (OrbitQuotient R c b)) :=
  (s.orbitImageRepresentation hb hc hab hcb).comp (s.orbitImageEquiv hsurj).symm.toMonoidHom

theorem orbitFullRepresentation_projection (hsurj : Function.Surjective s.projection)
    (m : (⊤ : Subgroup M)) :
    s.orbitFullRepresentation hb hc hab hcb hsurj (s.projection m) =
      orbitRepresentation R c b m := by
  have he : (s.orbitImageEquiv hsurj).symm (s.projection m) = s.orbitProjection m := by
    apply (s.orbitImageEquiv hsurj).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change s.orbitImageRepresentation hb hc hab hcb
    ((s.orbitImageEquiv hsurj).symm (s.projection m)) = _
  rw [he,s.orbitImageRepresentation_projection]

theorem orbitFullRepresentation_injective (hsurj : Function.Surjective s.projection)
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    Function.Injective (s.orbitFullRepresentation hb hc hab hcb hsurj) :=
  (s.orbitImageRepresentation_injective hb hc hab hcb h t hfull hlarge).comp
    (s.orbitImageEquiv hsurj).symm.injective

def orbitFullSection (hsurj : Function.Surjective s.projection) :
    BinaryConjugationSection ⊤ (criticalOrbitNative R c b) (orbitLayer R)
      ((s.orbitFullRepresentation hb hc hab hcb hsurj).comp
        (s.projection.comp (⊤ : Subgroup M).subtype)) := by
  have he : (s.orbitFullRepresentation hb hc hab hcb hsurj).comp
      (s.projection.comp (⊤ : Subgroup M).subtype) = orbitRepresentation R c b :=
    MonoidHom.ext (s.orbitFullRepresentation_projection hb hc hab hcb hsurj)
  rw [he]
  exact orbitSection R c b (s.orbitLayer_le_orbit hb hc hab hcb)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
