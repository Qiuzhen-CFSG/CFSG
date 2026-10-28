module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.Marking
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Action

/-!
# Moving spaces in the original natural action

The natural coordinates identify the actual subgroup commutator [V,A]
with the displacement space of the literal permutation image of A.
The inverse subspace construction retains the subgroup embedding in G.
This connects the native cubic planes to their original lifted actors;
no faithfulness or a new choice of natural module is assumed.

Source: Aschbacher–Smith 13.5.6, printed p.917.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)

noncomputable def realize (W : Submodule (ZMod 2) (natural (Fin 6))) : Subgroup G :=
  (W.toAddSubgroup.toSubgroup.comap d.coordinate.toMonoidHom).map V.subtype

theorem realize_le (W) : realize d W ≤ V := map_subtype_le _

theorem image_realize (W) : image d (realize d W) = W := by
  ext w
  constructor
  · rintro ⟨v,⟨u,hu,he⟩,rfl⟩
    have he' : u=v := Subtype.ext he
    change (d.coordinate u).toAdd ∈ W at hu
    exact he' ▸ hu
  · intro hw
    obtain ⟨v,hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    refine ⟨v,⟨v,?_,rfl⟩,hv⟩
    change (d.coordinate v).toAdd ∈ W
    rw [hv]
    exact hw

theorem image_module : image d V = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨v,hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
  exact ⟨v,v.property,hv⟩

noncomputable def actor (A:Subgroup G) (hA:A≤L⊔(T:Subgroup G)) :
    A →* Equiv.Perm (Fin 6) :=
  (permutation d).comp (inclusion hA)

private theorem commutator_coordinate (A:Subgroup G) (hA:A≤L⊔(T:Subgroup G))
    (a:A) (v:V) : ∃c:V, c.val=⁅(a:G),(v:G)⁆ ∧
      (d.coordinate c).toAdd = naturalRepresentation (Fin 6) (actor d A hA a)
        (d.coordinate v).toAdd-(d.coordinate v).toAdd := by
  let c := V.normalizerMonoidHom ⟨a.val,d.normalizes_V (hA a.property)⟩ v*v⁻¹
  refine ⟨c,rfl,?_⟩
  change (d.coordinate (V.normalizerMonoidHom _ v*v⁻¹)).toAdd=_
  rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg,
    conjugation d ⟨a.val,hA a.property⟩ v]
  rfl

theorem image_commutator (A:Subgroup G) (hA:A≤L⊔(T:Subgroup G)) :
    image d ⁅V,A⁆ = NondegeneratePlane.movedSpace (actor d A hA).range := by
  let D := NondegeneratePlane.movedSpace (actor d A hA).range
  have hc : ⁅V,A⁆≤realize d D := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha v hv
    obtain ⟨c,he,hd⟩ := commutator_coordinate d A hA ⟨a,ha⟩ ⟨v,hv⟩
    refine ⟨c,?_,he⟩
    change (d.coordinate c).toAdd∈D
    rw [hd]
    exact Representation.Coinvariants.sub_mem_ker
      (ρ := (naturalRepresentation (Fin 6)).comp (actor d A hA).range.subtype)
      ⟨actor d A hA ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩ _
  apply le_antisymm
  · rintro w ⟨v,hv,rfl⟩
    obtain ⟨u,hu,he⟩ := hc hv
    have he' : u=v := Subtype.ext he
    change (d.coordinate u).toAdd∈D at hu
    exact he' ▸ hu
  · apply Submodule.span_le.mpr
    rintro w ⟨⟨a,v⟩,rfl⟩
    obtain ⟨x,hx⟩ := a.property
    obtain ⟨u,hu⟩ := d.coordinate.surjective (Multiplicative.ofAdd v)
    obtain ⟨c,he,hd⟩ := commutator_coordinate d A hA x u
    apply (mem_image d ⁅V,A⁆ _).mpr
    refine ⟨c,?_,?_⟩
    · rw [he,commutator_comm]
      exact commutator_mem_commutator x.property u.property
    · rw [hd,hu]
      change naturalRepresentation (Fin 6) (actor d A hA x) v-v=_
      rw [hx]
      rfl
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
