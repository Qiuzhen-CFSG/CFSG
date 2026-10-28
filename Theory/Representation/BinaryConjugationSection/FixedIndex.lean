module
public import Theory.Representation.BinaryConjugationSection.FixedImage
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Fixed indices in a literal binary conjugation section

The image of the commutator preimage is exactly the fixed space of the
specified actor. The coordinate kernel lies in this preimage, so the original
relative index equals two to the fixed codimension. The image-actor version
keeps the original surjective coordinate map and the actual actor homomorphism.

Source application: Meierfrankenfeld--Stellmacher (1993), (3.6), p.871.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H U Z : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V}
  (d : BinaryConjugationSection H U Z ρ)

theorem fixed_image_eq (A : Subgroup G) (hAH : A ≤ H)
    (hn : U ≤ normalizer (Z : Set G)) :
    d.imageSpace (commutatorPreimage U A Z) = fixedSpace ρ (A.subgroupOf H) := by
  let C := commutatorPreimage U A Z
  apply le_antisymm
  · intro v hv a
    apply d.fixed_on_imageSpace_of_commutator_le A C
      (by rw [commutator_comm]; exact commutator_commutatorPreimage_le U A Z hn)
      a.val a.property v hv
  · intro v hv
    obtain ⟨u,hu⟩ := d.onto (Multiplicative.ofAdd v)
    let F : Subgroup (Multiplicative V) :=
      AddSubgroup.toSubgroup' (fixedSpace ρ (A.subgroupOf H)).toAddSubgroup
    let P : Subgroup G := (F.comap d.coordinates).map U.subtype
    have hP : d.imageSpace P ≤ fixedSpace ρ (A.subgroupOf H) := by
      intro w hw
      obtain ⟨x,⟨y,hy,he⟩,hw⟩ := (d.mem_imageSpace_iff P w).mp hw
      have hyx : y = x := Subtype.ext he
      subst y
      change (d.coordinates x).toAdd ∈ fixedSpace ρ (A.subgroupOf H) at hy
      exact hw ▸ hy
    have hcomm : ⁅P,A⁆ ≤ Z := by
      rw [commutator_comm]
      exact d.commutator_le_of_imageSpace_fixed A P hAH (map_subtype_le _) hP
    have huP : (u : G) ∈ P := by
      refine ⟨u,?_,rfl⟩
      change (d.coordinates u).toAdd ∈ fixedSpace ρ (A.subgroupOf H)
      rw [hu]
      exact hv
    have huC : (u : G) ∈ C := le_commutatorPreimage (map_subtype_le _) hcomm huP
    exact (d.mem_imageSpace_iff C v).mpr ⟨u,huC,congrArg Multiplicative.toAdd hu⟩

include d in
theorem fixed_index [Finite U] [Z.Normal] (A : Subgroup G) (hAH : A ≤ H) :
    (commutatorPreimage U A Z).relIndex U =
      2 ^ fixedCodim ρ (A.subgroupOf H) := by
  let : Finite V := Finite.of_surjective (fun u : U => (d.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  let C := commutatorPreimage U A Z
  let F : Subgroup (Multiplicative V) :=
    AddSubgroup.toSubgroup' (fixedSpace ρ (A.subgroupOf H)).toAddSubgroup
  have hm : (C.subgroupOf U).map d.coordinates = F := by
    ext v
    change v.toAdd ∈ d.imageSpace C ↔ v.toAdd ∈ fixedSpace ρ (A.subgroupOf H)
    rw [d.fixed_image_eq A hAH le_normalizer_of_normal]
  have hz : Z ≤ C := le_commutatorPreimage d.kernel_le (commutator_le_left Z A)
  have hk : d.coordinates.ker ≤ C.subgroupOf U := by
    rw [d.kernel_eq]
    exact comap_mono hz
  have hi : F.index = C.relIndex U := by
    rw [←hm,index_map_eq _ d.onto hk]
    rfl
  have hc := F.card_mul_index
  have hF : Nat.card F = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (A.subgroupOf H)) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ (A.subgroupOf H))).trans (by rw [Nat.card_zmod])
  have hV : Nat.card (Multiplicative V) = 2 ^ Module.finrank (ZMod 2) V := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)).trans
      (by rw [Nat.card_zmod])
  rw [hF,hV,←fixedCodim_add_finrank ρ (A.subgroupOf H),add_comm,pow_add] at hc
  exact hi.symm.trans (Nat.eq_of_mul_eq_mul_left (by positivity) hc)

theorem fixed_index_image [Finite U] [Z.Normal]
    {D : Type*} [Group D] (σ : Representation (ZMod 2) D V) (π : H →* D)
    (d : BinaryConjugationSection H U Z (σ.comp π))
    (A : Subgroup G) (hAH : A ≤ H) :
    (commutatorPreimage U A Z).relIndex U =
      2 ^ fixedCodim σ ((A.subgroupOf H).map π) := by
  rw [d.fixed_index A hAH]
  unfold fixedCodim
  rw [fixedSpace_comp_map]

end Representation.BinaryConjugationSection
