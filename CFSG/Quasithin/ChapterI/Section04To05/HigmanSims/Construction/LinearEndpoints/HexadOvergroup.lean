module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.EndpointModel
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedEndpointConstruction
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.DerivedModel
public import Theory.SpecificGroups.SL2.Affine.Structure.LinearThree
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The actual alternating-six overgroup of a marked linear endpoint

The retained normalizer quotient defines a literal even preimage in the
original group. It has kernel A and quotient A6, hence order5760. The
perfect natural endpoint lies in this preimage. A marked PSL3(4) overgroup
meets the full radical normalizer in precisely its maximal parabolic:
otherwise the radical would be a nontrivial proper normal subgroup of the
simple linear group. Thus its intersection with the even preimage is the
same original endpoint. No Mathieu model or index22 premise is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "F" => Matrix.PSL3Four.F
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic F
local notation "S6" => Equiv.Perm (Fin 6)
local notation "A6" => alternatingGroup (Fin 6)

/-- The six-letter quotient uses the specified original symplectic marking. -/
@[expose] def NaturalEndpointData.six_letter_quotient (d : NaturalEndpointData A) :
    normalizer (A : Set G) →* S6 :=
  Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp
    (d.symplectic_quotient.toMonoidHom.comp
      (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G)))))

/-- The literal ambient preimage of A6 under that same quotient marking. -/
@[expose] def NaturalEndpointData.hexad_overgroup (d : NaturalEndpointData A) : Subgroup G :=
  ((A6).comap d.six_letter_quotient).map (normalizer (A : Set G)).subtype

private theorem six_surjective (d : NaturalEndpointData A) :
    Function.Surjective d.six_letter_quotient :=
  Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.surjective.comp
    (d.symplectic_quotient.surjective.comp (QuotientGroup.mk'_surjective _))

private theorem six_kernel (d : NaturalEndpointData A) :
    d.six_letter_quotient.ker = A.subgroupOf (normalizer (A : Set G)) := by
  ext g
  change Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
    (d.symplectic_quotient (QuotientGroup.mk' _ g)) = 1 ↔ _
  rw [← MulEquiv.map_one Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm,
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective.eq_iff,
    ← d.symplectic_quotient.map_one,d.symplectic_quotient.injective.eq_iff]
  exact QuotientGroup.eq_one_iff g

private theorem radical_card (d : NaturalEndpointData A) : Nat.card A = 16 := by
  rw [Nat.card_congr d.coordinates.toEquiv]
  exact (Nat.card_eq_fintype_card (α := Representation.SL2FourNatural.V)).trans
    Representation.SL2FourNatural.card_vector

private theorem endpoint_perfect (d : NaturalEndpointData A) : Group.IsPerfect d.carrier := by
  obtain ⟨_,e,_⟩ := point_parabolic_of_natural_endpoint A d.carrier d.complement
    d.kernel_le d.normalizes d.quotient d.quotient_surjective d.quotient_kernel
    d.coordinates d.action d.is_complement
  have hpoint : Point = Matrix.PSL3.LinearThree.pointLocal F := by
    rw [Matrix.PSL3.LinearThree.pointParabolic_eq_sup]
    exact sup_eq_left.mpr
      (Matrix.PSL3.CartanActions.FullTorusFixer.borel_le_pointLocal_of_card_four Matrix.PSL3Four.card_F)
  let f := e.trans (MulEquiv.subgroupCongr hpoint)
  let := Matrix.PSL3.LinearThree.pointLocal_isPerfect F (by rw [Matrix.PSL3Four.card_F])
  exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective

/-- Inside any actual marked PSL3(4) overgroup, the first endpoint is the
full normalizer of its original elementary radical. -/
theorem NaturalEndpointData.linear_three_radical_normalizer (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L)
    (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    L ⊓ normalizer (A : Set G) = d.carrier := by
  let P := d.carrier.subgroupOf L
  let R := (normalizer (A : Set G)).subgroupOf L
  have hmax : IsCoatom P := (e.mapSubgroup.isCoatom_iff P).mp (by
    change IsCoatom (P.map e.toMonoidHom)
    rw [show P.map e.toMonoidHom = Point from hmark]
    exact Matrix.PSL3.LinearThree.pointParabolic_isCoatom F)
  have hPR : P ≤ R := fun _ hx => d.normalizes hx
  have hAL : A ≤ L := d.kernel_le.trans hPL
  have hRtop : R ≠ ⊤ := by
    intro he
    have hn : L ≤ normalizer (A : Set G) := by
      intro x hx
      exact (show (⟨x,hx⟩ : L) ∈ R from he ▸ mem_top _)
    let : IsSimpleGroup Matrix.PSL3Four.PSL := Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup L := e.isSimpleGroup
    let : (A.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hn
    have hcA : Nat.card (A.subgroupOf L) = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv).trans (radical_card d)
    have hcL : Nat.card L = 20160 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL
    rcases (inferInstance : (A.subgroupOf L).Normal).eq_bot_or_eq_top with hb | ht
    · rw [hb,card_bot] at hcA
      omega
    · rw [ht,card_top,hcL] at hcA
      omega
  have hRP : R = P := (hmax.le_iff.mp hPR).resolve_left hRtop
  apply le_antisymm
  · intro x hx
    exact (show (⟨x,hx.1⟩ : L) ∈ P from hRP ▸ hx.2)
  · exact le_inf hPL d.normalizes

/-- The same quotient marking constructs an actual E16-by-A6 subgroup of
order5760 meeting the marked linear group in exactly the original endpoint.
The full quotient map, literal kernel and its evaluated equivalence remain. -/
theorem NaturalEndpointData.hexad_overgroup_structure (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L)
    (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    ∃ hDN : d.hexad_overgroup ≤ normalizer (A : Set G),
      A ≤ d.hexad_overgroup ∧ d.carrier ≤ d.hexad_overgroup ∧
      Nat.card d.hexad_overgroup = 5760 ∧ L ⊓ d.hexad_overgroup = d.carrier ∧
      ∃ π : d.hexad_overgroup →* A6, Function.Surjective π ∧
        π.ker = A.subgroupOf d.hexad_overgroup ∧
        (∀ g : d.hexad_overgroup, (π g : S6) =
          d.six_letter_quotient (inclusion hDN g)) ∧
        ∃ f : (d.hexad_overgroup ⧸ π.ker) ≃* A6,
          ∀ g : d.hexad_overgroup, f (QuotientGroup.mk g) = π g := by
  let N := normalizer (A : Set G)
  let D := d.hexad_overgroup
  let q := d.six_letter_quotient
  have hDN : D ≤ N := map_subtype_le _
  have hmem (x : N) : (x : G) ∈ D ↔ q x ∈ A6 :=
    mem_map_iff_mem N.subtype_injective
  have hPD : d.carrier ≤ D := by
    let := endpoint_perfect d
    let f : d.carrier →* ℤˣ := Equiv.Perm.sign.comp (q.comp (inclusion d.normalizes))
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    intro x hx
    apply (hmem (inclusion d.normalizes ⟨x,hx⟩)).mpr
    apply Equiv.Perm.mem_alternatingGroup.mpr
    exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict ⟨x,hx⟩) 1)
  have hAD : A ≤ D := d.kernel_le.trans hPD
  let π : D →* A6 := (q.comp (inclusion hDN)).codRestrict A6 (fun g =>
    (hmem (inclusion hDN g)).mp g.property)
  have hπ (g : D) : (π g : S6) = q (inclusion hDN g) := rfl
  have hπs : Function.Surjective π := by
    intro a
    obtain ⟨x,hx⟩ := six_surjective d (a : S6)
    have hxD : (x : G) ∈ D := (hmem x).mpr (hx ▸ a.property)
    exact ⟨⟨x,hxD⟩,Subtype.ext hx⟩
  have hk : π.ker = A.subgroupOf D := by
    ext g
    change π g = 1 ↔ (g : G) ∈ A
    rw [Subtype.ext_iff]
    change q (inclusion hDN g) = 1 ↔ (g : G) ∈ A
    have hh := SetLike.ext_iff.mp (six_kernel d) (inclusion hDN g)
    exact hh
  have hDcard : Nat.card D = 5760 := by
    have hh := π.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr hπs,card_top,hk,
      Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv,radical_card d,
      nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    exact hh.symm
  have hi : L ⊓ D = d.carrier := le_antisymm
    ((inf_le_inf le_rfl hDN).trans (d.linear_three_radical_normalizer L hPL e hmark).le)
    (le_inf hPL hPD)
  refine ⟨hDN,hAD,hPD,hDcard,hi,π,hπs,hk,hπ,
    QuotientGroup.quotientKerEquivOfSurjective π hπs,?_⟩
  intro g
  rfl

end CFSG.Quasithin.HigmanSims
