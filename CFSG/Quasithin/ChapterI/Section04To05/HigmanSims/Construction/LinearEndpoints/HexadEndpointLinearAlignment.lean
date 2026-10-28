module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates

/-!
# Simultaneous linear alignment of the actual endpoint and hexad quotient

The same original endpoint quotient embeds in the literal hexad A₆ quotient.
Its composite on every endpoint element is the original hexad quotient, and
its polar matrices are exactly the specified natural symplectic embedding.
The original binary and field coordinates therefore intertwine the same
restricted action; no complement or affine cocycle is changed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Matrix
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F
local notation "A6" => alternatingGroup (Fin 6)
local notation "SL" => Representation.SL2FourNatural.SL
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule

/-- The original A₅ endpoint and hexad A₆ quotient have simultaneous literal
linear markings, including the unchanged quotient on every endpoint element. -/
theorem NaturalEndpointData.hexad_endpoint_linear_alignment (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier≤L) (e : L≃*Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom=Point) :
    ∃ (hDN : d.hexad_overgroup≤normalizer (A:Set G))
      (hPD : d.carrier≤d.hexad_overgroup),
      ∃ q : d.hexad_overgroup→*A6, Function.Surjective q ∧
        q.ker=A.subgroupOf d.hexad_overgroup ∧
        (∀ g : d.hexad_overgroup, (q g:Equiv.Perm (Fin 6))=
          d.six_letter_quotient (inclusion hDN g)) ∧
        ∃ ι : SL→*A6, Function.Injective ι ∧
          (∀ g : d.carrier, q (inclusion hPD g)=ι (d.quotient g)) ∧
          (∀ g : SL, Theory.SpecificGroups.SymmetricSix.polarRepresentation (ι g).val=
            d.embedding g) ∧
          ∀ (g : SL) (v : Vec),
            d.field_coordinates.symm (Theory.SpecificGroups.SymmetricSix.polarAction (ι g).val v)=
              Representation.SL2FourNatural.action g (d.field_coordinates.symm v) := by
  obtain ⟨hDN,_,hPD,_,_,q,hq,hker,hqmark,_⟩ :=
    d.hexad_overgroup_structure L hPL e hmark
  let f : d.carrier→*A6 := q.comp (inclusion hPD)
  have hkf : f.ker=d.quotient.ker := by
    rw [d.quotient_kernel]
    ext g
    change q (inclusion hPD g)=1 ↔ (g:G)∈A
    change inclusion hPD g∈q.ker ↔ _
    rw [hker]
    rfl
  let ι : SL→*A6 := d.quotient.liftOfSurjective d.quotient_surjective ⟨f,hkf.symm.le⟩
  have hι (g : d.carrier) : ι (d.quotient g)=f g :=
    d.quotient.liftOfRightInverse_comp_apply _ _ _ g
  have hi : Function.Injective ι := by
    apply (MonoidHom.ker_eq_bot_iff ι).mp
    apply bot_unique
    intro x hx
    obtain ⟨g,rfl⟩ := d.quotient_surjective x
    have hg : g∈f.ker := (hι g).symm.trans hx
    have hqg : g∈d.quotient.ker := hkf ▸ hg
    exact hqg
  have hmatrix (x : SL) :
      Theory.SpecificGroups.SymmetricSix.polarRepresentation (ι x).val=d.embedding x := by
    obtain ⟨g,rfl⟩ := d.quotient_surjective x
    rw [hι]
    change Theory.SpecificGroups.SymmetricSix.polarRepresentation (q (inclusion hPD g)).val=_
    rw [hqmark,←Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply]
    change Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv
      (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
        (d.symplectic_quotient (QuotientGroup.mk (inclusion hDN (inclusion hPD g)))))=_
    rw [MulEquiv.apply_symm_apply,d.quotient_marking]
    rfl
  refine ⟨hDN,hPD,q,hq,hker,hqmark,ι,hi,fun g => (hι g).symm,hmatrix,?_⟩
  intro g v
  apply d.field_coordinates.injective
  rw [LinearEquiv.apply_symm_apply,←d.embedding_action,LinearEquiv.apply_symm_apply]
  rw [←hmatrix,Theory.SpecificGroups.SymmetricSix.polarRepresentation_apply]

end CFSG.Quasithin.HigmanSims
