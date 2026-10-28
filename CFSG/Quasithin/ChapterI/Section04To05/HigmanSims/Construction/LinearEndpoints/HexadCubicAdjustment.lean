module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.NormalizerCubicCentralizer
public import Theory.SpecificGroups.SymmetricSix.PolarAffine.CubicQuadraticAdjustment

/-!
# The original hexad adjustment fixes the specified cubic normalizer

The original endpoint action proves that the chosen cubic has trivial
centralizer in the whole original radical. Thus the normalized quadratic
adjustment fixes its full normalizer in the original hexad group, while
retaining the same quotient and all original binary kernel coordinates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F
local notation "A6" => alternatingGroup (Fin 6)
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule

/-- The actual cubic and its whole hexad normalizer can remain fixed under
a nonprincipal adjustment of the same original full-kernel extension. -/
theorem NaturalEndpointData.hexad_cubic_adjustment (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier≤L) (e : L≃*Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom=Point)
    (t : G) (ht : t∈d.carrier) (ht3 : orderOf t=3) :
    ∃ (hDN : d.hexad_overgroup≤normalizer (A:Set G))
      (hPD : d.carrier≤d.hexad_overgroup),
      ∃ q : d.hexad_overgroup→*A6, Function.Surjective q ∧
        ∃ hqker : q.ker=A.subgroupOf d.hexad_overgroup,
        (∀ g : d.hexad_overgroup, (q g:Equiv.Perm (Fin 6))=
          d.six_letter_quotient (inclusion hDN g)) ∧
        ∃ k : q.ker≃*Multiplicative Vec,
          (∀ a : q.ker, (k a).toAdd=d.binary_coordinates
            (Additive.ofMul ⟨((a:d.hexad_overgroup):G), by
              exact (show (a:d.hexad_overgroup)∈A.subgroupOf d.hexad_overgroup
                from hqker ▸ a.property)⟩)) ∧
          (∀ (g : d.hexad_overgroup) (a : q.ker),
            k (MulAut.conjNormal g a)=Multiplicative.ofAdd
              (Theory.SpecificGroups.SymmetricSix.polarAction (q g).val (k a).toAdd)) ∧
          let T : d.hexad_overgroup := ⟨t,hPD ht⟩
          ∃ β : MulAut d.hexad_overgroup,
            (∀ g, q (β g)=q g) ∧
            (∀ a : q.ker, β a=(a:d.hexad_overgroup)) ∧ β T=T ∧
            (∀ g∈normalizer (zpowers T : Set d.hexad_overgroup),β g=g) ∧
            (∀ g, β (β g)=g) ∧
            ¬ ∃ a : q.ker, ∀ g, β g=(a:d.hexad_overgroup)⁻¹*g*a := by
  obtain ⟨_,_,hPD,_⟩ := d.hexad_overgroup_structure L hPL e hmark
  obtain ⟨hDN,q,hq,hqker,hqmark,k,hk,hact⟩ :=
    d.hexad_kernel_coordinates L hPL e hmark
  let T : d.hexad_overgroup := ⟨t,hPD ht⟩
  have hT3 : orderOf T=3 := (orderOf_coe T).symm.trans ht3
  have hct (a : q.ker) (ha : Commute (a:d.hexad_overgroup) T) : a=1 := by
    have haA : ((a:d.hexad_overgroup):G)∈A :=
      show (a:d.hexad_overgroup)∈A.subgroupOf d.hexad_overgroup from hqker ▸ a.property
    have hac : ((a:d.hexad_overgroup):G)∈centralizer ({t}:Set G) :=
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val ha.eq)
    have hz : ((a:d.hexad_overgroup):G)∈(⊥:Subgroup G) :=
      d.cubic_radical_centralizer t ht ht3 ▸ (show ((a:d.hexad_overgroup):G)∈
        A⊓centralizer ({t}:Set G) from ⟨haA,hac⟩)
    exact Subtype.ext (Subtype.ext (mem_bot.mp hz))
  obtain ⟨β,hβq,hβk,hβt,hβN,hβ2,_,hβni⟩ :=
    Theory.SpecificGroups.SymmetricSix.PolarAffine.exists_cubic_normalized_quadratic_automorphism
      q hq k hact T hT3 hct
  exact ⟨hDN,hPD,q,hq,hqker,hqmark,k,hk,hact,β,hβq,hβk,hβt,hβN,hβ2,hβni⟩

end CFSG.Quasithin.HigmanSims
