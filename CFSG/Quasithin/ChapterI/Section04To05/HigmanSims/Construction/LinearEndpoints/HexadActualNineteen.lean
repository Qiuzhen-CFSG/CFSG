module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.QuotientAmalgamRelationsConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadAffineCoordinates
public import Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadActualNineteen.Assembly

/-!
# Actual word 19 on the same original TypeAt tuple

The original paired radicals supply the proved affine coordinates. Their
quotient is identified pointwise with the unchanged quotient of the original
marked tuple. The same selected cubic now satisfies actual word 19.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetWordCertificate
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

/-- The same original tuple and same cubic choice satisfy twenty-one actual
relations, together with all seven previously established quotient words. -/
theorem TypeAt.exists_original_twentyone_and_quotient_relators (h : TypeAt z V) :
    ∃ (W A B : Subgroup G) (u c t : G) (hAE : IsElementaryAbelian 2 A)
      (hBE : IsElementaryAbelian 2 B), letI := hAE; letI := hBE
      W ≤ V ∧ Nat.card W = 4 ∧ Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A ≤ normalizer (B : Set G) ∧ B ≤ normalizer (A : Set G) ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ B = W ∧ ⁅A, B⁆ ≤ W ∧ Nat.card (A ⊔ B : Subgroup G) = 64 ∧
      A ⊔ B ≤ centralizer (W : Set G) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧ (∀ x ∈ B, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ B, x ≠ 1 → Nat.card (B ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      u ∈ V ∧ u ≠ 1 ∧ u ∉ W ∧ TypeAt u V ∧
      V ⊓ centralizer ({t} : Set G) = zpowers u ∧
      c ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ c ^ 2 = u ∧ orderOf c = 4 ∧ Commute c t ∧
      (normalizer (V : Set G)).pCoreIn 2 ⊓ centralizer ({t} : Set G) = zpowers c ∧
      B = A.map (MulAut.conj c).toMonoidHom ∧ A = B.map (MulAut.conj c).toMonoidHom ∧
      orderOf t = 3 ∧ t ∈ normalizer (W : Set G) ∧
      Disjoint (A ⊔ B) (zpowers t) ∧
      ∃ (d : NaturalEndpointData A) (hBA : B ≤ normalizer (A : Set G)),
        Representation.SL2FourNatural.BorelFactors.U0.map d.embedding =
          ((d.symplectic_quotient.toMonoidHom.comp
            (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))).comp
              (inclusion hBA)).range ∧
        let P₂ := d.carrier.map (MulAut.conj c).toMonoidHom
        let J := (A ⊔ B) ⊔ zpowers t
        B ≤ d.carrier ∧ A ≤ P₂ ∧ B ≤ P₂ ∧ t ∈ d.carrier ⊓ P₂ ∧
        P₂ ≤ normalizer (B : Set G) ∧ Nat.card P₂ = 960 ∧
        d.carrier ⊓ P₂ = J ∧ Nat.card J = 192 ∧ c ∈ normalizer (J : Set G) ∧
        d.carrier.pCoreIn 2 = A ∧ P₂.pCoreIn 2 = B ∧
        ∃ (e₁ : d.carrier ≃* Point) (e₂ : P₂ ≃* Point) (k : d.carrier ≃* P₂),
          (A.subgroupOf d.carrier).map e₁.toMonoidHom = pCore 2 Point ∧
          (B.subgroupOf P₂).map e₂.toMonoidHom = pCore 2 Point ∧
          (∀ x, (k x : G) = c * (x : G) * c⁻¹) ∧ (∀ x, e₂ (k x) = e₁ x) ∧
          ∃ r s : G, r ∈ d.carrier ∧ s ∈ P₂ ∧ s = c * r * c⁻¹ ∧
            r ∉ J ∧ s ∉ J ∧ orderOf r = 2 ∧ orderOf s = 2 ∧
            r * t * r⁻¹ = t⁻¹ ∧ s * t * s⁻¹ = t⁻¹ ∧
            r * s ∈ centralizer ({t} : Set G) ∧ r * s ≠ 1 ∧ orderOf (r*s)=3 ∧
            ∃ marking : RankTwoAmalgam.Iso
              (RankTwoAmalgam.ofSubgroups d.carrier (d.carrier⊓P₂) P₂ inf_le_left inf_le_right)
              (ChapterF.GreenBook.LieModels.LinearThree.amalgam Matrix.PSL3Four.F),
              (A.subgroupOf d.carrier).map marking.left.toMonoidHom = pCore 2 Point ∧
              (B.subgroupOf P₂).map marking.right.toMonoidHom = pCore 2
                (Matrix.PSL3.LinearThree.lineParabolic Matrix.PSL3Four.F) ∧
              (d.carrier⊔P₂:Subgroup G)≠⊤ ∧
              ∃ e : (d.carrier⊔P₂:Subgroup G)≃*Matrix.PSL3Four.PSL,
                (d.carrier.subgroupOf (d.carrier⊔P₂)).map e.toMonoidHom = Point ∧
                (P₂.subgroupOf (d.carrier⊔P₂)).map e.toMonoidHom =
                  Matrix.PSL3.LinearThree.lineParabolic Matrix.PSL3Four.F ∧
                ∃ (hrL : r∈(d.carrier⊔P₂:Subgroup G)) (hsL : s∈(d.carrier⊔P₂:Subgroup G)),
                  e ⟨r,hrL⟩=Matrix.PSL3.SmallCompletion.reflection Matrix.PSL3Four.F false ∧
                  e ⟨s,hsL⟩=Matrix.PSL3.SmallCompletion.reflection Matrix.PSL3Four.F true ∧
                  ∃ pair : Fin 2→G, closure (Set.range pair)=d.carrier ∧
                    ∃ hmem : ∀ i,pair i∈d.carrier,
                    (∀ i,pair i=(e.symm (Matrix.PSL3Four.MathieuAmalgamMarking.pair i):G)) ∧
                    Subgroup.CosetWordCertificate.eval pair
                      Matrix.PSL3Four.MathieuAmalgamMarking.reflectionWord=r ∧
                    zpowers (Subgroup.CosetWordCertificate.eval pair
                      Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)=zpowers t ∧
                    ∃ hDN : d.hexad_overgroup≤normalizer (A:Set G),
                      ∃ π : d.hexad_overgroup→*alternatingGroup (Fin 6), Function.Surjective π ∧
                        ∃ hπker : π.ker=A.subgroupOf d.hexad_overgroup,
                        (∀ g : d.hexad_overgroup, (π g:Equiv.Perm (Fin 6))=
                          d.six_letter_quotient (inclusion hDN g)) ∧
                        ∃ kA : π.ker≃*Multiplicative Theory.SpecificGroups.SymmetricSix.NaturalModule,
                          (∀ a : π.ker, (kA a).toAdd=d.binary_coordinates
                            (Additive.ofMul ⟨((a:d.hexad_overgroup):G), by
                              exact (show (a:d.hexad_overgroup)∈A.subgroupOf d.hexad_overgroup
                                from hπker ▸ a.property)⟩)) ∧
                          (∀ (g : d.hexad_overgroup) (a : π.ker),
                            kA (MulAut.conjNormal g a)=Multiplicative.ofAdd
                              (Theory.SpecificGroups.SymmetricSix.polarAction (π g).val (kA a).toAdd)) ∧
                          ∃ (n : G) (hnD : n∈d.hexad_overgroup), n∉d.carrier ∧ Commute n t ∧
                            orderOf n=3 ∧ n∉zpowers t ∧ r*n*r⁻¹=n⁻¹ ∧ ⁅r*s,n⁆^2=1 ∧
                            d.carrier⊔zpowers (r*s)=d.carrier⊔P₂ ∧
                            d.carrier⊔zpowers n=d.hexad_overgroup ∧
                            ∃ hPD : d.carrier≤d.hexad_overgroup,
                              let pD : Fin 2→d.hexad_overgroup := fun i => ⟨pair i,hPD (by
                                exact hmem i)⟩
                              ∃ b : Bool, ∃ j : Fin 3,
                                let m := (if b then (⟨n,hnD⟩ : d.hexad_overgroup)
                                  else ⟨n,hnD⟩⁻¹) *
                                  (Subgroup.CosetWordCertificate.eval pD
                                    Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)^j.val
                                (∀ i : Fin 27, (i.val<17 ∨ i=19 ∨ i=23 ∨ i=25 ∨ i=26) →
                                  Subgroup.CosetWordCertificate.eval ![pair 0,pair 1,r*s,(m:G)]
                                    (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1) ∧
                                ∀ ell : d.hexad_overgroup, ∀ i : Fin 27,
                                  (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
                                  π (Subgroup.CosetWordCertificate.eval ![pD 0,pD 1,ell,m]
                                    (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i))=1 := by
  exact assemble_actual19 h (h.exists_original_twenty_and_quotient_relators)

end CFSG.Quasithin.HigmanSims
