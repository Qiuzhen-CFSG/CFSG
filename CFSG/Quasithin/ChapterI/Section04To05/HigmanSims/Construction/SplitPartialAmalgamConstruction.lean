module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.StandardLinearThreeConstruction
public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.MarkedTransport
public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.SharedHexadRelations
public import Theory.SpecificGroups.MathieuAmalgamCompletion.MixedRelation
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCubicRelation
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadGenerators
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.EndpointCubicCentralizer

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PartialAmalgamRelationsConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadSplitting

/-!
# The original nineteen-relator tuple with its proved full hexad complement

All original subgroups, points, quotient maps, coordinates and four generator
values are retained. The paired radical geometry supplies a complement to
the actual full hexad kernel; its map to A₆ is the same quotient already
present in the original tuple. No compatibility with the endpoint complement
or the remaining eight cross-relations is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

/-- Original TypeAt supplies the same nineteen relations together with
a complement to the full original hexad kernel, marked by the retained map. -/
theorem TypeAt.exists_original_split_partial_amalgam_relators (h : TypeAt z V) :
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
                    (∀ i,pair i∈d.carrier) ∧
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
                          ∃ n : G, n∈d.hexad_overgroup ∧ n∉d.carrier ∧ Commute n t ∧
                            orderOf n=3 ∧ n∉zpowers t ∧ r*n*r⁻¹=n⁻¹ ∧ ⁅r*s,n⁆^2=1 ∧
                            d.carrier⊔zpowers (r*s)=d.carrier⊔P₂ ∧
                            d.carrier⊔zpowers n=d.hexad_overgroup ∧
                            (∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=26) →
                              Subgroup.CosetWordCertificate.eval ![pair 0,pair 1,r*s,n]
                                (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1) ∧
                            ∃ K : Subgroup d.hexad_overgroup, π.ker.IsComplement' K ∧
                              ∃ k : K≃*alternatingGroup (Fin 6),∀ g : K,k g=π g := by
  obtain ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright,hrL,hsL,her,hes,pair,hpair,hmem,hpairmark,
    hwordr,hwordt,hDN,π,hπs,hπker,hπmark,kA,hkA,hkact,
    n,hnD,hnP,hnt,hn3,hnT,hrn,hcross,hLgen,hDgen,hrelations⟩ :=
      h.exists_original_partial_amalgam_relators
  let := hAE
  let := hBE
  let P₂ := d.carrier.map (MulAut.conj c).toMonoidHom
  let L := d.carrier⊔P₂
  have hWA : W≤A := hAP ▸ (show A⊓(normalizer (V:Set G)).pCoreIn 2≤A from inf_le_left)
  have hAC : A≤centralizer (W:Set G) := le_sup_left.trans hC
  obtain ⟨hDN',q,hq,hker,hqmark,K,hK,f,hf⟩ := h.hexad_kernel_complement
    W A B hWV hW4 hWA hAC hAP c hcP (by rwa [hc2]) hBc hi d hBd
      L le_sup_left e hleft hB16
  have heq : q=π := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    exact (hqmark g).trans (hπmark g).symm
  have hK' : π.ker.IsComplement' K := heq ▸ hK
  have hf' (g : K) : f g=π g := by rw [hf,heq]
  exact ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright,hrL,hsL,her,hes,pair,hpair,hmem,hpairmark,
    hwordr,hwordt,hDN,π,hπs,hπker,hπmark,kA,hkA,hkact,
    n,hnD,hnP,hnt,hn3,hnT,hrn,hcross,hLgen,hDgen,hrelations,K,hK',f,hf'⟩

end CFSG.Quasithin.HigmanSims
