module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.StandardLinearThreeConstruction
public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.MarkedTransport
public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.SharedHexadRelations
public import Theory.SpecificGroups.MathieuAmalgamCompletion.MixedRelation
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCubicRelation
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadGenerators
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.EndpointCubicCentralizer

/-!
# Nineteen exact relations on the same original four generators

The actual TypeAt construction supplies the original endpoint pair, the
literal reflection product and the original exterior hexad cubic. The full
hexad quotient and its polar kernel marking are retained. The thirteen
linear words, the hexad cubic word, four shared endpoint words and the mixed
commutator word hold simultaneously. Eight hexad cross-relations remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

/-- The complete original tuple supplies nineteen exact local-amalgam
relations on one pair and the same two original exterior cubics, retaining
the full hexad quotient and every polar-kernel coordinate. -/
theorem TypeAt.exists_original_partial_amalgam_relators (h : TypeAt z V) :
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
                            ∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=26) →
                              Subgroup.CosetWordCertificate.eval ![pair 0,pair 1,r*s,n]
                                (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1 := by
  obtain ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright,hrL,hsL,her,hes⟩ :=
    h.exists_original_standard_linearThree_subgroup
  let := hAE
  let := hBE
  let P₂ := d.carrier.map (MulAut.conj c).toMonoidHom
  let L := d.carrier⊔P₂
  have hell : r*s∈L := L.mul_mem hrL hsL
  have he : e ⟨r*s,hell⟩=Matrix.PSL3Four.MathieuAmalgamMarking.cycle := by
    change e ((⟨r,hrL⟩:L)*⟨s,hsL⟩)=_
    rw [map_mul,her,hes,Matrix.PSL3Four.MathieuAmalgamMarking.cycle_eq_reflections]
  have her' : e ⟨r,hrL⟩=Matrix.PSL3Four.MathieuAmalgamMarking.reflection :=
    her.trans Matrix.PSL3Four.MathieuAmalgamMarking.reflection_eq_standard.symm
  obtain ⟨pair,hpair,hmem,hpairmark,hwordr,hwordt,hrel⟩ :=
    Matrix.PSL3Four.MathieuAmalgamMarking.exists_original_marked_linear_relators
      d.carrier L le_sup_left e hleft (r*s) r t hell hrL htd.1 he her' ht3
        (show Commute t (r*s) from (mem_centralizer_singleton_iff.mp hrs).symm)
  obtain ⟨hDN,π,hπs,hπker,hπmark,kA,hkA,hkact⟩ :=
    d.hexad_kernel_coordinates L le_sup_left e hleft
  obtain ⟨n,hnD,hnt,hn3,hnT,hrn,_,hcross⟩ :=
    h.exists_hexad_cubic_cross_relation W A B hWV hW4 hA16 hB16 hAP hBP hC
      hBA d hBd h64 hpureB hpointsB u c t r huV huW hcP hc2 hc4 hct hBc
        ht3 htW h192 htd.1 hr hrJ hr2 hrt
  have hcross' : ⁅r*s,n⁆^2=1 := by simpa only [hsc] using hcross
  have hnP : n∉d.carrier := by
    intro hnP
    apply hnT
    rw [←d.cubic_endpoint_centralizer t htd.1 ht3]
    exact ⟨hnP,mem_centralizer_singleton_iff.mpr hnt.eq⟩
  have hellP : r*s∉d.carrier := by
    intro hh
    apply hsJ
    rw [←hinter]
    refine ⟨?_,hs⟩
    have hm := d.carrier.mul_mem (d.carrier.inv_mem hr) hh
    change s∈d.carrier
    simpa only [inv_mul_cancel_left] using hm
  obtain ⟨hLgen,hDgen,_⟩ := d.exterior_elements_generate_overgroups
    L le_sup_left e hleft (r*s) n hell hellP hnD hnP
  have hrelations (i : Fin 27) (hi : i.val<17 ∨ i=23 ∨ i=26) :
      Subgroup.CosetWordCertificate.eval ![pair 0,pair 1,r*s,n]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1 := by
    by_cases hfirst : i.val<13
    · exact hrel n ⟨i.val,hfirst⟩
    by_cases h13 : i=13
    · subst i
      have hh : n^3=1 := hn3 ▸ pow_orderOf_eq_one n
      simpa [Theory.SpecificGroups.MathieuAmalgamCompletion.relator,
        Theory.SpecificGroups.MathieuAmalgamCompletion.decode,
        Subgroup.CosetWordCertificate.eval,FreeGroup.lift_mk,pow_succ,mul_assoc] using hh
    by_cases h26 : i=26
    · subst i
      apply Theory.SpecificGroups.MathieuAmalgamCompletion.mixed_relator_of_commutator_square
      exact hcross'
    have hshared : i=14 ∨ i=15 ∨ i=16 ∨ i=23 := by
      rcases hi with hi | hi | hi
      · have hne : i.val≠13 := by intro hh; apply h13; exact Fin.ext hh
        have hcases : i.val=14 ∨ i.val=15 ∨ i.val=16 := by omega
        rcases hcases with hh | hh | hh
        · exact Or.inl (Fin.ext hh)
        · exact Or.inr (Or.inl (Fin.ext hh))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext hh)))
      · exact Or.inr (Or.inr (Or.inr hi))
      · exact (h26 hi).elim
    rw [hpairmark 0,hpairmark 1]
    exact Matrix.PSL3Four.MathieuAmalgamMarking.mapped_shared_hexad_relators
      (L.subtype.comp e.symm.toMonoidHom) (r*s) n i hshared
  exact ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright,hrL,hsL,her,hes,pair,hpair,hmem,hpairmark,hwordr,hwordt,hDN,π,hπs,hπker,hπmark,kA,hkA,hkact,
    n,hnD,hnP,hnt,hn3,hnT,hrn,hcross',hLgen,hDgen,hrelations⟩

end CFSG.Quasithin.HigmanSims
