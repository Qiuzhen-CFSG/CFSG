module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PartialAmalgamRelationsConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadQuotientTransport

/-!
# Twenty actual words and seven quotient words on one original tuple

The complete TypeAt source supplies the arbitrary original pair and its full
hexad quotient. The native marked-pair conjugacy calculation chooses a single
literal exterior cubic variant. This source retains all nineteen accepted
words, adds actual word 25 and proves the remaining seven quotient words for
that very same choice. No source defect-centralizer hypothesis is added.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetWordCertificate
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

omit [Finite G] in
private theorem eval_hom_transport {H α : Type*} [Group H]
    (f : H→*G) (p : α→H) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

/-- The unchanged full original TypeAt tuple supports twenty actual relations
and all seven remaining quotient relations for one and the same cubic choice. -/
theorem TypeAt.exists_original_twenty_and_quotient_relators (h : TypeAt z V) :
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
                                (∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=25 ∨ i=26) →
                                  Subgroup.CosetWordCertificate.eval ![pair 0,pair 1,r*s,(m:G)]
                                    (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1) ∧
                                ∀ ell : d.hexad_overgroup, ∀ i : Fin 27,
                                  (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
                                  π (Subgroup.CosetWordCertificate.eval ![pD 0,pD 1,ell,m]
                                    (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i))=1 := by
  obtain ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright,hrL,hsL,her,hes,
    pair,hpair,hmem,hpairmark,hwordr,hwordt,hDN,π,hπs,hπker,hπmark,kA,hkA,hkact,
    n,hnD,hnP,hnt,hn3,hnT,hrn,hcross,hLgen,hDgen,hrelations⟩ :=
    h.exists_original_partial_amalgam_relators
  let := hAE
  let := hBE
  let P₂ := d.carrier.map (MulAut.conj c).toMonoidHom
  let L := d.carrier⊔P₂
  obtain ⟨_,_,hPD,_⟩ := d.hexad_overgroup_structure L le_sup_left e hleft
  let p : Fin 2→d.carrier := fun i => ⟨pair i,hmem i⟩
  have hpmark (i : Fin 2) : e (inclusion (show d.carrier≤L from le_sup_left) (p i)) =
      Matrix.PSL3Four.MathieuAmalgamMarking.pair i := by
    have hp : inclusion (show d.carrier≤L from le_sup_left) (p i) =
        e.symm (Matrix.PSL3Four.MathieuAmalgamMarking.pair i) := Subtype.ext (hpairmark i)
    rw [hp,e.apply_symm_apply]
  have htorus : ((eval p Matrix.PSL3Four.MathieuAmalgamMarking.torusWord : d.carrier) : G) =
      eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord :=
    by simpa only [p,Subgroup.subtype_apply] using
      eval_hom_transport d.carrier.subtype p Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
  have hline : zpowers (eval p Matrix.PSL3Four.MathieuAmalgamMarking.torusWord) =
      zpowers (⟨t,htd.1⟩ : d.carrier) := by
    apply Subgroup.map_injective d.carrier.subtype_injective
    rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    change zpowers ((eval p Matrix.PSL3Four.MathieuAmalgamMarking.torusWord : d.carrier) : G) =
      zpowers t
    rw [htorus]
    exact hwordt
  obtain ⟨b,j,h25,hquot⟩ := d.hexad_quotient_relators
    L le_sup_left e hleft hPD π hπker kA hkact p hpmark
    ⟨t,htd.1⟩ (by simpa using ht3) hline n hnD hn3 hnt hnT
  let T : G := eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
  let TD : d.hexad_overgroup := eval (fun i => inclusion hPD (p i))
    Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
  let m : d.hexad_overgroup := (if b then (⟨n,hnD⟩ : d.hexad_overgroup)
    else ⟨n,hnD⟩⁻¹)*TD^j.val
  have hTD : (TD:G)=T := by
    simpa only [TD,T,p,Subgroup.subtype_apply,Subgroup.coe_inclusion] using
      eval_hom_transport d.hexad_overgroup.subtype (fun i => inclusion hPD (p i))
        Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
  have hm : (m:G)=(if b then n else n⁻¹)*T^j.val := by
    simp only [m,Subgroup.coe_mul,Subgroup.coe_pow,apply_ite,Subgroup.coe_inv,hTD]
  have hTmem : T∈d.carrier := by
    change eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord∈d.carrier
    rw [←htorus]
    exact (eval p Matrix.PSL3Four.MathieuAmalgamMarking.torusWord).property
  have hT3 : orderOf T=3 := by
    have hh := congrArg (fun H : Subgroup G => Nat.card H) hwordt
    simpa only [Nat.card_zpowers,ht3] using hh
  have hTline : zpowers T=zpowers t := hwordt
  have hntT : Commute n T := by
    have hTt : T∈zpowers t := hTline ▸ mem_zpowers T
    obtain ⟨k,hk⟩ := hTt
    rw [←hk]
    exact hnt.zpow_right k
  have hnTT : n∉zpowers T := by rwa [hTline]
  have hrT : r*T*r⁻¹=T⁻¹ := by
    have hTt : T∈zpowers t := hTline ▸ mem_zpowers T
    obtain ⟨k,hk⟩ := hTt
    rw [←hk]
    have hh := congrArg (fun x : G => x^k) hrt
    simpa only [conj_zpow,inv_zpow] using hh
  have hellT : Commute (r*s) T := by
    have htell : Commute (r*s) t := mem_centralizer_singleton_iff.mp hrs
    have hTt : T∈zpowers t := hTline ▸ mem_zpowers T
    obtain ⟨k,hk⟩ := hTt
    rw [←hk]
    exact htell.zpow_right k
  have h19 := Theory.SpecificGroups.MathieuAmalgamCompletion.partial_relators_cubic_variants
    d.carrier pair T n r (r*s) hTmem hT3 hn3 hntT hnTT hrT hrn hellT hcross
    hrelations (!b) j.val
  have htwenty (i : Fin 27) (hi : i.val<17 ∨ i=23 ∨ i=25 ∨ i=26) :
      eval ![pair 0,pair 1,r*s,(m:G)]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1 := by
    by_cases h25i : i=25
    · subst i
      exact h25 (r*s)
    have hcut : i.val<17 ∨ i=23 ∨ i=26 := by tauto
    have hh := h19 i hcut
    rw [hm]
    cases b <;> simpa using hh
  exact ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright,hrL,hsL,her,hes,pair,hpair,hmem,hpairmark,hwordr,hwordt,hDN,π,hπs,hπker,hπmark,kA,hkA,hkact,
    n,hnD,hnP,hnt,hn3,hnT,hrn,hcross,hLgen,hDgen,hPD,b,j,htwenty,hquot⟩


end CFSG.Quasithin.HigmanSims
