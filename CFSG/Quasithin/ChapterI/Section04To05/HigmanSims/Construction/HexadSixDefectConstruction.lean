module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadActualNineteen
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadSixSourceDefects

/-!
# One exact source obstruction for the six remaining hexad words

The complete original tuple supplies actual equations expressing each remaining
word as products of conjugates of its word-17 kernel defect. The same literal
pair, q, full kernel, n and cubic parameters are retained. No new vanishing
hypothesis is introduced; all27words hold precisely when that one defect is1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Subgroup.CosetWordCertificate
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

private theorem eval_hom_defects {H K α : Type*} [Group H] [Group K]
    (f : H→*K) (p : α→H) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

omit [Finite G] in
private theorem support_defects : ∀ i : Fin 27,
    (i=17 ∨ i=18 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
    ∀ a∈Theory.SpecificGroups.MathieuAmalgamCompletion.relator i,a.1≠2 := by decide +kernel
omit [Finite G] in
private theorem eval_agrees_defects (g h : Fin 4→G) (w : Word (Fin 4))
    (ha : ∀ a∈w,g a.1=h a.1) : eval g w=eval h w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [eval_cons,eval_cons,ha a (by simp),ih (fun b hb => ha b (by simp [hb]))]
omit [Finite G] in
private theorem middle_defects (a b ell n : G) (i : Fin 27)
    (hi : i=17 ∨ i=18 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) :
    eval ![a,b,ell,n] (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=
      eval ![a,b,1,n] (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i) := by
  apply eval_agrees_defects
  rintro ⟨j,s⟩ hj
  have hn := support_defects i hi ⟨j,s⟩ hj
  fin_cases j <;> simp_all
omit [Finite G] in
private theorem cut_defects (i : Fin 27) :
    (i.val<17 ∨ i=19 ∨ i=23 ∨ i=25 ∨ i=26) ∨
      (i=17 ∨ i=18 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) := by
  fin_cases i <;> decide

omit [Finite G] in
private theorem all_relators_iff_defect17 (a b ell n : G)
    (h21 : ∀ i : Fin 27, (i.val<17 ∨ i=19 ∨ i=23 ∨ i=25 ∨ i=26) →
      eval ![a,b,ell,n] (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1)
    (heqs : Theory.SpecificGroups.SymmetricSix.HexadSixDefects.Equations a b n) :
    (∀ i : Fin 27, eval ![a,b,ell,n]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1) ↔
      eval ![a,b,1,n] (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17)=1 := by
  have he := heqs.all_iff
  simp only [Theory.SpecificGroups.SymmetricSix.HexadSixDefects.hexadWord_eq] at he
  constructor
  · intro hall
    rw [←middle_defects a b ell n 17 (Or.inl rfl)]
    exact hall 17
  · intro h17 i
    rcases cut_defects i with hi|hi
    · exact h21 i hi
    · rw [middle_defects a b ell n i hi]
      exact (he.mpr h17) i hi

theorem TypeAt.exists_original_six_defect_equations (h : TypeAt z V) :
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
                                (∀ ell : d.hexad_overgroup, ∀ i : Fin 27,
                                  (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
                                  π (Subgroup.CosetWordCertificate.eval ![pD 0,pD 1,ell,m]
                                    (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i))=1) ∧
                                Theory.SpecificGroups.SymmetricSix.HexadSixDefects.Equations
                                  (pair 0) (pair 1) (m:G) ∧
                                let δ := Subgroup.CosetWordCertificate.eval
                                  ![pair 0,pair 1,(1:G),(m:G)]
                                  (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17)
                                δ∈A ∧ δ^2=1 ∧
                                ((∀ i : Fin 27,
                                  Subgroup.CosetWordCertificate.eval ![pair 0,pair 1,r*s,(m:G)]
                                    (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1)
                                  ↔ δ=1) := by
  obtain ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright,hrL,hsL,her,hes,
    pair,hpair,hmem,hpairmark,hwordr,hwordt,hDN,π,hπs,hπker,hπmark,kA,hkA,hkact,
    n,hnD,hnP,hnt,hn3,hnT,hrn,hcross,hLgen,hDgen,hPD,b,j,htwentyone,hquot⟩ :=
    h.exists_original_twentyone_and_quotient_relators
  let := hAE
  let := hBE
  let P₂ := d.carrier.map (MulAut.conj c).toMonoidHom
  let L := d.carrier⊔P₂
  let p : Fin 2→d.carrier := fun i => ⟨pair i,hmem i⟩
  let pD : Fin 2→d.hexad_overgroup := fun i => inclusion hPD (p i)
  let TD : d.hexad_overgroup := eval pD Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
  let m : d.hexad_overgroup := (if b then (⟨n,hnD⟩ : d.hexad_overgroup)
    else ⟨n,hnD⟩⁻¹)*TD^j.val
  have hm3 : m^3=1 := by
    apply Subtype.ext
    change (m:G)^3=1
    have hh : eval ![pair 0,pair 1,r*s,(m:G)]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 13)=1 :=
      htwentyone 13 (Or.inl (by decide))
    simpa [Theory.SpecificGroups.MathieuAmalgamCompletion.relator,
      Theory.SpecificGroups.MathieuAmalgamCompletion.decode,eval,FreeGroup.lift_mk,
      pow_succ,mul_assoc] using hh
  have hTD : (TD:G)=eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord := by
    simpa only [TD,pD,p,Subgroup.subtype_apply,Subgroup.coe_inclusion] using
      eval_hom_defects d.hexad_overgroup.subtype pD
        Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
  have hnTD : Commute (⟨n,hnD⟩ : d.hexad_overgroup) TD := by
    apply Subtype.ext
    have hTt : eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord∈zpowers t :=
      hwordt ▸ mem_zpowers _
    obtain ⟨k,hk⟩ := hTt
    have hh := hnt.zpow_right k
    simpa only [Subgroup.coe_mul,hTD,hk] using hh.eq
  have hmTD : Commute m TD := by
    dsimp [m]
    cases b
    · exact hnTD.inv_left.mul_left ((Commute.refl TD).pow_left j.val)
    · exact hnTD.mul_left ((Commute.refl TD).pow_left j.val)
  have hq17 : π (eval ![pD 0,pD 1,1,m]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17))=1 :=
    hquot 1 17 (Or.inl rfl)
  have hq19 : π (eval ![pD 0,pD 1,1,m]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 19))=1 :=
    hquot 1 19 (Or.inr (Or.inr (Or.inl rfl)))
  have heqs := h.hexad_six_defect_equations W A B hWV hW4 hAP hC hi c hcP
    (by rwa [hc2]) hBc d hBd hB16 L le_sup_left e hleft pair hmem hpairmark
    hDN π hπker hπmark kA hkact hPD m hm3 hmTD hq17 hq19
  let δ : G := eval ![pair 0,pair 1,1,(m:G)]
    (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17)
  have hδA : δ∈A := by
    have hker : eval ![pD 0,pD 1,1,m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17)∈π.ker := hq17
    have hA : ((eval ![pD 0,pD 1,1,m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17) : d.hexad_overgroup):G)∈A :=
      show eval ![pD 0,pD 1,1,m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17)∈A.subgroupOf d.hexad_overgroup
        from hπker ▸ hker
    change d.hexad_overgroup.subtype (eval ![pD 0,pD 1,1,m]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17))∈A at hA
    rw [eval_hom_defects] at hA
    have heval : (fun i => d.hexad_overgroup.subtype (![pD 0,pD 1,1,m] i)) =
        ![pair 0,pair 1,(1:G),(m:G)] := by
      funext i
      fin_cases i <;> rfl
    rw [heval] at hA
    exact hA
  have hδ2 : δ^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) δ hδA
  have hall : (∀ i : Fin 27,
      eval ![pair 0,pair 1,r*s,(m:G)]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1) ↔ δ=1 :=
    all_relators_iff_defect17 (pair 0) (pair 1) (r*s) (m:G) htwentyone heqs
  exact ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright,hrL,hsL,her,hes,pair,hpair,hmem,hpairmark,hwordr,hwordt,hDN,π,hπs,hπker,hπmark,kA,hkA,hkact,
    n,hnD,hnP,hnt,hn3,hnT,hrn,hcross,hLgen,hDgen,hPD,b,j,htwentyone,hquot,heqs,hδA,hδ2,hall⟩

end CFSG.Quasithin.HigmanSims
