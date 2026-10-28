module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearThreeConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadOvergroup

/-!
# The actual linear group and its hexad overgroup from the HS source

The same original paired endpoints construct a proper PSL3(4) subgroup L.
The retained full radical-normalizer quotient then constructs the literal
E16-by-A6 subgroup D. Their intersection is exactly the first endpoint,
and adjoining D strictly enlarges L. All original local data and markings
are retained. The degree of this enlargement is a separate source duty.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

/-- The original local hypotheses construct the actual linear/hexad pair,
with the full original endpoint data and exact radical quotient markings. -/
theorem TypeAt.exists_original_mathieu_seed (h : TypeAt z V) :
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
                (d.carrier⊔P₂) ⊓ normalizer (A : Set G) = d.carrier ∧
                (d.carrier⊔P₂ : Subgroup G) < (d.carrier⊔P₂)⊔d.hexad_overgroup ∧
                ∃ hDN : d.hexad_overgroup ≤ normalizer (A : Set G),
                  A ≤ d.hexad_overgroup ∧ d.carrier ≤ d.hexad_overgroup ∧
                  Nat.card d.hexad_overgroup = 5760 ∧
                  (d.carrier⊔P₂) ⊓ d.hexad_overgroup = d.carrier ∧
                  ∃ π : d.hexad_overgroup →* alternatingGroup (Fin 6),
                    Function.Surjective π ∧ π.ker = A.subgroupOf d.hexad_overgroup ∧
                    (∀ g : d.hexad_overgroup, (π g : Equiv.Perm (Fin 6)) =
                      d.six_letter_quotient (inclusion hDN g)) ∧
                    ∃ f : (d.hexad_overgroup ⧸ π.ker) ≃* alternatingGroup (Fin 6),
                      ∀ g : d.hexad_overgroup, f (QuotientGroup.mk g) = π g := by
  obtain ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright⟩ := h.exists_original_linearThree_subgroup
  let := hAE
  let := hBE
  let P₂ := d.carrier.map (MulAut.conj c).toMonoidHom
  let L := d.carrier⊔P₂
  have hLN := d.linear_three_radical_normalizer L le_sup_left e hleft
  obtain ⟨hDN,hAD,hPD,hDcard,hLD,π,hπs,hπker,hπmark,f,hf⟩ :=
    d.hexad_overgroup_structure L le_sup_left e hleft
  have hDL : ¬ d.hexad_overgroup ≤ L := by
    intro hh
    have hh' : d.hexad_overgroup = d.carrier := by
      simpa only [inf_eq_right.mpr hh] using hLD
    have hc := d.carrier_card
    rw [← hh',hDcard] at hc
    norm_num at hc
  have hstrict : L < L⊔d.hexad_overgroup :=
    lt_of_le_of_ne le_sup_left (fun he => hDL (he ▸ le_sup_right))
  exact ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA',hRA,hBd,hAP₂,hBP₂,htd,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,hk,hke,
    r,s,hr,hs,hsc,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,hrs3,
    marking,hmA,hmB,hproper,e,hleft,hright,hLN,hstrict,
    hDN,hAD,hPD,hDcard,hLD,π,hπs,hπker,hπmark,f,hf⟩

end CFSG.Quasithin.HigmanSims
