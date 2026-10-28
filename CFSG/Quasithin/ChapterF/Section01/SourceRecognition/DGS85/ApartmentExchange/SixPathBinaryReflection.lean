module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathReflectionChange
public import Theory.GroupTheory.DihedralCentralCorrection
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.OddInvolutionEndpointModels

/-!
# The order-twelve binary reflection correction on the original six-path

When a binary path root and the chosen reflection have product of order six,
the word z = (x t)^3 is the central involution of their actual generated
group. The group calculation constructs its central splitting and identifies
the corrected pair with the dihedral group of order six and proves that
the whole original root and corrected reflection generate a group with
trivial two-core. Fixation of the
radius-three ball by this single word supplies the ball hypothesis for the
whole center, so the existing six-path theorem applies with no assumed
central splitting or complement.

The corrected reflection is exactly z t. The original opposite reflection,
Cartan, neighbor orientations and exclusion of Borel twists are retained.
The binary field profile, the source D12/D24 alternatives and the fixation
of z are still required before this proves the binary branch of (14.17).
In particular, the order-twenty-four alternative is not discarded.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(14.17), printed pp.222--223. The earlier local profiles are the Chapter 10 inputs; the remaining
binary alternatives and final source exchange are not asserted here.
-/

public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (c : CompatibleCartans L (reducedSylow L S))
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ j, t j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
  base (Universal.cosetFamily (reducedAmalgam L S)) j)
variable (htmove : ∀ j, t j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
variable (htsq : ∀ j, t j*t j=1)
variable (htnorm : ∀ j, t j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include htfix htmove htsq htnorm in
/-- The binary order-twelve case constructs the splitting, the exact corrected
reflection and its order-six root group on the literal source six-path. -/
theorem source_six_binary_dihedral_reflection_change
    (h : HypothesisF11 L S) (i : Bool) (hK : cartan c=⊥)
    (hcard : Nat.card (pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)=2)
    (x : (reducedAmalgam L S).Universal)
    (hx : x∈pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)
    (hproduct : orderOf (x*t i)=6)
    (hball : (x*t i)^3∈graphBallFixer (sourceGraph (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 3)
    (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7)
    (hthick : ∀ j, ∃ v, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) j) v ∧
      v≠base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ∧
      v≠t j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
    (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))) :
    ∃ (t' : Bool → (reducedAmalgam L S).Universal)
      (htfix' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
        base (Universal.cosetFamily (reducedAmalgam L S)) j)
      (htmove' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
      (_htsq' : ∀ j, t' j*t' j=1)
      (htnorm' : ∀ j, t' j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal)),
      t' i=(x*t i)^3*t i ∧ t' (!i)=t (!i) ∧ orderOf (x*t' i)=3 ∧
      Nonempty ((zpowers x ⊔ zpowers (t' i) : Subgroup (reducedAmalgam L S).Universal) ≃*
        DihedralGroup 3) ∧
      centerIn (zpowers x ⊔ zpowers (t' i))=⊥ ∧
      pCore 2 (pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk ⊔
          zpowers (t' i) : Subgroup (reducedAmalgam L S).Universal)=⊥ ∧
      (∀ z∈originalMiddle (reducedAmalgam L S),
        z • (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 ≠
          (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 →
        (pathRoot (X := (reducedAmalgam L S).Universal)
          (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk).map
            (MulAut.conj z).toMonoidHom ≠
          pathRoot (X := (reducedAmalgam L S).Universal)
            (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk) := by
  let P := pathRoot (X := (reducedAmalgam L S).Universal)
    (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk
  let : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hx2 : x*x=1 := by
    have hh := congrArg (fun y:P => (y : (reducedAmalgam L S).Universal))
      (pow_card_eq_one' (x := (⟨x,hx⟩ : P)))
    change x^Nat.card P=1 at hh
    dsimp only [P] at hh
    simpa only [hcard,pow_two] using hh
  have hxne : x≠1 := by
    intro he
    have ho : orderOf (t i)=6 := by simpa only [he,one_mul] using hproduct
    have hd := orderOf_dvd_of_pow_eq_one
      (show (t i)^2=1 by simpa only [pow_two] using htsq i)
    norm_num [ho] at hd
  have hxo : orderOf x=2 :=
    orderOf_eq_prime (by simpa only [pow_two] using hx2) hxne
  have hP : P=zpowers x := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hx)
    rw [Nat.card_zpowers,hxo]
    exact hcard.le
  let z := (x*t i)^3
  let u := z*t i
  let J := zpowers x ⊔ zpowers (t i)
  let R := zpowers x ⊔ zpowers u
  obtain ⟨hz2,hzo,hu2,hxu,hzJ,hRJ,heR,hZR,hZJ,hdis,hjoin,htu⟩ :=
    involutions_product_six_central_correction x (t i) hx2 (htsq i) hproduct
  change z*z=1 at hz2
  change z∈centerIn J at hzJ
  change R≤J at hRJ
  change centerIn J ⊓ R=⊥ at hdis
  have hKJ : cartan c≤J := by rw [hK]; exact bot_le
  have htprod : t i∈centerIn J ⊔ R := by
    rw [←hjoin]
    exact mem_sup_right (mem_zpowers (t i))
  have hcenterball : centerIn J≤graphBallFixer (sourceGraph (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 3 := by
    rw [hZJ]
    exact zpowers_le.mpr hball
  obtain ⟨t',hfix',hmove',hsq',hnorm',hvR,hother,⟨w,hw,htw,hw2⟩,hsep⟩ :=
    source_six_central_reflection_change_with_root_separation c t htfix htmove htsq htnorm
      h i J R hRJ hKJ hdis htprod hcenterball htrans hthick hodd
  have huR : u∈R := mem_sup_right (mem_zpowers u)
  have he : t' i*u⁻¹=w⁻¹*z := by
    calc
      t' i*u⁻¹ = w⁻¹*(w*t' i)*u⁻¹ := by group
      _ = w⁻¹*(z*u)*u⁻¹ := by rw [←htw,htu]
      _ = w⁻¹*z := by group
  have hdiff : t' i*u⁻¹=1 := hdis.le ⟨by
    rw [he]
    exact (centerIn J).mul_mem ((centerIn J).inv_mem hw) hzJ,
    R.mul_mem hvR (R.inv_mem huR)⟩
  have hcorrect : t' i=u := mul_inv_eq_one.mp hdiff
  have hcore : pCore 2 R=⊥ := by
    obtain ⟨e⟩ := heR
    let : Finite R := Finite.of_equiv (DihedralGroup 3) e.symm.toEquiv
    obtain ⟨e3⟩ := nonempty_dihedralThreeEquivPerm
    let f := (e.trans e3).toMonoidHom
    have hker : f.ker=⊥ := (MonoidHom.ker_eq_bot_iff f).mpr (e.trans e3).injective
    have hh := ker_eq_twoCore_of_surjective_perm_three f (e.trans e3).surjective (by
      rw [hker]
      exact IsPGroup.of_subsingleton 2 _)
    exact hh.symm.trans hker
  refine ⟨t',hfix',hmove',hsq',hnorm',hcorrect,hother,?_,?_,?_,?_,hsep⟩
  · simpa only [hcorrect] using hxu
  · rw [hcorrect]
    exact heR
  · simpa only [hcorrect] using hZR
  · change pCore 2 (P ⊔ zpowers (t' i) : Subgroup (reducedAmalgam L S).Universal)=⊥
    rw [hP,hcorrect]
    exact hcore

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
