module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadPairOrders
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCubicSeparation
public import Theory.SpecificGroups.SymmetricSix.HexadQuotientRelatorsLift
public import Theory.SpecificGroups.MathieuAmalgamCompletion.CubicVariantRelations
public import Mathlib.Data.Fin.VecNotation

/-!
# Simultaneous quotient words for the original endpoint marking

This source keeps the original full hexad quotient and the literal endpoint
pair.  The natural-kernel fixed-point-free lemma kills the cube of the
selected exterior cubic; no complement or affine splitting is introduced.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetWordCertificate
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "A6" => alternatingGroup (Fin 6)
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule

private theorem eval_hom {H α : Type*} [Group H]
    (f : H→*G) (p : α→H) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

private theorem eval_agrees {α : Type*} (g h : α→G) (w : Word α)
    (ha : ∀ a∈w,g a.1=h a.1) : eval g w=eval h w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [eval_cons,eval_cons,ha a (by simp),ih (fun b hb => ha b (by simp [hb]))]

private theorem support25 : ∀ a∈
    Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25, a.1≠2 := by
  decide +kernel

/-- The original pair, full kernel and exterior cubic supply one variant
satisfying actual relator 25 and quotient relators 17–22 and 24 simultaneously.
All quotient-separation and pair-order hypotheses are derived from the same
source data, without a splitting or remaining-word hypothesis. -/
theorem NaturalEndpointData.hexad_quotient_relators
    (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier≤L)
    (e : L≃*Matrix.PSL3Four.PSL)
    (_hmark : (d.carrier.subgroupOf L).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F)
    (hPD : d.carrier≤d.hexad_overgroup)
    (q : d.hexad_overgroup→*A6)
    (hqker : q.ker=A.subgroupOf d.hexad_overgroup)
    (k : q.ker≃*Multiplicative Vec)
    (hk : ∀ (g : d.hexad_overgroup) (a : q.ker),
      k (MulAut.conjNormal g a)=Multiplicative.ofAdd
        (Theory.SpecificGroups.SymmetricSix.polarAction (q g).val (k a).toAdd))
    (pair : Fin 2→d.carrier)
    (hpair : ∀ i, e (inclusion hPL (pair i)) =
      Matrix.PSL3Four.MathieuAmalgamMarking.pair i)
    (t : d.carrier) (ht3 : orderOf t=3)
    (hline : zpowers (Subgroup.CosetWordCertificate.eval pair
        Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)=zpowers t)
    (n : G) (hnD : n∈d.hexad_overgroup)
    (hn3 : orderOf n=3) (hnt : Commute n (t:G))
    (hnT : n∉zpowers (t:G)) :
    ∃ b : Bool, ∃ j : Fin 3,
      let m := (if b then (⟨n,hnD⟩ : d.hexad_overgroup) else ⟨n,hnD⟩⁻¹) *
        (Subgroup.CosetWordCertificate.eval
          (fun i => inclusion hPD (pair i))
          Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)^j.val
      (∀ ell : G, eval ![(pair 0 : G),(pair 1 : G),ell,(m:G)]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25)=1) ∧
      ∀ ell : d.hexad_overgroup, ∀ i : Fin 27,
        (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
        q (eval ![inclusion hPD (pair 0),inclusion hPD (pair 1),ell,m]
          (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i))=1 := by
  obtain ⟨hp0, hp1, hp01⟩ := d.hexad_pair_quotient_orders L hPL e hPD q hqker pair hpair
  have hp0orig : orderOf (pair 0)=3 := by
    rw [←orderOf_injective (inclusion hPL) (inclusion_injective hPL),←e.orderOf_eq,
      hpair]
    exact Matrix.PSL3Four.MathieuAmalgamMarking.canonical_pair_orders.1
  have hpa : (inclusion hPD (pair 0))^3=1 := by
    rw [← map_pow]
    have hh : (pair 0)^3=1 := by
      have hx := pow_orderOf_eq_one (pair 0)
      rw [hp0orig] at hx
      exact hx
    rw [hh]
    simp
  have hpb : (q (inclusion hPD (pair 1)))^2=1 := by
    have hh := pow_orderOf_eq_one (q (inclusion hPD (pair 1)))
    rw [hp1] at hh
    exact hh
  have hp01orig : orderOf (pair 0*pair 1)=5 := by
    rw [←orderOf_injective (inclusion hPL) (inclusion_injective hPL),←e.orderOf_eq,
      map_mul]
    change orderOf (e ((inclusion hPL) (pair 0) * (inclusion hPL) (pair 1)))=5
    rw [map_mul,hpair 0,hpair 1]
    exact Matrix.PSL3Four.MathieuAmalgamMarking.canonical_pair_orders.2.2
  have hpab : (inclusion hPD (pair 0)*inclusion hPD (pair 1))^5=1 := by
    rw [← map_mul,← map_pow]
    have hh : (pair 0*pair 1)^5=1 := by
      have hx := pow_orderOf_eq_one (pair 0*pair 1)
      rw [hp01orig] at hx
      exact hx
    rw [hh]
    simp
  have hfree : ∀ v : Vec,
      Theory.SpecificGroups.SymmetricSix.polarAction
        (q (inclusion hPD (pair 0))).val v=v → v=0 :=
    d.hexad_cubic_kernel_fixed_free hPD q hqker k hk (pair 0) hp0orig
  obtain ⟨nq,nqT,nqT2,hcommT⟩ :=
    d.hexad_cubic_quotient_separation hPD q hqker pair t ht3 hline n hnD hn3 hnt hnT
  let T : d.hexad_overgroup :=
    Subgroup.CosetWordCertificate.eval
      ![(inclusion hPD (pair 0)),(inclusion hPD (pair 1))]
      Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
  have hnt3 : (⟨n,hnD⟩ : d.hexad_overgroup)^3=1 := by
    simpa [hn3] using pow_orderOf_eq_one (⟨n,hnD⟩ : d.hexad_overgroup)
  obtain ⟨b,j,hword,hquot⟩ :=
    Theory.SpecificGroups.SymmetricSix.HexadCubicWord.exists_lifted_cubic_variant_relators
      q k hk (inclusion hPD (pair 0)) (inclusion hPD (pair 1)) ⟨n,hnD⟩
      hpa hfree hpb hpab hnt3 nq nqT nqT2 hcommT
  let m := (if b then (⟨n,hnD⟩ : d.hexad_overgroup) else ⟨n,hnD⟩⁻¹) * T^j.val
  refine ⟨b,j,?_,?_⟩
  · change ∀ ell : G, eval ![(pair 0 : G),(pair 1 : G),ell,(m:G)]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25)=1
    intro ell
    have hd : eval ![(inclusion hPD (pair 0)),(inclusion hPD (pair 1)),
        (1 : d.hexad_overgroup),m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25)=1 := by
      simpa [m,T] using hword (1 : d.hexad_overgroup)
    have hd' := congrArg (fun x : d.hexad_overgroup => (x:G)) hd
    have hcoeval :
        (eval ![(inclusion hPD (pair 0)),(inclusion hPD (pair 1)),
          (1 : d.hexad_overgroup),m]
          (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25) : G) =
        eval ![(pair 0 : G),(pair 1 : G),(1:G),(m:G)]
          (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25) := by
      exact (eval_hom (d.hexad_overgroup.subtype)
        ![(inclusion hPD (pair 0)),(inclusion hPD (pair 1)),
          (1 : d.hexad_overgroup),m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25))
    have hd'' : eval ![(pair 0 : G),(pair 1 : G),(1:G),(m:G)]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25)=1 := by
      rw [←hcoeval]
      exact hd'
    have hmiddle :
        eval ![(pair 0 : G),(pair 1 : G),ell,(m:G)]
          (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25) =
        eval ![(pair 0 : G),(pair 1 : G),(1:G),(m:G)]
          (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25) := by
      apply eval_agrees
      intro a ha
      rcases a with ⟨i,s⟩
      have hi := support25 ⟨i,s⟩ ha
      fin_cases i <;> simp_all
    rw [hmiddle]
    exact hd''

  · exact hquot

end CFSG.Quasithin.HigmanSims
