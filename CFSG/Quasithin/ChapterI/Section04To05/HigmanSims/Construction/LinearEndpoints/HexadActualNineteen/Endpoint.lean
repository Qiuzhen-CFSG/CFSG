module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadQuotientTransport
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadAffineCoordinates
public import Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen

/-!
# Internal source bridge for actual word 19

This intentional internal module isolates the source mathematics before the
large TypeAt tuple assembly. The original paired radicals supply the proved
affine coordinates. Their
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

private theorem eval_hom_nineteen {H K α : Type*} [Group H] [Group K]
    (f : H→*K) (p : α→H) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

private theorem actual19_source (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W≤V) (hW4 : Nat.card W=4)
    (hAP : A⊓(normalizer (V:Set G)).pCoreIn 2=W)
    (hC : A⊔B≤centralizer (W:Set G)) (hi : A⊓B=W)
    (c : G) (hcP : c∈(normalizer (V:Set G)).pCoreIn 2) (hcW : c^2∉W)
    (hBc : B=A.map (MulAut.conj c).toMonoidHom)
    (d : NaturalEndpointData A) (hBd : B≤d.carrier) (hB16 : Nat.card B=16)
    (L : Subgroup G) (hPL : d.carrier≤L) (e : L≃*Matrix.PSL3Four.PSL)
    (hleft : (d.carrier.subgroupOf L).map e.toMonoidHom=Point)
    (pair : Fin 2→G) (hmem : ∀ i,pair i∈d.carrier)
    (hpairmark : ∀ i,pair i=(e.symm (Matrix.PSL3Four.MathieuAmalgamMarking.pair i):G))
    (t n ell : G) (hnt : Commute n t)
    (hwordt : zpowers (eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)=zpowers t)
    (hDN : d.hexad_overgroup≤normalizer (A:Set G))
    (π : d.hexad_overgroup→*alternatingGroup (Fin 6))
    (hπker : π.ker=A.subgroupOf d.hexad_overgroup)
    (hπmark : ∀ g : d.hexad_overgroup,(π g:Equiv.Perm (Fin 6))=
      d.six_letter_quotient (inclusion hDN g))
    (kA : π.ker≃*Multiplicative Theory.SpecificGroups.SymmetricSix.NaturalModule)
    (hkact : ∀ (g : d.hexad_overgroup) (a : π.ker),
      kA (MulAut.conjNormal g a)=Multiplicative.ofAdd
        (Theory.SpecificGroups.SymmetricSix.polarAction (π g).val (kA a).toAdd))
    (hnD : n∈d.hexad_overgroup) (hPD : d.carrier≤d.hexad_overgroup)
    (b : Bool) (j : Fin 3)
    (htwenty : ∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=25 ∨ i=26) →
      eval ![pair 0,pair 1,ell,
        (((if b then (⟨n,hnD⟩ : d.hexad_overgroup) else ⟨n,hnD⟩⁻¹)*
          (eval (fun i => (⟨pair i,hPD (hmem i)⟩ : d.hexad_overgroup))
            Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)^j.val):G)]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1)
    (hquot : ∀ ell' : d.hexad_overgroup, ∀ i : Fin 27,
      (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
      π (eval ![(⟨pair 0,hPD (hmem 0)⟩ : d.hexad_overgroup),⟨pair 1,hPD (hmem 1)⟩,ell',
        (if b then (⟨n,hnD⟩ : d.hexad_overgroup) else ⟨n,hnD⟩⁻¹)*
          (eval (fun i => (⟨pair i,hPD (hmem i)⟩ : d.hexad_overgroup))
            Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)^j.val]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i))=1) :
    eval ![pair 0,pair 1,ell,
      (((if b then (⟨n,hnD⟩ : d.hexad_overgroup) else ⟨n,hnD⟩⁻¹)*
        (eval (fun i => (⟨pair i,hPD (hmem i)⟩ : d.hexad_overgroup))
          Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)^j.val):G)]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 19)=1 := by
  let p : Fin 2→d.carrier := fun i => ⟨pair i,hmem i⟩
  let pD : Fin 2→d.hexad_overgroup := fun i => inclusion hPD (p i)
  let TD : d.hexad_overgroup := eval pD Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
  let m : d.hexad_overgroup := (if b then (⟨n,hnD⟩ : d.hexad_overgroup)
    else ⟨n,hnD⟩⁻¹)*TD^j.val
  have hWA : W≤A := hi ▸ inf_le_left
  have hAC : A≤centralizer (W:Set G) := le_trans le_sup_left hC
  obtain ⟨hDN',q',hq',hker',hmark',kA',hkA',hkact',K,hK,eD,heD,hkeD,hKeD⟩ :=
    h.hexad_affine_coordinates W A B hWV hW4 hWA hAC hAP c hcP hcW hBc hi
      d hBd L hPL e hleft hB16
  have hqeq : q'=π := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    exact (hmark' g).trans (hπmark g).symm
  have heq (g : d.hexad_overgroup) : (eD g).right=π g := by rw [heD,hqeq]
  have hpmark (i : Fin 2) : e (inclusion (show d.carrier≤L from hPL) (p i)) =
      Matrix.PSL3Four.MathieuAmalgamMarking.pair i := by
    have hp : inclusion (show d.carrier≤L from hPL) (p i) =
        e.symm (Matrix.PSL3Four.MathieuAmalgamMarking.pair i) := Subtype.ext (hpairmark i)
    rw [hp,e.apply_symm_apply]
  obtain ⟨hp0,hp1,hp01⟩ := d.hexad_pair_quotient_orders L hPL e hPD π hπker p hpmark
  have hp0orig : orderOf (p 0)=3 := by
    rw [←orderOf_injective (inclusion (show d.carrier≤L from hPL))
      (inclusion_injective hPL),←e.orderOf_eq,hpmark]
    exact Matrix.PSL3Four.MathieuAmalgamMarking.canonical_pair_orders.1
  have hfree := d.hexad_cubic_kernel_fixed_free hPD π hπker kA hkact (p 0) hp0orig
  change orderOf (π (pD 0))=3 at hp0
  change orderOf (π (pD 1))=2 at hp1
  change orderOf (π (pD 0)*π (pD 1))=5 at hp01
  have hp03 : (π (pD 0))^3=1 := by simpa only [hp0] using pow_orderOf_eq_one (π (pD 0))
  have hp12 : (π (pD 1))^2=1 := by simpa only [hp1] using pow_orderOf_eq_one (π (pD 1))
  have hp015 : (π (pD 0)*π (pD 1))^5=1 := by
    simpa only [hp01] using pow_orderOf_eq_one (π (pD 0)*π (pD 1))
  have hm3 : m^3=1 := by
    apply Subtype.ext
    change (m:G)^3=1
    have hh : eval ![pair 0,pair 1,ell,(m:G)]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 13)=1 :=
      htwenty 13 (Or.inl (by decide))
    simpa [Theory.SpecificGroups.MathieuAmalgamCompletion.relator,
      Theory.SpecificGroups.MathieuAmalgamCompletion.decode,eval,FreeGroup.lift_mk,
      pow_succ,mul_assoc] using hh
  have hmq3 : (π m)^3=1 := by rw [←map_pow,hm3,map_one]
  have hq19 : (π (pD 1)*π m*(π (pD 0))⁻¹)^4=1 := by
    have hh : π (eval ![pD 0,pD 1,1,m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 19))=1 :=
      hquot 1 19 (by tauto)
    simpa [Theory.SpecificGroups.MathieuAmalgamCompletion.relator,
      Theory.SpecificGroups.MathieuAmalgamCompletion.decode,eval,FreeGroup.lift_mk,
      pow_succ,mul_assoc,map_mul,map_inv] using hh
  have hTD : (TD:G)=eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord := by
    simpa only [TD,pD,p,Subgroup.subtype_apply,Subgroup.coe_inclusion] using
      eval_hom_nineteen d.hexad_overgroup.subtype pD
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
  have hET : eD TD=eval ![eD (pD 0),eD (pD 1)]
      Matrix.PSL3Four.MathieuAmalgamMarking.torusWord := by
    change eD.toMonoidHom (eval pD _)=_
    rw [eval_hom_nineteen]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hactual : (pD 1*m*(pD 0)⁻¹)^4=1 := by
    apply eD.injective
    rw [map_pow,map_mul,map_mul,map_inv,map_one]
    apply Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen.word19
    · simpa only [heq] using hp03
    · simpa only [heq] using hfree
    · simpa only [heq] using hp12
    · simpa only [heq] using hp015
    · simpa only [heq] using hmq3
    · rw [←hET]
      exact hmTD.map eD.toMonoidHom
    · simpa only [heq] using hq19
  have h19 : eval ![pair 0,pair 1,ell,(m:G)]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 19)=1 := by
    have hh := congrArg (fun x : d.hexad_overgroup => (x:G)) hactual
    simpa [Theory.SpecificGroups.MathieuAmalgamCompletion.relator,
      Theory.SpecificGroups.MathieuAmalgamCompletion.decode,eval,FreeGroup.lift_mk,
      pow_succ,mul_assoc,pD,p] using hh
  exact h19

end CFSG.Quasithin.HigmanSims
