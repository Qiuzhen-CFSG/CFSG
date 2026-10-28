module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadQuotientTransport
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadAffineCoordinates
public import Theory.SpecificGroups.SymmetricSix.HexadSixDefects

/-!
# Exact equations for the six original hexad defects

The original paired-radical source supplies affine coordinates. Their quotient
is identified with the unchanged original quotient. The literal pair and
selected cubic are then used in the arbitrary-pair defect theorem; its actual
identities are pulled back to the original group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetWordCertificate
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

private theorem eval_hom_six {H K α : Type*} [Group H] [Group K]
    (f : H→*K) (p : α→H) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

theorem TypeAt.hexad_six_defect_equations (h : TypeAt z V)
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
    (hDN : d.hexad_overgroup≤normalizer (A:Set G))
    (π : d.hexad_overgroup→*alternatingGroup (Fin 6))
    (hπker : π.ker=A.subgroupOf d.hexad_overgroup)
    (hπmark : ∀ g : d.hexad_overgroup,(π g:Equiv.Perm (Fin 6))=
      d.six_letter_quotient (inclusion hDN g))
    (kA : π.ker≃*Multiplicative Theory.SpecificGroups.SymmetricSix.NaturalModule)
    (hkact : ∀ (g : d.hexad_overgroup) (a : π.ker),
      kA (MulAut.conjNormal g a)=Multiplicative.ofAdd
        (Theory.SpecificGroups.SymmetricSix.polarAction (π g).val (kA a).toAdd))
    (hPD : d.carrier≤d.hexad_overgroup) (m : d.hexad_overgroup)
    (hm3 : m^3=1)
    (hmT : Commute m (eval (fun i => (⟨pair i,hPD (hmem i)⟩ : d.hexad_overgroup))
      Matrix.PSL3Four.MathieuAmalgamMarking.torusWord))
    (hq17 : π (eval ![(⟨pair 0,hPD (hmem 0)⟩ : d.hexad_overgroup),
      ⟨pair 1,hPD (hmem 1)⟩,1,m]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17))=1)
    (hq19 : π (eval ![(⟨pair 0,hPD (hmem 0)⟩ : d.hexad_overgroup),
      ⟨pair 1,hPD (hmem 1)⟩,1,m]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 19))=1) :
    Theory.SpecificGroups.SymmetricSix.HexadSixDefects.Equations
      (pair 0) (pair 1) (m:G) := by
  let p : Fin 2→d.carrier := fun i => ⟨pair i,hmem i⟩
  let pD : Fin 2→d.hexad_overgroup := fun i => inclusion hPD (p i)
  let TD : d.hexad_overgroup := eval pD Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
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
  have hmq3 : (π m)^3=1 := by rw [←map_pow,hm3,map_one]
  have hqfour : (π (pD 1)*π m*(π (pD 0))⁻¹)^4=1 := by
    have hh : π (eval ![pD 0,pD 1,1,m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 19))=1 := hq19
    simpa [Theory.SpecificGroups.MathieuAmalgamCompletion.relator,
      Theory.SpecificGroups.MathieuAmalgamCompletion.decode,eval,FreeGroup.lift_mk,
      pow_succ,mul_assoc,map_mul,map_inv] using hh
  have hET : eD TD=eval ![eD (pD 0),eD (pD 1)]
      Matrix.PSL3Four.MathieuAmalgamMarking.torusWord := by
    change eD.toMonoidHom (eval pD _)=_
    rw [eval_hom_six]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hmodel17 : eval ![(eD (pD 0)).right,(eD (pD 1)).right,1,(eD m).right]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17)=1 := by
    have hh : π (eval ![pD 0,pD 1,1,m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 17))=1 := hq17
    rw [eval_hom_six] at hh
    have htuple : (fun i => π (![pD 0,pD 1,1,m] i)) =
        ![π (pD 0),π (pD 1),1,π m] := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · exact map_one π
      · rfl
    rw [htuple] at hh
    simpa only [heq] using hh
  have hmodel := Theory.SpecificGroups.SymmetricSix.HexadSixDefects.actual_equations
    (eD (pD 0)) (eD (pD 1)) (eD m)
    (by simpa only [heq] using hp03)
    (by simpa only [heq] using hfree)
    (by simpa only [heq] using hp12)
    (by simpa only [heq] using hp015)
    (by simpa only [heq] using hmq3)
    (by rw [←hET]; exact hmT.map eD.toMonoidHom)
    (by simpa only [heq] using hqfour) (by exact congrArg Subtype.val hmodel17)
  have hD := Theory.SpecificGroups.SymmetricSix.HexadSixDefects.Equations.map eD.symm.toMonoidHom hmodel
  change Theory.SpecificGroups.SymmetricSix.HexadSixDefects.Equations
    (eD.symm (eD (pD 0))) (eD.symm (eD (pD 1))) (eD.symm (eD m)) at hD
  rw [eD.symm_apply_apply,eD.symm_apply_apply,eD.symm_apply_apply] at hD
  have hG := Theory.SpecificGroups.SymmetricSix.HexadSixDefects.Equations.map d.hexad_overgroup.subtype hD
  exact hG

end CFSG.Quasithin.HigmanSims
