module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates
public import Theory.SpecificGroups.SymmetricSix.NaturalDihedralComplement

/-!
# Splitting the original hexad kernel from its actual opposite radical

The original opposite elementary sixteen supplies commuting involutions
with independent kernel cosets and the same fixed four. Their proved
dihedral extension complements the kernel over a Sylow-two image. Gaschütz
then gives a complement to the literal full hexad kernel. The same original
six-letter quotient identifies this complement with A₆.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

/-- The original paired-radical geometry splits the literal hexad kernel,
retaining the original quotient values on the actual complement. -/
theorem TypeAt.hexad_kernel_complement (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W≤V) (hW4 : Nat.card W=4) (hWA : W≤A)
    (hAC : A≤centralizer (W:Set G)) (hAP : A⊓(normalizer (V:Set G)).pCoreIn 2=W)
    (c : G) (hc : c∈(normalizer (V:Set G)).pCoreIn 2) (hcW : c^2∉W)
    (hB : B=A.map (MulAut.conj c).toMonoidHom) (hi : A⊓B=W)
    (d : NaturalEndpointData A) (hBd : B≤d.carrier)
    (L : Subgroup G) (hPL : d.carrier≤L) (eL : L≃*Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map eL.toMonoidHom=Point)
    (hB16 : Nat.card B=16) :
    ∃ hDN : d.hexad_overgroup≤normalizer (A:Set G),
      ∃ q : d.hexad_overgroup→*alternatingGroup (Fin 6), Function.Surjective q ∧
        q.ker=A.subgroupOf d.hexad_overgroup ∧
        (∀ g : d.hexad_overgroup, (q g:Equiv.Perm (Fin 6))=
          d.six_letter_quotient (inclusion hDN g)) ∧
        ∃ K : Subgroup d.hexad_overgroup, q.ker.IsComplement' K ∧
          ∃ k : K≃*alternatingGroup (Fin 6), ∀ g : K,k g=q g := by
  have hWB : W≤B := hi ▸ (show A⊓B≤B from inf_le_right)
  obtain ⟨x,hx,hxW⟩ : ∃ x∈B,x∉W := by
    by_contra! hn
    have hh := card_le_of_le hn
    rw [hW4,hB16] at hh
    omega
  have hx1 : x≠1 := fun he => hxW (he ▸ W.one_mem)
  have hxorder : orderOf x=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx) hx1
  let J := W⊔zpowers x
  have hJcard : Nat.card J≤8 := by
    have hn : zpowers x≤normalizer (W:Set G) := zpowers_le.mpr
      (centralizer_le_normalizer _ (fun w hw => setLike_mul_comm (hWB hw) hx))
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes W (zpowers x) hn
    rw [hW4,Nat.card_zpowers,hxorder] at hh
    have hp : 0<Nat.card (W⊓zpowers x:Subgroup G) := Nat.card_pos
    change 4*2=Nat.card (W⊓zpowers x:Subgroup G)*Nat.card J at hh
    nlinarith
  obtain ⟨y,hy,hyJ⟩ : ∃ y∈B,y∉J := by
    by_contra! hn
    have hh := card_le_of_le hn
    rw [hB16] at hh
    omega
  have hyW : y∉W := fun hh => hyJ (mem_sup_left hh)
  have hxyW : x*y∉W := by
    intro hh
    apply hyJ
    have h := J.mul_mem (J.inv_mem (mem_sup_right (mem_zpowers x))) (mem_sup_left hh)
    simpa only [inv_mul_cancel_left] using h
  obtain ⟨_,_,hPD,_⟩ := d.hexad_overgroup_structure L hPL eL hmark
  obtain ⟨hDN,q,hq,hker,hmarkq,e,_,he⟩ := d.hexad_kernel_coordinates L hPL eL hmark
  have ker_mem {a : d.hexad_overgroup} (ha : a∈q.ker) : (a:G)∈A :=
    show a∈A.subgroupOf d.hexad_overgroup from hker ▸ ha
  let X : d.hexad_overgroup := ⟨x,hPD (hBd hx)⟩
  let Y : d.hexad_overgroup := ⟨y,hPD (hBd hy)⟩
  have hx2 : X^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx)
  have hy2 : Y^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) y hy)
  have hxA : x∉A := fun hh => hxW (hi ▸ (show x∈A⊓B from ⟨hh,hx⟩))
  have hyA : y∉A := fun hh => hyW (hi ▸ (show y∈A⊓B from ⟨hh,hy⟩))
  have hqX : orderOf (q X)=2 := orderOf_eq_prime
    (by rw [←map_pow,hx2,map_one]) (fun he => hxA (ker_mem he))
  have hqY : orderOf (q Y)=2 := orderOf_eq_prime
    (by rw [←map_pow,hy2,map_one]) (fun he => hyA (ker_mem he))
  have hne : q X≠q Y := by
    intro hh
    have hprod : X*Y∈q.ker := by
      change q (X*Y)=1
      rw [map_mul,hh,←pow_two,←map_pow,hy2,map_one]
    apply hxyW
    rw [←hi]
    exact ⟨ker_mem hprod,B.mul_mem hx hy⟩
  have hfixX := h.paired_plane_radical_centralizer W A hWV hW4 hWA hAC hAP c hc hcW x (hB ▸ hx) hxW
  have hfixY := h.paired_plane_radical_centralizer W A hWV hW4 hWA hAC hAP c hc hcW y (hB ▸ hy) hyW
  have hfixed (a : d.hexad_overgroup) (ha : a∈q.ker) (hay : Commute a Y) : Commute a X := by
    have haA : (a:G)∈A := ker_mem ha
    have haw : (a:G)∈W := hfixY ▸
      (show (a:G)∈A⊓involutionCentralizer y from
        ⟨haA,mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hay.eq)⟩)
    have hac : (a:G)∈A⊓involutionCentralizer x := hfixX ▸ haw
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hac.2)
  obtain ⟨K,hK⟩ :=
    Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts.exists_complement_of_same_kernel_fixed
      q hq e (by intro g a; simpa only [Theory.SpecificGroups.SymmetricSix.polarRepresentation_apply] using he g a)
      X Y hx2 hy2 (Subtype.ext (setLike_mul_comm hx hy)) hqX hqY hne hfixed
  let a := QuotientGroup.quotientKerEquivOfSurjective q hq
  let k : K≃*alternatingGroup (Fin 6) := hK.symm.QuotientMulEquiv.symm.trans a
  refine ⟨hDN,q,hq,hker,hmarkq,K,hK,k,?_⟩
  intro g
  have hh : hK.symm.QuotientMulEquiv.symm g=QuotientGroup.mk' q.ker g := by
    apply hK.symm.QuotientMulEquiv.injective
    rw [MulEquiv.apply_symm_apply,quotientMulEquiv_mk_apply_of_isComplement']
  change a (hK.symm.QuotientMulEquiv.symm g)=q g
  rw [hh]
  rfl

end CFSG.Quasithin.HigmanSims
