module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.ElementaryAbelian.Basic

/-!
# The marked quotient of a dihedral product by one factor center

The parity coordinates on D₈ identify its central-involution quotient with
E₄. Their product with the second D₈ gives a literal marked quotient map
D₈ × D₈ → E₄ × D₈. Any homomorphism with that same kernel has the same
marked image. The derived subgroup of the image is the second factor center.

Source application: Aschbacher--Smith F.5.5, printed pp.301--302.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace DihedralProductCentralFactorQuotient
abbrev D := DihedralGroup 4
abbrev C2 := Multiplicative (ZMod 2)
abbrev E4 := C2×C2
def abelianization : D →* E4 where
  toFun x := match x with
    | .r i => (Multiplicative.ofAdd (i.val : ZMod 2),1)
    | .sr i => (Multiplicative.ofAdd (i.val : ZMod 2),Multiplicative.ofAdd 1)
  map_one' := rfl
  map_mul' := by decide +kernel

theorem abelianization_surjective : Function.Surjective abelianization := by decide +kernel
theorem abelianization_kernel : ∀ d:D,abelianization d=1 ↔ d=1 ∨ d=DihedralGroup.r 2 := by decide +kernel

def modelMap : D×D →* E4×D :=
  (abelianization.comp (MonoidHom.fst D D)).prod (MonoidHom.snd D D)
theorem modelMap_surjective : Function.Surjective modelMap := by
  rintro ⟨a,b⟩
  obtain ⟨d,hd⟩ := abelianization_surjective a
  exact ⟨(d,b),Prod.ext hd rfl⟩
theorem modelMap_kernel (d:D×D) :
    modelMap d=1 ↔ d=1 ∨ d=(DihedralGroup.r 2,1) := by
  change (abelianization d.1,d.2)=(1,1) ↔ _
  rw [Prod.mk.injEq,abelianization_kernel]
  constructor
  · rintro ⟨h|h,hb⟩ <;> simp only [Prod.ext_iff,Prod.fst_one,Prod.snd_one,h,hb] <;> simp
  · rintro (rfl|rfl) <;> simp

theorem exists_range_equiv {H : Type*} [Group H] (j : D×D →* H)
    (hk : ∀ x,j x=1 ↔ x=1 ∨ x=(DihedralGroup.r 2,1)) :
    ∃ e:j.range≃*E4×D, ∀x,e ⟨j x,⟨x,rfl⟩⟩=modelMap x := by
  have hker : j.ker=modelMap.ker := by
    ext x
    exact (hk x).trans (modelMap_kernel x).symm
  let e : j.range≃*E4×D := (QuotientGroup.quotientKerEquivRange j).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective modelMap modelMap_surjective))
  refine ⟨e,?_⟩
  intro x
  have hm : (QuotientGroup.quotientKerEquivRange j) (QuotientGroup.mk' j.ker x)=
      ⟨j x,⟨x,rfl⟩⟩ := rfl
  have hi := (QuotientGroup.quotientKerEquivRange j).symm_apply_apply (QuotientGroup.mk' j.ker x)
  rw [hm] at hi
  change (QuotientGroup.quotientKerEquivOfSurjective modelMap modelMap_surjective)
    (QuotientGroup.quotientMulEquivOfEq hker
      ((QuotientGroup.quotientKerEquivRange j).symm ⟨j x,⟨x,rfl⟩⟩))=modelMap x
  rw [hi]
  rfl

private theorem commutator_cases : ∀a b:E4×D,
    ⁅a,b⁆=1 ∨ ⁅a,b⁆=(1,DihedralGroup.r 2) := by decide +kernel
theorem model_commutator : _root_.commutator (E4×D)=zpowers (1,DihedralGroup.r 2) := by
  apply le_antisymm
  · rw [_root_.commutator_def,commutator_le]
    intro a _ b _
    rcases commutator_cases a b with he|he
    · exact he ▸ (zpowers (1,DihedralGroup.r 2)).one_mem
    · exact he ▸ mem_zpowers _
  · apply zpowers_le.mpr
    have he : ⁅((1:E4),(DihedralGroup.r 1:D)),((1:E4),(DihedralGroup.sr 0:D))⁆=
        (1,DihedralGroup.r 2) := by decide +kernel
    rw [←he]
    exact commutator_mem_commutator (mem_top _) (mem_top _)

private theorem dihedral_center_cases : ∀d:D,(∀a:D,a*d=d*a) →
    d=1 ∨ d=DihedralGroup.r 2 := by decide +kernel

/-- Original central elements have only two images in the quotient. -/
theorem modelMap_center_cases (x : D×D) (hx : x∈center (D×D)) :
    modelMap x=1 ∨ modelMap x=(1,DihedralGroup.r 2) := by
  have ha := dihedral_center_cases x.1 (fun a => congrArg Prod.fst (mem_center_iff.mp hx (a,1)))
  have hb := dihedral_center_cases x.2 (fun b => congrArg Prod.snd (mem_center_iff.mp hx (1,b)))
  have ha0 : abelianization x.1=1 := (abelianization_kernel x.1).mpr ha
  change (abelianization x.1,x.2)=1 ∨ (abelianization x.1,x.2)=(1,DihedralGroup.r 2)
  rcases hb with hb|hb <;> simp [ha0,hb]

theorem model_center_card : Nat.card (center (E4×D))=8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem model_center_elementary : IsElementaryAbelian 2 (center (E4×D)) := by
  refine { toIsMulCommutative := inferInstance
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  exact (by decide +kernel : ∀x:E4×D,x∈center (E4×D) → x^2=1) x.val x.property

end DihedralProductCentralFactorQuotient
