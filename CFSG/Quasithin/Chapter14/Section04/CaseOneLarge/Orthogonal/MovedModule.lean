module
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Interchange
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Actions
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.CentralizerComparison
public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.ComponentAction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Swapping
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Components

/-!
# The actual deleted moved module and orthogonal source exclusion

An order-three element of the selected diagonal residual has nontrivial
projections to both determinant factors. Conjugacy of cubics supplies a nonzero
fixed matrix. Its involution displacement, or the matrix itself when fixed,
gives a nonzero cubic fixed vector in the moved four-space. Irreducibility and
the checked binary A₅ classification select the deleted five-point module.

The matrix equivalence is transported to the literal commutator image in
U/Z(U). The actor map has kernel exactly U in K₀U and intertwines ambient
conjugation. The original flag constructs all component and module data for
i=z^(gkg), discharging the remaining premise of the orthogonal contradiction.
No selection, component or module-recognition input remains in the final theorem.
The marked-catalogue exhaustiveness and other source rows are separate steps.

Source: Aschbacher--Smith, Lemma 14.4.9, printed p.1010; refs/quasithin.pdf.
The private imports preserve the existing public boundaries of the faithful
star action and its rank calculation.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.MovedCubic
open Subgroup ClassicalOrthogonal.FourPlusMatrix ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
local notation "A" => alternatingGroup (Fin 5)

private theorem cubic_pair_conjugate (a b : Representation.SL2FourNatural.SL)
    (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ c : Representation.SL2FourNatural.SL, c * b * c⁻¹ = a := by
  have hcycle (x : Representation.SL2FourNatural.SL) (hx : orderOf x = 3) :
      Equiv.Perm.IsThreeCycle (factorAlternatingEquiv x).val := by
    have ho : orderOf (factorAlternatingEquiv x).val = 3 :=
      (Subgroup.orderOf_coe _).trans ((factorAlternatingEquiv.orderOf_eq x).trans hx)
    have hc := Equiv.Perm.isCycle_of_prime_order' (σ := (factorAlternatingEquiv x).val)
      (by rw [ho]; decide) (by rw [ho]; decide)
    change ((factorAlternatingEquiv x).val).cycleType = {3}
    rw [hc.cycleType,←hc.orderOf,ho]
  obtain ⟨c,hc⟩ := isConj_iff.mp
    (alternatingGroup.isThreeCycle_isConj (by simp) (hcycle b hb) (hcycle a ha))
  refine ⟨factorAlternatingEquiv.symm c,?_⟩
  apply factorAlternatingEquiv.injective
  simpa only [map_mul,map_inv,factorAlternatingEquiv.apply_symm_apply] using hc

/-- A commuting cubic which is nontrivial on both determinant factors fixes
some nonzero vector in the actual moved four-space. -/
private theorem cubic_fixed_in_moved (t : Binary.V ≃ₗ[ZMod 2] Binary.V)
    (ht : t ^ 2 = 1)
    (hd : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 4)
    (r : Binary.G) (hr₁ : orderOf r.1 = 3) (hr₂ : orderOf r.2 = 3)
    (hc : Commute t (Binary.linearAction r)) :
    ∃ v : Binary.V, v ≠ 0 ∧
      v ∈ LinearMap.range (t.toLinearMap - LinearMap.id) ∧ Binary.action r v = v := by
  obtain ⟨c,hc'⟩ := cubic_pair_conjugate r.1 r.2 hr₁ hr₂
  have hcv : Binary.action r c.val = c.val := by
    apply (Displacement.fixed_iff_intertwines r c.val).mpr
    have he : r.1 * c = c * r.2 := by rw [←hc']; group
    exact congrArg Subtype.val he
  have hcn : c.val ≠ 0 := by
    intro hz
    have h := c.property
    rw [hz,Matrix.det_zero] at h
    exact zero_ne_one h
  by_cases he : t c.val = c.val
  · obtain ⟨w,hw⟩ := fixed_mem_range t ht hd c.val he
    exact ⟨c.val,hcn,⟨w,hw⟩,hcv⟩
  · let v := t c.val - c.val
    have hv : v ≠ 0 := sub_ne_zero.mpr he
    refine ⟨v,hv,⟨c.val,rfl⟩,?_⟩
    change Binary.action r (t c.val - c.val) = _
    rw [map_sub]
    have hcomm : Binary.action r (t c.val) = t (Binary.action r c.val) :=
      (LinearEquiv.congr_fun hc.eq c.val).symm
    rw [hcomm,hcv]

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.MovedCubic

noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Representation

/-- An actual cubic fixed vector chooses the deleted action in the checked
irreducible A₅ classification. The output preserves both action maps. -/
private theorem deleted_action_of_cubic_fixed {J W : Type*} [Group J]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) J W) [ρ.IsIrreducible]
    (e : J ≃* alternatingGroup (Fin 5)) (hρ : ∃ g, ρ g ≠ 1)
    (r : J) (hr : orderOf r = 3) (v : W) (hv : v ≠ 0) (hfix : ρ r v = v) :
    ∃ f : J ≃* alternatingGroup (Fin 5),
      ∃ E : W ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
        ∀ g w, E (ρ g w) = BinaryPermutation.coreRepresentation (Fin 5) (f g).val (E w) := by
  let : Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
    ZMod.algebra _ 2
  obtain ⟨_,hn | hd⟩ :=
    ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
      ρ e hρ
  · obtain ⟨f,⟨E⟩⟩ := hn
    exfalso
    apply hv
    apply E.toLinearEquiv.injective
    have ho : orderOf (f r) = 3 := (f.orderOf_eq r).trans hr
    have he := Representation.IntertwiningMap.isIntertwining ρ _ E.toIntertwiningMap r v
    have hz : E v = 0 := Matrix.SL2.cubic_fixed_eq_zero (f r) ho (E v)
      (by simpa only [hfix, MonoidHom.comp_apply, SL2.BinarySmall.natural_apply,
        Representation.Equiv.coe_toIntertwiningMap, MulEquiv.coe_toMonoidHom] using he.symm)
    exact hz.trans E.toLinearEquiv.map_zero.symm
  · obtain ⟨f,⟨E⟩⟩ := hd
    let c := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
    refine ⟨f,E.toLinearEquiv.trans c.symm,?_⟩
    intro g w
    apply c.injective
    change c (c.symm (E (ρ g w))) = _
    rw [c.apply_symm_apply]
    change E (ρ g w) = c (BinaryPermutation.coreRepresentation (Fin 5) (f g).val (c.symm (E w)))
    rw [show c (BinaryPermutation.coreRepresentation (Fin 5) (f g).val (c.symm (E w))) =
      BinaryPermutation.naturalRepresentation (Fin 5) (f g).val (c (c.symm (E w))) from
        BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) (f g).val _]
    rw [c.apply_symm_apply]
    exact Representation.IntertwiningMap.isIntertwining ρ _ E.toIntertwiningMap g w

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Subgroup ClassicalOrthogonal.FourPlusMatrix Representation

/-- Recognition on the literal matrix moved space, retaining its actual actor. -/
private theorem matrix_moved_deleted
    (t : Binary.V ≃ₗ[ZMod 2] Binary.V) (ht : t ^ 2 = 1)
    (hd : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 4)
    (R : Subgroup Binary.G) (hR : ¬ Group.IsSolvable R)
    (hc : ∀ r : R, Commute t (Binary.linearAction r.val))
    (e : R ≃* alternatingGroup (Fin 5))
    (r : R) (hr : orderOf r = 3) (hr₁ : orderOf r.val.1 = 3)
    (hr₂ : orderOf r.val.2 = 3) :
    ∃ f : R ≃* alternatingGroup (Fin 5),
      ∃ E : LinearMap.range (t.toLinearMap - LinearMap.id) ≃ₗ[ZMod 2]
        BinaryPermutation.core (Fin 5),
        ∀ (g : R) (w w' : LinearMap.range (t.toLinearMap - LinearMap.id)),
          w'.val = Binary.action g.val w.val → E w' =
          BinaryPermutation.coreRepresentation (Fin 5) (f g).val (E w) := by
  let M := LinearMap.range (t.toLinearMap - LinearMap.id)
  let S : Subrepresentation (Binary.action.comp R.subtype) :=
    ⟨M, fun g v hv => Binary.InvolutionResidual.Swapping.action_preserves_moved t R hc g v hv⟩
  let ρ := S.toRepresentation
  have hsimple := (Binary.InvolutionResidual.Swapping.moved_finrank_and_irreducible
    t ht R hR hc (by rw [hd]; decide)).2
  let : Nontrivial M := Module.nontrivial_of_finrank_pos (by rw [hd]; decide)
  have hirr : ρ.IsIrreducible := by
    rw [Representation.IsIrreducible,isSimpleOrder_iff]
    refine ⟨inferInstance,fun P => ?_⟩
    let X := P.toSubmodule.map M.subtype
    have hXM : X ≤ M := by
      rintro _ ⟨v,hv,rfl⟩
      exact v.property
    have hXi (g : R) (v : Binary.V) (hv : v ∈ X) : Binary.action g.val v ∈ X := by
      obtain ⟨w,hw,rfl⟩ := hv
      exact ⟨ρ g w,P.apply_mem_toSubmodule g hw,rfl⟩
    rcases hsimple X hXM hXi with hbot | htop
    · left
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm _ bot_le
      intro v hv
      have hx : v.val ∈ X := ⟨v,hv,rfl⟩
      have hz : v.val = 0 := hbot.le hx
      exact show v = 0 from Subtype.ext hz
    · right
      apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro v _
      have hx : v.val ∈ X := htop.ge v.property
      obtain ⟨w,hw,he⟩ := hx
      have he' : w = v := Subtype.ext he
      exact he' ▸ hw
  let := hirr
  have hn : ∃ g, ρ g ≠ 1 := by
    by_contra! hall
    obtain ⟨v,hv⟩ := exists_ne (0 : M)
    let P : Subrepresentation ρ := ⟨Submodule.span (ZMod 2) {v}, by
      intro g w hw
      rw [hall g]
      exact hw⟩
    rcases eq_bot_or_eq_top P with h | h
    · apply hv
      have h' : P.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact h'.le (Submodule.mem_span_singleton_self v)
    · have h' : Submodule.span (ZMod 2) {v} = ⊤ :=
        congrArg Subrepresentation.toSubmodule h
      have hh := finrank_span_singleton (K := ZMod 2) hv
      rw [h',finrank_top] at hh
      have hm : Module.finrank (ZMod 2) M = 4 := hd
      omega
  obtain ⟨v,hv,hm,hfix⟩ := MovedCubic.cubic_fixed_in_moved t ht hd r.val hr₁ hr₂ (hc r)
  obtain ⟨f,E,hE⟩ := deleted_action_of_cubic_fixed ρ e hn r hr ⟨v,hm⟩
    (fun hz => hv (congrArg Subtype.val hz)) (Subtype.ext hfix)
  refine ⟨f,E,?_⟩
  intro g w w' hw'
  have he : w' = ρ g w := Subtype.ext hw'
  rw [he]
  exact hE g w

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Subgroup ClassicalOrthogonal.FourPlusMatrix
open ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
open LargerDimension.Orthogonal
local notation "A" => alternatingGroup (Fin 5)

private theorem diagonalInner_injective : Function.Injective (diagonalInner (S:=A)) := by
  intro a b hab
  have he : MulAut.conj (a,a) = MulAut.conj (b,b) := hab
  have hinj := Theory.GroupTheory.conj_injective_of_center_eq_bot
    (show center (A × A) = ⊥ by rw [Subgroup.center_prod,alternatingGroup.center_eq_bot (by simp),bot_prod_bot])
  exact congrArg Prod.fst (hinj he)

/-- The actual selected residual is isomorphic to A₅, through its faithful component action. -/
private def selectedResidualEquiv {Q : Type*} [Group Q] [Finite Q] {i : Q} {K : Subgroup Q}
    (d : QuotientModel.SelectedComponentData Q i K) : K ≃* A :=
  (K.equivMapOfInjective d.action d.action_injective).trans
    ((MulEquiv.subgroupCongr d.action_diagonal).trans
      (MonoidHom.ofInjective diagonalInner_injective).symm)

/-- Neither factor projection of the fixed diagonal matrix subgroup can vanish. -/
private theorem first_projection_injective
    (t : Binary.V ≃ₗ[ZMod 2] Binary.V)
    (ht : Binary.InvolutionResidual.SwapsFactors t)
    (R : Subgroup Binary.G)
    (hc : ∀ r : R, Commute t (Binary.linearAction r.val)) :
    Function.Injective ((MonoidHom.fst _ _).comp R.subtype) := by
  rw [←MonoidHom.ker_eq_bot_iff]
  apply eq_bot_iff.mpr
  intro r hr
  have hfst : r.val.1 = 1 := hr
  have hright : Binary.linearAction r.val ∈ Binary.InvolutionResidual.rightFactor := by
    refine ⟨r.val.2,?_⟩
    exact congrArg Binary.linearAction (Prod.ext hfst.symm rfl)
  have hleft : Binary.linearAction r.val ∈ Binary.InvolutionResidual.leftFactor := by
    rw [←ht.2]
    refine ⟨Binary.linearAction r.val,hright,?_⟩
    change t * Binary.linearAction r.val * t⁻¹ = Binary.linearAction r.val
    rw [(hc r).eq,mul_inv_cancel_right]
  obtain ⟨a,ha⟩ := hleft
  have he : (a,1) = r.val := Binary.action_injective
    (congrArg LinearEquiv.toLinearMap ha)
  have hrone : r.val = 1 := Prod.ext hfst (congrArg Prod.snd he).symm
  exact show r = 1 from Subtype.ext hrone

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Subgroup ClassicalOrthogonal.FourPlusMatrix
open ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
open LargerDimension.Orthogonal
local notation "A" => alternatingGroup (Fin 5)

private theorem second_projection_injective
    (t : Binary.V ≃ₗ[ZMod 2] Binary.V)
    (ht : Binary.InvolutionResidual.SwapsFactors t)
    (R : Subgroup Binary.G)
    (hc : ∀ r : R, Commute t (Binary.linearAction r.val)) :
    Function.Injective ((MonoidHom.snd _ _).comp R.subtype) := by
  rw [←MonoidHom.ker_eq_bot_iff]
  apply eq_bot_iff.mpr
  intro r hr
  have hsnd : r.val.2 = 1 := hr
  have hleft : Binary.linearAction r.val ∈ Binary.InvolutionResidual.leftFactor := by
    refine ⟨r.val.1,?_⟩
    exact congrArg Binary.linearAction (Prod.ext rfl hsnd.symm)
  have hright : Binary.linearAction r.val ∈ Binary.InvolutionResidual.rightFactor := by
    rw [←ht.1]
    refine ⟨Binary.linearAction r.val,hleft,?_⟩
    change t * Binary.linearAction r.val * t⁻¹ = Binary.linearAction r.val
    rw [(hc r).eq,mul_inv_cancel_right]
  obtain ⟨a,ha⟩ := hright
  have he : (1,a) = r.val := Binary.action_injective
    (congrArg LinearEquiv.toLinearMap ha)
  have hrone : r.val = 1 := Prod.ext (congrArg Prod.fst he).symm hsnd
  exact show r = 1 from Subtype.ext hrone

/-- Factor interchange supplies the cubic in both projections; the deleted
module is identified with its actual matrix action. -/
private theorem matrix_swapped_moved_deleted
    (t : Binary.V ≃ₗ[ZMod 2] Binary.V) (ht : t ^ 2 = 1)
    (hs : Binary.InvolutionResidual.SwapsFactors t)
    (hd : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 4)
    (R : Subgroup Binary.G)
    (hc : ∀ r : R, Commute t (Binary.linearAction r.val))
    (e : R ≃* A) :
    ∃ f : R ≃* A,
      ∃ E : LinearMap.range (t.toLinearMap - LinearMap.id) ≃ₗ[ZMod 2]
        BinaryPermutation.core (Fin 5),
        ∀ (g : R) (w w' : LinearMap.range (t.toLinearMap - LinearMap.id)),
          w'.val = Binary.action g.val w.val → E w' =
          BinaryPermutation.coreRepresentation (Fin 5) (f g).val (E w) := by
  have hR : ¬ Group.IsSolvable R := by
    intro h
    let := h
    let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable A (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hcard : Nat.card R = 60 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
    norm_num
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hcard]; decide)
  have h₁ : orderOf r.val.1 = 3 :=
    (orderOf_injective ((MonoidHom.fst _ _).comp R.subtype)
      (first_projection_injective t hs R hc) r).trans hr
  have h₂ : orderOf r.val.2 = 3 :=
    (orderOf_injective ((MonoidHom.snd _ _).comp R.subtype)
      (second_projection_injective t hs R hc) r).trans hr
  exact matrix_moved_deleted t ht hd R hR hc e r hr h₁ h₂

/-- Transport the matrix result onto the literal moved image in U/Z(U),
with the quotient presentation of KU/U and its ambient conjugation action. -/
private theorem movedCoreModel_of_matrix {G : Type*} [Group G] [Finite G]
    (H U K : Subgroup G) (m : ExchangedModel.CaseThreeAction H U)
    (hKH : K ≤ H) (hUH : U ≤ H) (i : H) (hio : orderOf (i:G) = 2)
    (hs : Binary.InvolutionResidual.SwapsFactors (m.action i))
    (hd : Module.finrank (ZMod 2)
      (LinearMap.range ((m.action i).toLinearMap - LinearMap.id)) = 4)
    (R : Subgroup Binary.G) (e : R ≃* A)
    (p : ↥(K ⊔ U) →* R) (hp : Function.Surjective p)
    (hker : p.ker = U.subgroupOf (K ⊔ U))
    (he : ∀ k : ↥(K ⊔ U), m.action (inclusion (sup_le hKH hUH) k) = Binary.linearAction (p k))
    (hc : ∀ r : R, Commute (m.action i) (Binary.linearAction r.val)) :
    Nonempty (MovedCoreModel U K (i:G) (hKH.trans m.normalizes)) := by
  let J := K ⊔ U
  let j : J →* H := inclusion (sup_le hKH hUH)
  let t := m.action i
  let W := LinearMap.range (t.toLinearMap - LinearMap.id)
  have ht : t^2=1 := by
    rw [←map_pow,show i^2=1 from Subtype.ext (hio ▸ pow_orderOf_eq_one (i:G)),map_one]
  obtain ⟨f,E,hE⟩ := matrix_swapped_moved_deleted t ht hs hd R hc e
  let a := m.quotientAction.comp j
  have hm (v : U ⧸ center U) :
      v ∈ movedImage U (i:G) ↔ (m.coordinates v).toAdd ∈ W := by
    have h := m.subspace_moved i hio
    change m.subspace (movedImage U (i:G)) = W at h
    rw [←h]
    change v ∈ movedImage U (i:G) ↔ m.coordinates v ∈
      (movedImage U (i:G)).map m.coordinates.toMonoidHom
    exact (mem_map_iff_mem m.coordinates.injective).symm
  have hai (k : J) (v : U ⧸ center U) :
      (m.coordinates (a k v)).toAdd = Binary.action (p k) (m.coordinates v).toAdd := by
    rw [show a k v = m.quotientAction (j k) v from rfl,m.intertwines]
    change m.action (j k) (m.coordinates v).toAdd = _
    rw [he]
    rfl
  have hinv (k : J) (v : U ⧸ center U) (hv : v ∈ movedImage U (i:G)) :
      a k v ∈ movedImage U (i:G) := by
    apply (hm _).mpr
    rw [hai]
    exact Binary.InvolutionResidual.Swapping.action_preserves_moved t R hc (p k) _ ((hm v).mp hv)
  let C : movedImage U (i:G) ≃* Multiplicative W := {
    toFun := fun v => Multiplicative.ofAdd ⟨(m.coordinates v).toAdd,(hm v).mp v.property⟩
    invFun := fun w => ⟨m.coordinates.symm (Multiplicative.ofAdd w.toAdd.val),
      (hm _).mpr (by rw [m.coordinates.apply_symm_apply]; exact w.toAdd.property)⟩
    left_inv := by intro v; apply Subtype.ext; exact m.coordinates.symm_apply_apply v
    right_inv := by intro w; apply Subtype.ext; exact congrArg Multiplicative.toAdd (m.coordinates.apply_symm_apply _)
    map_mul' := by intro v w; apply Subtype.ext; exact congrArg Multiplicative.toAdd (m.coordinates.map_mul v w) }
  let B : Multiplicative W ≃* Multiplicative (BinaryPermutation.core (Fin 5)) := E.toAddEquiv.toMultiplicative
  refine ⟨{
    π := f.toMonoidHom.comp p
    surjective := f.surjective.comp hp
    kernel := ?_
    action := a
    formula := ?_
    invariant := hinv
    equiv := C.trans B
    equivariant := ?_ }⟩
  · ext k
    change f (p k) = 1 ↔ _
    rw [←f.map_one,f.injective.eq_iff]
    exact SetLike.ext_iff.mp hker k
  · intro k u
    exact m.quotientAction_apply (j k) u
  · intro k v
    apply Multiplicative.toAdd.injective
    change E ⟨(m.coordinates (a k v)).toAdd,_⟩ =
      BinaryPermutation.coreRepresentation (Fin 5) (f (p k)).val (E ⟨(m.coordinates v).toAdd,_⟩)
    exact hE (p k) _ _ (hai k v)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Subgroup ClassicalOrthogonal.FourPlusMatrix
open LargerDimension.Orthogonal

/-- The star quotient marking transports to KU/U without changing either
quotient map or the conjugation action on U/Z(U). -/
private theorem movedCoreModel_of_star {G : Type*} [Group G] [Finite G]
    (H U K : Subgroup G) (m : ExchangedModel.CaseThreeAction H U)
    (hKH : K ≤ H) (hcore : H.pCoreIn 2 = U) (i : H)
    (hKi : K ≤ centralizer ({(i:G)} : Set G)) (hio : orderOf (i:G) = 2)
    (hs : Binary.InvolutionResidual.SwapsFactors (m.action i))
    (hd : Module.finrank (ZMod 2)
      (LinearMap.range ((m.action i).toLinearMap - LinearMap.id)) = 4)
    (B : Subgroup (H ⧸ pCore 2 H)) (b : B ≃* Binary.G)
    (f : (H ⧸ pCore 2 H) →* (Binary.V ≃ₗ[ZMod 2] Binary.V))
    (hf : ∀ h : H, m.action h = f (QuotientGroup.mk' (pCore 2 H) h))
    (hb : ∀ k : B, f k = Binary.linearAction (b k))
    (hIB : (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≤ B)
    (e : (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≃* alternatingGroup (Fin 5)) :
    Nonempty (MovedCoreModel U K (i:G) (hKH.trans m.normalizes)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let I := (K.subgroupOf H).map q
  let J := K ⊔ U
  have hUH : U ≤ H := hcore ▸ H.pCoreIn_le 2
  have hU : U.subgroupOf H = pCore 2 H := by
    rw [←hcore]
    ext h
    constructor
    · rintro ⟨k,hk,he⟩
      exact (show k = h from Subtype.ext he) ▸ hk
    · intro hh
      exact ⟨h,hh,rfl⟩
  let j : J →* H := inclusion (sup_le hKH hUH)
  let qJ := q.comp j
  have hqJ : qJ.range = I := by
    rw [MonoidHom.range_comp,inclusion_range,subgroupOf_sup hKH hUH,Subgroup.map_sup,hU]
    have hbot : (pCore 2 H).map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    rw [hbot,sup_bot_eq]
  let α : J →* I := qJ.codRestrict I (fun k => hqJ ▸ (show qJ k ∈ qJ.range from ⟨k,rfl⟩))
  have hα : Function.Surjective α := by
    intro y
    have hy : y.val ∈ qJ.range := hqJ.symm ▸ y.property
    obtain ⟨k,hk⟩ := hy
    exact ⟨k,Subtype.ext hk⟩
  let β : I →* Binary.G := b.toMonoidHom.comp (inclusion hIB)
  have hβ : Function.Injective β := b.injective.comp (inclusion_injective hIB)
  let R := β.range
  let βe : I ≃* R := MonoidHom.ofInjective hβ
  let p : J →* R := βe.toMonoidHom.comp α
  have hp : Function.Surjective p := βe.surjective.comp hα
  have hker : p.ker = U.subgroupOf J := by
    ext k
    change βe (α k) = 1 ↔ (k:G) ∈ U
    rw [←βe.map_one,βe.injective.eq_iff]
    change α k = 1 ↔ _
    rw [Subtype.ext_iff]
    change q (j k) = 1 ↔ _
    rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    exact SetLike.ext_iff.mp hU.symm (j k)
  have he (k : J) : m.action (j k) = Binary.linearAction (p k) := by
    rw [hf]
    exact hb (inclusion hIB (α k))
  have hc (r : R) : Commute (m.action i) (Binary.linearAction r.val) := by
    obtain ⟨y,hy⟩ := βe.surjective r
    obtain ⟨k,hk,hqk⟩ := y.property
    let kj : J := ⟨k,(le_sup_left : K ≤ J) hk⟩
    have hpk : p kj = r := by
      have ha : α kj = y := Subtype.ext hqk
      change βe (α kj) = r
      rw [ha,hy]
    rw [←hpk,←he]
    apply Commute.map
    exact (show Commute i (j kj) from
      Subtype.ext (mem_centralizer_singleton_iff.mp (hKi hk)).symm)
  exact movedCoreModel_of_matrix H U K m hKH hUH i hio hs hd R
    (βe.symm.trans e) p hp hker he hc

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Orthogonal CoreGeometry
open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

/-- Construct the deleted-five model on the literal moved image, with its
actual ambient conjugation and quotient kernel U. -/
theorem source_orthogonal_moved_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : let := chosen.elementary
      let := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (z : G) (hz : orderOf z = 2) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) (hio : orderOf (i:G) = 2) :
    ∃ hKU : diagonalResidual F.H (i:G) ≤ normalizer (F.U : Set G),
      Nonempty (MovedCoreModel F.U (diagonalResidual F.H (i:G)) (i:G) hKU) := by
  let := chosen.elementary
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let m := source_orthogonal_action d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  let K := diagonalResidual F.H (i:G)
  have hKH : K ≤ F.H := (map_subtype_le _).trans inf_le_left
  have hKi : K ≤ centralizer ({(i:G)} : Set G) := (map_subtype_le _).trans inf_le_right
  let B := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let b : B ≃* Binary.G := κ.trans elementaryEquiv.symm
  let f := sourceStarAction F hk e
  have hf (h : F.H) : m.action h = f (QuotientGroup.mk' (pCore 2 F.H) h) := rfl
  have hb (k : B) : f k = Binary.linearAction (b k) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := (e.trans Binary.binaryCoordinates).surjective w
    rw [sourceStarAction_apply,Binary.linearAction_apply]
    change Binary.binaryCoordinates (e ((sourceAction F hk).representation k v)) = _
    rw [he]
    obtain ⟨a,ha⟩ := elementaryEquiv.surjective (κ k)
    have ha' : b k = a := by
      change elementaryEquiv.symm (κ k) = a
      rw [←ha,elementaryEquiv.symm_apply_apply]
    rw [←ha,ha']
    exact toOrthogonal_coordinates a (e v)
  have hr := diagonalResidual_image_of_comparison F.H z i hz hH.le
    (source_orthogonal_centralizer_comparison d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he z hzp hH i hiX hiV hio)
  have hIB : (K.subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H)) ≤ B := by
    rw [hr]
    change _ ≤ (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
    exact map_pResidual_le 2 _
  let c := (source_orthogonal_selected_components d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z hz hzp hH i hiX hiV hio).some
  refine ⟨hKH.trans m.normalizes,?_⟩
  exact movedCoreModel_of_star F.H F.U K m hKH
    (source_orthogonal_twoCore d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he).2 i hKi hio
    (source_orthogonal_action_swaps d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he i hiX hiV)
    (source_orthogonal_moved_rank d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he i hiX hiV hio).1 B b f hf hb hIB
    (selectedResidualEquiv c)

/-- Source case (3) is impossible. The original selected involution, diagonal
component, and deleted moved module are all constructed from the original flag. -/
theorem source_orthogonal_contradiction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : let := chosen.elementary
      let := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) : False := by
  obtain ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiV⟩ :=
    source_orthogonal_selected_involution d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  have hmoved := source_orthogonal_moved_model d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z hzo hzp hH ⟨_,F.invariant 1 hiT⟩ hiX hiV hio
  change ∃ hKU : diagonalResidual F.H (conjugateElement z (g*k*g)) ≤ normalizer (F.U : Set G),
    Nonempty (MovedCoreModel F.U (diagonalResidual F.H (conjugateElement z (g*k*g)))
      (conjugateElement z (g*k*g)) hKU) at hmoved
  rw [hH] at hmoved
  obtain ⟨hKU,hm⟩ := hmoved
  exact source_selected_contradiction_of_moved_model d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z (g*k*g) hzo hzp hH hiT hiU hiX hiV hKU hm.some

/-- Eliminate the marked orthogonal row directly on the original flag.
The conjugator and the selected involution are both constructed. -/
theorem source_orthogonal_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : let := chosen.elementary
      let := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) : False := by
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  exact source_orthogonal_contradiction d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
