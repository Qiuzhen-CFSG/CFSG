module
public import Theory.Representation.SL2NaturalOffenders.OuterSemilinear
public import Theory.Representation.SemilinearInvolutionFixedCard
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction

public import Theory.Representation.SL2OrthogonalCover.OuterSemilinear
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverCoordinates

/-!
# Fixed two-cores of actual outer block involutions

The marked natural module carries the block automorphism and its literal
quotient actor. Outer involutions have a nontrivial field coefficient, giving
a square-root fixed count. For a centerless block this is already the entire
core. In the full central-cover case, the equivariant orthogonal coordinates
and uniqueness of lifts extend the same semilinearity to the entire core.

The private import is an intentional proof extension of AutomorphismAction:
it compares the defined actor with the model's specified quotient isomorphism.
Its private implementation does not enter any public statement.
Source: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]

theorem IsL2EvenBlock.outer_module_fixed_card {n : ℕ} (hL : IsL2EvenBlock L n)
    (a : MulAut L) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, quotientAut (pCore 2 L) a = MulAut.conj g) :
    Nat.card ((blockModuleAut a).toMonoidHom.eqLocus (MonoidHom.id (BlockModule L))) ^ 2 =
      Nat.card (BlockModule L) := by
  obtain ⟨F,_,_,hF,_,ρ,⟨m⟩,hm⟩ := hL.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let A := m.moduleAction a
  let E₀ : (Fin 2 → F) ≃+ (Fin 2 → F) :=
    { toFun v := (A (Multiplicative.ofAdd v)).toAdd
      invFun v := (A.symm (Multiplicative.ofAdd v)).toAdd
      left_inv v := A.symm_apply_apply v
      right_inv v := A.apply_symm_apply v
      map_add' v w := A.map_mul v w }
  let E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F) :=
    { E₀ with map_smul' := fun c v => ZMod.map_smul E₀ c v }
  have hE : Function.Involutive E := by
    intro v
    have hA : A ^ 2 = 1 := by dsimp only [A]; rw [←map_pow,ha,map_one]
    exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hA (Multiplicative.ofAdd v))
  have he (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      E (g.val.mulVec v) = (m.quotientAction a g).val.mulVec (E v) := by
    have hh := m.actions_compatible a g (Multiplicative.ofAdd v)
    have hv : Multiplicative.ofAdd (g.val.mulVec v) = ρ g (Multiplicative.ofAdd v) := by
      exact Multiplicative.toAdd.injective (hm g (Multiplicative.ofAdd v)).symm
    change (A (Multiplicative.ofAdd (g.val.mulVec v))).toAdd = _
    rw [hv]
    exact (congrArg Multiplicative.toAdd hh).trans (hm _ _)
  have hqa : m.quotientAction a = MulAut.congr m.quotientIso (quotientAut (pCore 2 L) a) := by
    apply MulEquiv.ext
    intro g
    obtain ⟨l,rfl⟩ := m.actor_surjective g
    rw [m.quotientAction_actor]
    change m.quotientIso (QuotientGroup.mk' _ (a l)) =
      m.quotientIso (quotientAut (pCore 2 L) a (m.quotientIso.symm (m.quotientIso (QuotientGroup.mk' _ l))))
    rw [m.quotientIso.symm_apply_apply,quotientAut_apply_mk]
  have ho : ¬ ∃ g, m.quotientAction a = MulAut.conj g := by
    rw [hqa]
    exact fun hh => houter ((MulAut.congr_inner_iff m.quotientIso _).mp hh)
  obtain ⟨σ,hσne,hσ⟩ := SL2NaturalOffenders.outer_intertwiner_semilinear (m.quotientAction a) E he ho
  exact SemilinearInvolution.fixed_card_sq_of_mulEquiv σ
    (SL2NaturalOffenders.semilinear_coefficient_involutive E hE σ hσ) hσne
    E.toLinearMap.toAddMonoidHom hE hσ (blockModuleAut a).toMonoidHom m.moduleIso (fun u => by
      obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) u
      change m.moduleIso (blockModuleAut a (QuotientGroup.mk' _ v)) = m.moduleAction a (m.moduleIso (QuotientGroup.mk' _ v))
      rw [blockModuleAut_apply_mk,m.moduleAction_mk])

theorem IsL2EvenBlock.centerless_core_fixed_card {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hz : center L = ⊥)
    (a : MulAut L) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, quotientAut (pCore 2 L) a = MulAut.conj g) :
    Nat.card (((MulAut.characteristic (pCore 2 L) a).toMonoidHom).eqLocus
      (MonoidHom.id (pCore 2 L))) ^ 2 = Nat.card (pCore 2 L) := by
  have hz' : blockFixed L = ⊥ := by change (center L).subgroupOf (blockU L) = ⊥; rw [hz,bot_subgroupOf]
  let q := QuotientGroup.mk' (blockFixed L)
  have hq : Function.Bijective q := ⟨by
    apply q.ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_mk',hz'], QuotientGroup.mk'_surjective _⟩
  let e : pCore 2 L ≃* BlockModule L :=
    (MulEquiv.subgroupCongr hcore).trans (MulEquiv.ofBijective q hq)
  let α := MulAut.characteristic (pCore 2 L) a
  let β := blockModuleAut a
  have he (u : pCore 2 L) : e (α u) = β (e u) := by
    change QuotientGroup.mk' (blockFixed L) (MulEquiv.subgroupCongr hcore (α u)) =
      blockModuleAut a (QuotientGroup.mk' (blockFixed L) (MulEquiv.subgroupCongr hcore u))
    rw [blockModuleAut_apply_mk]
    congr 1
  let ef : α.toMonoidHom.eqLocus (MonoidHom.id _) ≃ β.toMonoidHom.eqLocus (MonoidHom.id _) :=
    e.toEquiv.subtypeEquiv (fun u => by
      change α u = u ↔ β (e u) = e u
      rw [←he]
      exact e.injective.eq_iff.symm)
  rw [Nat.card_congr ef,Nat.card_congr e.toEquiv]
  exact hL.outer_module_fixed_card a ha houter

theorem IsL2EvenBlock.full_cover_core_fixed_card {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hz : Nat.card (center L) = 2^n)
    (a : MulAut L) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, quotientAut (pCore 2 L) a = MulAut.conj g) :
    Nat.card (((MulAut.characteristic (pCore 2 L) a).toMonoidHom).eqLocus
      (MonoidHom.id (pCore 2 L))) ^ 2 = Nat.card (pCore 2 L) := by
  let := hL.2.1.finite
  let := hL.2.1.elementary
  let := hL.2.1.module_elementary
  obtain ⟨F,_,_,hF,_,ρ,⟨m⟩,hm⟩ := hL.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfixed : Nat.card (blockFixed L) = 2^n :=
    (Nat.card_congr (subgroupOfEquivOfLe (hL.center_le_module hcore)).toEquiv).trans hz
  obtain ⟨eU,heU⟩ := modelCover_orthogonal_equiv hL.2.1 m hm hL.1 hF hfixed
  let e : pCore 2 L ≃* Multiplicative (SL2OrthogonalCover.Space F) :=
    (MulEquiv.subgroupCongr hcore).trans eU
  let κ := MulAut.characteristic (pCore 2 L) a
  let A := MulAut.congr e κ
  let E₀ : SL2OrthogonalCover.Space F ≃+ SL2OrthogonalCover.Space F :=
    { toFun v := (A (Multiplicative.ofAdd v)).toAdd
      invFun v := (A.symm (Multiplicative.ofAdd v)).toAdd
      left_inv v := A.symm_apply_apply v
      right_inv v := A.apply_symm_apply v
      map_add' v w := A.map_mul v w }
  let E : SL2OrthogonalCover.Space F ≃ₗ[ZMod 2] SL2OrthogonalCover.Space F :=
    { E₀ with map_smul' := fun c v => ZMod.map_smul E₀ c v }
  have heκ (u : pCore 2 L) : (e (κ u)).toAdd = E (e u).toAdd := by
    change (e (κ u)).toAdd = (e (κ (e.symm (e u)))).toAdd
    rw [e.symm_apply_apply]
  have hel (l : L) (u : pCore 2 L) :
      (e (MulAut.conjNormal l u)).toAdd = SL2OrthogonalCover.action
        (m.actor l) (e u).toAdd := by
    exact heU l (MulEquiv.subgroupCongr hcore u)
  have hE (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : SL2OrthogonalCover.Space F) :
      E (SL2OrthogonalCover.action g v) = SL2OrthogonalCover.action (m.quotientAction a g) (E v) := by
    obtain ⟨l,rfl⟩ := m.actor_surjective g
    obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd v)
    have hv : (e u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←hv,←hel,←heκ,←heκ,m.quotientAction_actor]
    have hconj : κ (MulAut.conjNormal l u) = MulAut.conjNormal (a l) (κ u) := by
      apply Subtype.ext
      change a (l*u.val*l⁻¹)=a l * a u.val * (a l)⁻¹
      simp only [map_mul,map_inv]
    rw [hconj,hel]
  have ho : ¬ ∃ g, m.quotientAction a = MulAut.conj g := by
    exact fun hh => houter ((MulAut.congr_inner_iff m.quotientIso _).mp hh)
  have hκ : Function.Involutive κ := by
    intro u
    have hh : κ^2=1 := by dsimp only [κ]; rw [←map_pow,ha,map_one]
    exact DFunLike.congr_fun hh u
  apply SL2OrthogonalCover.outer_involution_fixed_card_sq_of_mulEquiv
    (by rw [hF]; exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide : 0<2) hL.1))
    (m.quotientAction a) E hE ho κ.toMonoidHom hκ e heκ

end CFSG.Quasithin.ChapterC
