module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCoreMarking
public import Theory.SpecificGroups.ReeTwo.FirstParabolicCubicAutomorphisms

/-!
# The actual second-core cubic action

The selected source Sylow three-subgroup acts nontrivially on the original
A: a trivial action would put its generator in C_F₂(A) ≤ A, contradicting
coprime orders. The proved cubic conjugacy theorem for the native core then
normalizes this action, with its original ambient conjugation formula.
The chosen core coordinates need not extend the previously chosen Sylow
coordinates; that additional extension compatibility is a separate step.

Source: Aschbacher–Smith J.4.4–5, printed pp.441–442, in the F.1.12 binary
Ree recognition branch. The earlier source theorem constructs X and F₂/A.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

def secondCoreAction (B5 : Sylow 5 d.toTypeRuSetup.H)
    (e : p.A B5 ≃* ReeTwo.SylowModel.firstParabolicCore) :
    p.parabolic →* MulAut ReeTwo.SylowModel.firstParabolicCore :=
  (MulAut.congr e).toMonoidHom.comp
    ((p.A B5).normalizerMonoidHom.comp (inclusion (p.A_normalized B5)))

theorem secondCoreAction_apply (B5 : Sylow 5 d.toTypeRuSetup.H)
    (e : p.A B5 ≃* ReeTwo.SylowModel.firstParabolicCore)
    (x : p.parabolic) (a : p.A B5) :
    (e.symm (secondCoreAction B5 e x (e a)) : G) = (x:G)*(a:G)*(x:G)⁻¹ := by
  change (e.symm (e ((p.A B5).normalizerMonoidHom
    (inclusion (p.A_normalized B5) x) (e.symm (e a)))):G)=_
  rw [e.symm_apply_apply,e.symm_apply_apply]
  rfl

theorem SourceChoice.secondCoreAction_order_three (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X : Sylow 3 p.parabolic)
    (hmodel : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)))
    (e : p.A B5 ≃* ReeTwo.SylowModel.firstParabolicCore)
    (x : X) (hx : orderOf x = 3) : orderOf (secondCoreAction B5 e (x : p.parabolic)) = 3 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    have hx3 : (x:p.parabolic)^3=1 := by
      exact congrArg (fun y:X => (y:p.parabolic)) (hx ▸ pow_orderOf_eq_one x)
    rw [hx3,map_one]
  · intro h
    have hcentral : ((x:p.parabolic):G)∈centralizer (p.A B5:Set G) := by
      intro a ha
      have hh := secondCoreAction_apply B5 e (x:p.parabolic) ⟨a,ha⟩
      rw [h,MulAut.one_apply,e.symm_apply_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    have hxF : ((x:p.parabolic):G)∈p.F₂ B5 X :=
      (show p.cubicSubgroup X≤p.F₂ B5 X from le_sup_right.trans le_sup_left)
        (mem_map_of_mem _ x.property)
    have hxA : ((x:p.parabolic):G)∈p.A B5 :=
      p.centralizer_le_of_plane_le (p.F₂_le_parabolic B5 X)
        (p.le_seed.trans (p.V_le_S₂.trans (p.S₂_le_A B5)))
        (p.F₂_inf_R₂ B5 X hmodel) ⟨hxF,hcentral⟩
    have hdiv := orderOf_dvd_natCard (⟨((x:p.parabolic):G),hxA⟩:p.A B5)
    have horder : orderOf (⟨((x:p.parabolic):G),hxA⟩:p.A B5)=3 := by
      simpa only [Subgroup.orderOf_mk,Subgroup.orderOf_coe] using hx
    rw [horder,s.card_A p B5 hi] at hdiv
    norm_num at hdiv

/-- Every prescribed native cubic action is realized on the unchanged source
second core, after choosing its coordinates and a generator of the original X. -/
theorem SourceChoice.exists_A_cubic_marking (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (γ : MulAut ReeTwo.SylowModel.firstParabolicCore) (hγ : orderOf γ = 3) :
    ∃(X : Sylow 3 p.parabolic)
      (e : p.A B5 ≃* ReeTwo.SylowModel.firstParabolicCore) (x : X),
      Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)) ∧
      orderOf x=3 ∧ ∀a : ReeTwo.SylowModel.firstParabolicCore,
        (e.symm (γ a):G)=((x:p.parabolic):G)*(e.symm a:G)*((x:p.parabolic):G)⁻¹ := by
  obtain ⟨X,_,hm,_⟩:=s.exists_secondParabolic p B5 hi
  obtain ⟨_,e,_⟩:=s.exists_T_F_A_marking B5 hi
  let _ : Fact (Nat.Prime 3):=⟨by decide⟩
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=X) 3
    (by rw [p.card_sylow_three X])
  have ho:=s.secondCoreAction_order_three B5 hi X hm e x hx
  obtain ⟨α,hα⟩:=ReeTwo.SylowModel.firstParabolic_cubic_conjugacy
    (secondCoreAction B5 e (x:p.parabolic)) γ ho hγ
  have norm (y:X) (hy:orderOf y=3)
      (he:α*secondCoreAction B5 e (y:p.parabolic)*α⁻¹=γ) :
      ∃(e' : p.A B5 ≃* ReeTwo.SylowModel.firstParabolicCore) (y:X),
      orderOf y=3 ∧ ∀a : ReeTwo.SylowModel.firstParabolicCore,
        (e'.symm (γ a):G)=((y:p.parabolic):G)*(e'.symm a:G)*((y:p.parabolic):G)⁻¹ := by
    refine ⟨e.trans α,y,hy,?_⟩
    intro a
    have hh:=secondCoreAction_apply B5 e (y:p.parabolic) (e.symm (α.symm a))
    rw [e.apply_symm_apply] at hh
    have ha : α.symm (γ a)=secondCoreAction B5 e (y:p.parabolic) (α.symm a) := by
      rw [←he]
      simp only [MulAut.mul_apply,MulAut.inv_apply,MulEquiv.symm_apply_apply]
    change (e.symm (α.symm (γ a)):G)=_
    rw [ha]
    exact hh
  rcases hα with hα|hα
  · obtain ⟨e',y,hy,he⟩:=norm x hx hα
    exact ⟨X,e',y,hm,hy,he⟩
  · have hinv : α*secondCoreAction B5 e ((x⁻¹:X):p.parabolic)*α⁻¹=γ := by
      have hh:=congrArg Inv.inv hα
      change α*secondCoreAction B5 e ((x:p.parabolic)⁻¹)*α⁻¹=γ
      rw [map_inv]
      simpa only [mul_inv_rev,inv_inv,mul_assoc] using hh
    obtain ⟨e',y,hy,he⟩:=norm x⁻¹ (by simpa only [orderOf_inv] using hx) hinv
    exact ⟨X,e',y,hm,hy,he⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
