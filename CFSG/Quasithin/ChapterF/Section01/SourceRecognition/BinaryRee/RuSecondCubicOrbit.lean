module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondNativeCubic
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicCoordinates

/-!
# A generating cubic orbit in the original second core

The earlier native cubic marking retains the actual X-conjugation formula
on A. The three conjugates of one marked element generate the native core;
transport through the same coordinates proves that their literal ambient
subgroup closure is precisely the original A.

Source: the binary Ree branch of Aschbacher–Smith F.1.12 applied in J.4.5.
This is a source input to the remaining second-endpoint extension census.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

/-- Three actual X-conjugates generate the unchanged source A. -/
theorem SourceChoice.exists_A_cubic_orbit_generators (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃(X : Sylow 3 p.parabolic) (x : X) (a : p.A B5), orderOf x=3 ∧
      closure (Set.range (fun i:Fin 3 => ((x:p.parabolic):G)^i.val*(a:G)*
        (((x:p.parabolic):G)^i.val)⁻¹))=p.A B5 := by
  obtain ⟨X,e,x,_,hx,hact⟩:=s.exists_A_native_cubic_marking B5 hi
  let f : ReeTwo.SylowModel.CubicAction.A→*G := (p.A B5).subtype.comp e.symm.toMonoidHom
  let a : p.A B5 := e.symm (ReeTwo.SylowModel.CubicAction.orbit 0)
  have heval (n:ℕ) : f ((ReeTwo.SylowModel.CubicAction.cubic^n)
      (ReeTwo.SylowModel.CubicAction.orbit 0))=
      ((x:p.parabolic):G)^n*(a:G)*(((x:p.parabolic):G)^n)⁻¹ := by
    induction n with
    | zero => simp [f,a]
    | succ n ih =>
      rw [pow_succ',MulAut.mul_apply]
      change (e.symm (ReeTwo.SylowModel.CubicAction.cubic _):G)=_
      rw [hact]
      change ((x:p.parabolic):G)*f _*((x:p.parabolic):G)⁻¹=_
      rw [ih,pow_succ']
      group
  have horbit (i:Fin 3) : f (ReeTwo.SylowModel.CubicAction.orbit i)=
      ((x:p.parabolic):G)^i.val*(a:G)*(((x:p.parabolic):G)^i.val)⁻¹ := by
    rw [ReeTwo.SylowModel.CubicAction.orbit_actual]
    exact heval i.val
  have hgen := congrArg (Subgroup.map f) ReeTwo.SylowModel.CubicAction.orbit_generated
  rw [MonoidHom.map_closure] at hgen
  have hrange : f '' Set.range ReeTwo.SylowModel.CubicAction.orbit =
      Set.range (fun i:Fin 3 => ((x:p.parabolic):G)^i.val*(a:G)*(((x:p.parabolic):G)^i.val)⁻¹) := by
    ext y
    constructor
    · rintro ⟨a,⟨i,rfl⟩,rfl⟩
      exact ⟨i,(horbit i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i,rfl⟩,horbit i⟩
  have htop : (⊤:Subgroup ReeTwo.SylowModel.CubicAction.A).map f=p.A B5 := by
    rw [←MonoidHom.range_eq_map,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [hrange,htop] at hgen
  exact ⟨X,x,a,hx,hgen⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
