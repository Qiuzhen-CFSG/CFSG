module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.FixedGeometry
public import Theory.Representation.BinaryOffender.SylowFixedGeneration

/-!
# The point parabolic in the repeated-natural row

All coordinate projections of a Sylow-fixed seed lie on the same
one-dimensional natural fixed space. A generating seed has a nonzero
coordinate, so fixing that seed is equivalent to fixing this point.
The identification retains the supplied action intertwiner.

Source: Aschbacher--Smith, 15.2.23(a), printed p.1117, using B.5.1.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource

/-- The actual seed fixer in a repeated natural action is a point parabolic. -/
theorem repeatedNatural_seedKernel
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {n r : ℕ} (hn : 2 ≤ n) (hr : 0 < r)
    (e : ActionEquiv ρ (repeated (linearNatural BinaryField.two n) r))
    (P : Sylow 2 D) (Z : Submodule (ZMod 2) W)
    (hZ : Z ≤ fixedSpace ρ P) (hgen : (⨆ g : D, Z.map (ρ g)) = ⊤) :
    ∃ x : Fin n → ZMod 2, x ≠ 0 ∧
      (subspaceKernel ρ Z ⊤).map e.groupEquiv.toMonoidHom =
        MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) x := by
  let S : Sylow 2 (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    P.mapSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
  obtain ⟨x,f,hx,_,_,hfixed⟩ := NaturalDualCentralizer.exists_fixed_pair hn S
  have hcoords (z : W) (hz : z ∈ Z) (i : Fin r) :
      e.linearEquiv z i ∈ Submodule.span (ZMod 2) {x} := by
    have hfull : (e.linearEquiv z i,0) ∈
        fixedSpace (NaturalDualCentralizer.slAction n) S := by
      rintro ⟨g,hg⟩
      obtain ⟨p,hp,rfl⟩ := hg
      apply Prod.ext
      · have he := congrFun (e.intertwines p z) i
        have hzfix : ρ p z = z := hZ hz ⟨p,hp⟩
        rw [hzfix] at he
        exact he.symm
      · change (linearNatural BinaryField.two n).dual (e.groupEquiv p) 0 = 0
        exact map_zero _
    rw [hfixed] at hfull
    exact hfull.1
  let : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let : Nontrivial W := e.linearEquiv.symm.injective.nontrivial
  have hZne : Z ≠ ⊥ := by
    intro he
    have hb : (⊥ : Submodule (ZMod 2) W) = ⊤ := by
      simpa only [he, Submodule.map_bot, iSup_bot] using hgen
    exact bot_ne_top hb
  obtain ⟨z,hz,hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZne
  have hez : e.linearEquiv z ≠ 0 := by
    intro he
    exact hz0 (e.linearEquiv.map_eq_zero_iff.mp he)
  obtain ⟨i,hi⟩ : ∃ i, e.linearEquiv z i ≠ 0 := Function.ne_iff.mp hez
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (hcoords z hz i)
  have ha0 : a ≠ 0 := by
    intro he
    exact hi (by simpa only [he,zero_smul] using ha.symm)
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  have hzix : e.linearEquiv z i = x := by simpa only [ha1,one_smul] using ha.symm
  refine ⟨x,hx,?_⟩
  ext g
  constructor
  · rintro ⟨p,hp,rfl⟩
    have he := congrFun (e.intertwines p z) i
    rw [hp.2 z hz] at he
    change e.linearEquiv z i = linearNatural BinaryField.two n (e.groupEquiv p)
      (e.linearEquiv z i) at he
    rw [hzix] at he
    exact he.symm
  · intro hg
    obtain ⟨p,rfl⟩ := e.groupEquiv.surjective g
    refine ⟨p, ⟨mem_top _, ?_⟩, rfl⟩
    intro w hw
    apply e.linearEquiv.injective
    rw [e.intertwines]
    funext j
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp (hcoords w hw j)
    change linearNatural BinaryField.two n (e.groupEquiv p) (e.linearEquiv w j) =
      e.linearEquiv w j
    rw [← hb, map_smul]
    have he : linearNatural BinaryField.two n (e.groupEquiv p) x = x := hg
    rw [he]

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
