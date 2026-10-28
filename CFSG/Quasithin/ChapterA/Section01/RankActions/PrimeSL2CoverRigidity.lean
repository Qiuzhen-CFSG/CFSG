module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL2
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Prime-field SL₂ cover rigidity and the actual rank-action consumer

The proved universal projection SL₂(p) → PSL₂(p) is centrally closed.
For a perfect central cover E → SL₂(p), lift that universal projection
through the composite E → PSL₂(p). Uniqueness of maps from a perfect group
gives a right inverse, and the universal lift is surjective. This discharges
the exact input retained in A.1.29(2), also used twice in A.3.6's
noncentral branch. No multiplier value beyond the proved universal
projection is assumed.

Source: Aschbacher–Smith A.1.29, printed p.27; A.3.6, pp.44–45;
I.1.1 and I.1.3, printed p.407.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter
namespace CFSG.Quasithin.ChapterA.RankActions
universe u

/-- Every finite perfect central cover of prime-field SL₂(p), p > 3,
is injective, in the exact universe-polymorphic source contract. -/
theorem primeSL2CoverRigidity : PrimeSL2CoverRigidity.{u} := by
  intro p hp hlarge E hE hfin hperfect f hsurj hker
  let : Fact (3 < Nat.card (ZMod p)) := ⟨by simpa using hlarge⟩
  let c := PSL2Cover.cover (ZMod p)
  have hc : Covering.IsUniversal.{0, 0, u} c :=
    (ChapterI.LieMultipliers.PSL2.primeField_universalCover
      (ZMod p) (by simpa using hlarge) (by simpa using hp.out)).1
  let fperfect : PerfectCentralCovering.Cover E
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    { toMonoidHom := f, surjective := hsurj, isPerfect := inferInstance,
      ker_le_center := hker }
  let : IsQuasisimple E := fperfect.isQuasisimple
  let fc : Covering E (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    { toMonoidHom := f, surjective := hsurj }
  let a := hc.lift (c.comp fc)
  have hfac : c.toMonoidHom.comp (f.comp a.toMonoidHom) =
      c.toMonoidHom.comp (MonoidHom.id _) := by
    simpa only [Covering.comp_toMonoidHom, MonoidHom.comp_assoc,
      MonoidHom.comp_id] using congrArg Covering.toMonoidHom (hc.lift_fac (c.comp fc))
  have hright : f.comp a.toMonoidHom = MonoidHom.id _ :=
    PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      c.toMonoidHom c.ker_le_center _ _ hfac
  intro x y hxy
  obtain ⟨x, rfl⟩ := a.surjective x
  obtain ⟨y, rfl⟩ := a.surjective y
  have h : x = y := by
    exact (DFunLike.congr_fun hright x).symm.trans
      (hxy.trans (DFunLike.congr_fun hright y))
  exact congrArg a h

end CFSG.Quasithin.ChapterA.RankActions

namespace CFSG.Quasithin.ChapterA
open RankActions
universe u

/-- A.1.29(2), with the prime-field cover input now discharged. The kernel
is that of the original conjugation action on P/Φ(P). -/
theorem lemma_A_1_29_2
    {G : Type u} [Group G] [Finite G] (P H : Subgroup G) [P.Normal]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hP : IsPGroup p P)
    (ho : omega₁ P (p := p) = ⊤)
    (hc : _root_.commutator P ≤ center P) (hr : primeRank p P = 2)
    [Group.IsPerfect H] (hPH : ⁅P, H⁆ ≠ ⊥)
    [IsQuasisimple (H ⧸ pPrimeCore 2 H)] :
    pPrimeCore 2 H = frattiniCentralizer P H ∧ primeRank 2 H = 1 :=
  lemma_A_1_29_2_of_coverRigidity primeSL2CoverRigidity P H hp hP ho hc hr hPH

end CFSG.Quasithin.ChapterA
