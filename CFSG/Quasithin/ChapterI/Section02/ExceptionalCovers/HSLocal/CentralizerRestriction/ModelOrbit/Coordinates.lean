module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelCore

/-!
# Two-letter coordinates for the HS core

The 64 products of four quaternion representatives in each factor and the
cyclic factor have distinct pairs of images of letters 1 and 4. Kernel checks
verify this small table. The established upper bound of 64 for the actual
pair kernel proves coverage, so those two letter images determine every core
element. The orbit certificates use this faithful encoding to avoid repeatedly
comparing degree-100 permutations.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423,
and 16.1.5(10), printed p.1172. The factors are the existing exact ATLAS
carrier words. `source/discover.py` reproduces the coordinate and orbit data;
all mathematical certificates are checked by Lean's kernel.
-/

public section
open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelOrbitCoordinates

@[expose] def quaternion (n : Fin 4) : QuaternionGroup 2 :=
  if n.val < 2 then .a n.val else .xa (n.val - 2)
@[expose] def coordinate (i : Fin 64) : core :=
  leftEmbedding (quaternion ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩) *
    rightEmbedding (quaternion ⟨(i.val / 4) % 4, Nat.mod_lt _ (by decide)⟩) *
    cyclicEmbedding (Multiplicative.ofAdd ((i.val / 16 : Nat) : ZMod 4))
@[expose] def encode (x : core) : Fin 100 × Fin 100 := (x.val.val.val 1, x.val.val.val 4)
private def code (i : Fin 64) : Fin 100 × Fin 100 :=
  (⟨(206926897594316055981575830678291021909503645621687460265516910973306029869854961379799264650807942966617435618574998983815022012889496265975313750536620741354567138806882633252132988864011418256189191185315925215637561409619295519855590030631051769180393013385318695425 >>> (14 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩,
   ⟨(206926897594316055981575830678291021909503645621687460265516910973306029869854961379799264650807942966617435618574998983815022012889496265975313750536620741354567138806882633252132988864011418256189191185315925215637561409619295519855590030631051769180393013385318695425 >>> (14 * i.val + 7)) % 128 % 100, Nat.mod_lt _ (by decide)⟩)
private theorem code_spec : ∀ i, encode (coordinate i) = code i := by
  decide +kernel
private theorem code_injective : Function.Injective code := by
  decide +kernel
private theorem coordinate_injective : Function.Injective coordinate := by
  intro i j h
  apply code_injective
  rw [← code_spec, ← code_spec, h]

theorem coordinate_surjective : Function.Surjective coordinate := by
  apply ((Nat.bijective_iff_injective_and_card coordinate).mpr ⟨coordinate_injective, ?_⟩).2
  simpa only [Nat.card_fin] using (Nat.le_antisymm core_card_le core_card_ge).symm

theorem encode_injective : Function.Injective encode := by
  intro x y h
  obtain ⟨i,rfl⟩ := coordinate_surjective x
  obtain ⟨j,rfl⟩ := coordinate_surjective y
  rw [code_spec, code_spec] at h
  exact congrArg coordinate (code_injective h)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelOrbitCoordinates
