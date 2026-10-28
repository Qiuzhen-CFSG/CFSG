module

public import Theory.SpecificGroups.SU3.UnitaryEight.BinarySeed
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel
/-!
# The binary-seed obstruction for every SU₃(8) Borel

The concrete upper root group is Sylow, and its normalizer contains the
actual diagonal torus. Sylow conjugacy transports that torus to every Sylow
normalizer. The intrinsic matrix calculation therefore applies without a
chosen coordinate marking of the source Borel.

Source: Aschbacher–Smith 13.8.20, printed p.955; the Sylow and normalizer
identifications are the genuine matrix results in F.1.3.
-/

public section
open Matrix BenderSuzuki.External BenderSuzuki.MatrixGroups Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight
open BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEightSeed
open CFSG.Quasithin.ChapterF.Source.Unitary
variable {E : Type*} [Field E] [Finite E]

/-- No four-element subset of the natural module is invariant under the two-residual of a Sylow normalizer. -/
theorem no_four_set_sylow_borel (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])
    (hcard : Nat.card E = 64) (hfixed : Nat.card {x : E // J.conj x = x} = 8)
    (P : Sylow 2 J.specialSubgroup)
    (S : Set (Fin 3 → E)) (hS : Nat.card S = 4)
    (hs : ∀ b : (pResidual 2 (normalizer (P : Set J.specialSubgroup))).map
        (normalizer (P : Set J.specialSubgroup)).subtype,
      ∀ v ∈ S, b.val.val.val *ᵥ v ∈ S) : False := by
  obtain ⟨_, _, P₀, hR, _, _, _, hN, _⟩ := standard_su_borel_data J 3 (by decide)
    (by simpa using hcard)
    (huppert_II_10_4_conj_eq_frobenius J 8 (by simpa using hcard) hfixed) hJ
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq J.specialSubgroup P₀ P
  have hm : (P₀ : Subgroup J.specialSubgroup).map (MulAut.conj c).toMonoidHom = P :=
    congrArg Sylow.toSubgroup hc
  have hn := Subgroup.map_equiv_normalizer_eq (P₀ : Subgroup J.specialSubgroup) (MulAut.conj c)
  rw [hm] at hn
  have ht : (hermitianTorusSU J hJ).range ≤ normalizer (P₀ : Set J.specialSubgroup) := by
    change suTorus J hJ ≤ normalizer ((P₀ : Subgroup J.specialSubgroup) : Set _)
    rw [hR, hN]
    exact le_sup_right
  apply no_four_set_conjugate_torus J hJ hcard hfixed _ c ?_ S hS hs
  exact hn ▸ Subgroup.map_mono ht
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight
