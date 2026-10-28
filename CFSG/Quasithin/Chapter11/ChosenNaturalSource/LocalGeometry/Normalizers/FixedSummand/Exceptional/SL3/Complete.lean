module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.SL3.FiveAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.FiveNormalizer

/-!
# Exclusion of the literal SL₃ exceptional action

Both natural factors of O₂(L₁)/Z(L₁) have a fixed-free five-action.
The normalizer of the inner L₁ image on this section has order prime to
seven, by Frattini's argument and the fixed-free centralizer bound.
Thus O^{7′}(Y) acts trivially on the section, preserves VZ(L₁), and
preserves [VZ(L₁),L₁]=V. The already proved equality Y=O^{7′}(Y)(Y∩M)
then contradicts escape from M.

The theorem `exceptional_normalizes_seed` supplies the literal linear
branch of `ExceptionalBlockActions`. The last theorem applies it to the
original fixed-center target, retaining the Cartan–TI construction.
That construction, its centralizer control, the Sp₄ branch and final
assembly remain with qt-d-1222-natural-point-fixed-summand. The enclosing
source assembly owner is qt-d-1222-natural-normalizer-source.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
11.1.5, printed p.766. This argument avoids an extra abelian-section premise.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))

private theorem first_card_primes (hq : 2 ^ S.field.degree = 4) :
    Nat.Coprime 7 (Nat.card (f.Li 0)) ∧ ¬ 25 ∣ Nat.card (f.Li 0) := by
  have hm := first_isPSL D S m f
  rw [hq] at hm
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨j⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hc : Nat.card (f.Li 0 ⧸ pCore 2 (f.Li 0)) = 60 := by
    rw [Nat.card_congr (e.trans j).toEquiv, nat_card_alternatingGroup]
    norm_num
  have hindex : (pCore 2 (f.Li 0)).index = 60 := hc
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := f.Li 0)).exists_card_eq
  rw [←(pCore 2 (f.Li 0)).card_mul_index,hn,hindex]
  constructor
  · exact ((by decide : Nat.Coprime 7 2).pow_right n).mul_right (by decide)
  · intro hd
    have h25 : 25 ∣ 60 := ((by decide : Nat.Coprime 25 2).pow_right n).dvd_of_dvd_mul_left hd
    norm_num at h25

open Representation.GoldschmidtONan Representation.BinaryOffender

/-- The literal SL₃ central section kills the seven-residual action, with
all section, order, and fixed-free-action premises discharged. -/
theorem exceptional_sevenResidual_normalizes_seed (hb : ChapterC.IsShort L)
    (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    (primeToResidual 7 (normalizer (f.Ri 0 : Set G))).map
      (normalizer (f.Ri 0 : Set G)).subtype ≤ normalizer (V : Set G) := by
  have hq : 2 ^ S.field.degree = 4 := by
    rw [(chosen_exceptional_parameters D S f X hcenter hfixed he).1]
    rfl
  have hn := chosen_exceptional_normalizes_first D S f (first_isPSL D S m f)
    (first_centralizes_line D S m f) X hcenter hfixed he
  let a := (f.Li 0).normalizerMonoidHom.comp (inclusion hn)
  obtain ⟨B,hB,hBcard,hBfixed⟩ := exists_fixed_free_five D S m f hb hq
  have hp := first_card_primes D S m f hq
  have hk := ChiefSection.sevenResidual_le_section_kernel_of_five (f.Li 0) a hp.1 hp.2
    (exceptional_coreCentralSection_card D S m f hb X hcenter hfixed he) B hB hBcard hBfixed
  rintro _ ⟨y,hy,rfl⟩
  exact section_kernel_normalizes_seed D S m f (inclusion hn y) (hk hy)

/-- The source SL₃ exceptional action preserves the caller's original V. -/
theorem exceptional_normalizes_seed (hb : ChapterC.IsShort L)
    (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (V : Set G) :=
  chosen_exceptional_normalizes_seed_of_sevenResidual D S f X
    (PointBlocks.seed_eq_conjugateSpan_of_short D hb) h hfixed he
    (exceptional_sevenResidual_normalizes_seed D S m f hb X hcenter hfixed he)

/-- The complete SL₃ branch of the exceptional GO exclusion. -/
theorem exceptional_escape_of_short (hb : ChapterC.IsShort L)
    (X : Subgroup G)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) : False :=
  hescape ((exceptional_normalizes_seed D S m f hb X hcenter h hfixed he).trans
    (chosen_seed_normalizer_le D S))


/-- Application to the actual fixed-summand target in the SL₃ branch.
The remaining Cartan–TI construction is retained by this task, and the
preceding block and center inputs by the normalizer-source assembly owner. -/
theorem normalizes_fixed_of_pair
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hpair : PairConstruction D S f) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G) := by
  by_cases hz : radicalFixedCenter (f.Ri 0) L = ⊥
  · rw [hz,Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))]
    exact le_top
  obtain ⟨X,_,_,h,hfixed⟩ := hpair hescape
    (PointBlocks.seed_eq_conjugateSpan_of_short D hb.2.1) (Or.inl hb) hcenter hz
  rcases chosen_invariant_or_exceptional D f X h hfixed with hn | he
  · exact hn
  · exact (exceptional_escape_of_short D S m f hb.2.1 X hescape hcenter h hfixed he).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
